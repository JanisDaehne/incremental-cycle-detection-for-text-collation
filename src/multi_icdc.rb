# frozen_string_literal: true
require 'set'
require 'rbtree'

class MultiIncrementalCycleDetectionWithChains

  # array with an entry per chain/text
  # each entry is a hash to store the merge nodes for in the chain
  # for each merge node we store a list of reachable nodes in other chains
  #   the reachable list is an array with an entry per chain
  #   if a chain is reachable from the node, the entry is the index of the node in the other chain
  #   if the chain is not reachable, the entry is nil
  # if two nodes are connected (merge nodes via merge edge) they always have the same list!
  #   but we make different lists because we would have to set the lists to the same reference in some cases
  #   e.g. when we have 0-1 and 2-3 and then add 1-2, we have to update the lists of 0 and 3 (all connected nodes)
  #   but try this anyway because then we can skip the horizontal update for the reachable lists
  attr_accessor :nodes_to_reachable_lists_by_chain
  # for each merge node (in each chain) we store the length of the segment (merged nodes vertically)
  #   used for many to many alignments
  # better: do not store the length but the ending node
  # 4 len 2 -> 4+2-1 = 5
  # 7 len 5 -> 7+5-1 = 11
  attr_accessor :nodes_to_end_nodes_by_chain

  # for every chain an rb tree of merge nodes
  #   we could use a normal array and binary search but rb tree is in C (faster)
  #   and insert is faster when a tree is used (see chain_align2/3 for the binary search version)
  attr_accessor :merge_nodes_by_chain_sorted

  # [reachable list] -> set of nodes that have this reachable list
  attr_accessor :reachable_list_to_connected_nodes
  attr_accessor :chain_ranges

  # not really needed, only for debug (get state)
  def init(chain_ranges)
    # e.g.  ranges = [
    #   0..7,
    #   0..7,
    #   0..7,
    #   0..7,
    # ]
    @chain_ranges = chain_ranges
    @nodes_to_reachable_lists_by_chain = Array.new(chain_ranges.length) { |p| Hash.new }
    @merge_nodes_to_end_nodes_by_chain = Array.new(chain_ranges.length) { |p| Hash.new }
    @merge_nodes_by_chain_sorted = Array.new(chain_ranges.length) { |p| RBTree.new }
    @reachable_list_to_connected_nodes = Hash.new { |h, k| h[k] = Set.new }
    @reachable_list_to_connected_nodes.compare_by_identity # we change the keys (arrays via reference)
    # for each chain, for each node the predecessor / previous merge node in the chain
    @chain_node_to_same_chain_predecessor = Array.new(chain_ranges.length) { |p| Hash.new }
    # for each chain, for each node the successor / next merge node in the chain
    @chain_node_to_same_chain_successor = Array.new(chain_ranges.length) { |p| Hash.new }

    # edges starting from this node (we only store the directly connected nodes here)
    @merge_nodes_to_direct_reach = Array.new(chain_ranges.length) { |p| Hash.new }
  end

  # @param edge [[chain, node, len], [chain, node, len]]
  def can_add_edge?(edge)
    !self.edge_introduces_cycle?(edge)
  end

  # checks if the edges would introduce a cycle
  # checks if the edge is valid (does not intersect lengths)
  # @param edge [[chain, node, len], [chain, node, len]]
  def edge_introduces_cycle?(edge)
    chain_1, node_1, len_1 = edge[0]
    chain_2, node_2, len_2 = edge[1]

    return true if chain_1 == chain_2 # needed?

    # get next merging edge for both nodes (in same chain)
    # could be the node itself
    next_merge_node_1 = self._get_next_merge_node_improved(chain_1, node_1)
    next_merge_node_2 = self._get_next_merge_node_improved(chain_2, node_2)

    reachable_list_1 = @nodes_to_reachable_lists_by_chain[chain_1][next_merge_node_1]
    reachable_list_2 = @nodes_to_reachable_lists_by_chain[chain_2][next_merge_node_2]

    # could be the node itself
    # prev_merge_node_1 = self._get_prev_merge_node_improved(chain_1, node_1)
    # prev_merge_node_2 = self._get_prev_merge_node_improved(chain_2, node_2)
    prev_merge_node_1 = @chain_node_to_same_chain_predecessor[chain_1][next_merge_node_1]
    prev_merge_node_2 = @chain_node_to_same_chain_predecessor[chain_2][next_merge_node_2]

    # check if the nodes of the edge are valid
    # currently we only accept the "root" node of the length (4 & 5 & 6 -> len 3, but we expect 4)
    # we have to check the prev and next merge nodes because they both can make our edge invalid
    #   (our edge start-end could intersect their intervals/lengths)

    # check node 1 for overlaps
    curr_node_end_node_1 = node_1 + len_1 - 1

    # check interval with next node
    #  curr node end must be BEFORE next merge node start
    if next_merge_node_1 != nil
      if curr_node_end_node_1 < next_merge_node_1
        # ok
      else
        next_merge_node_end_1 = @merge_nodes_to_end_nodes_by_chain[chain_1][next_merge_node_1]
        if node_1 == next_merge_node_1 && curr_node_end_node_1 == next_merge_node_end_1
          # same node is only possible if we have horizontally connected nodes
          # then the interval must be the same
        else
          return true
        end
      end
    end

    # prev node end must be BEFORE curr node start
    if prev_merge_node_1 != nil
      prev_merge_node_end_1 = @merge_nodes_to_end_nodes_by_chain[chain_1][prev_merge_node_1]
      if prev_merge_node_end_1 < node_1
        # ok
      else
        if node_1 == prev_merge_node_1 && curr_node_end_node_1 == prev_merge_node_end_1
          # same node is only possible if we have horizontally connected nodes
          # then the interval must be the same
        else
          return true
        end
      end
    end

    # check node 2 for overlaps
    curr_node_end_node_2 = node_2 + len_2 - 1

    # check interval with next node
    #  curr node end must be BEFORE next merge node start
    if next_merge_node_2 != nil
      if curr_node_end_node_2 < next_merge_node_2
        # ok
      else
        next_merge_node_end_2 = @merge_nodes_to_end_nodes_by_chain[chain_2][next_merge_node_2]
        if node_2 == next_merge_node_2 && curr_node_end_node_2 == next_merge_node_end_2
          # same node is only possible if we have horizontally connected nodes
          # then the interval must be the same
        else
          return true
        end
      end
    end

    # prev node end must be BEFORE curr node start
    if prev_merge_node_2 != nil
      prev_merge_node_end_2 = @merge_nodes_to_end_nodes_by_chain[chain_2][prev_merge_node_2]
      if prev_merge_node_end_2 < node_2
        # ok
      else
        if node_2 == prev_merge_node_2 && curr_node_end_node_2 == prev_merge_node_end_2
          # same node is only possible if we have horizontally connected nodes
          # then the interval must be the same
        else
          return true
        end
      end
    end

    # if both nil -> no merge nodes below them -> no cycle
    # if one is nil -> no merge node below one -> maybe cycle (from the other node)

    # check side from node 1 to node 2
    # node 1 reaches to node 2 if
    # - chain of node 2 is reachable from node 1 (node_1_reachable_node_in_other_chain != nil)
    # - index of node 2 is after/equal the reachable node in the other chain
    #   (because we already can go further down the chain)
    #
    has_cycle_from_node_1 = false
    has_cycle_from_node_2 = false

    if reachable_list_1 != nil
      node_1_reachable_node_in_other_chain = reachable_list_1[chain_2]
      has_cycle_from_node_1 = node_1_reachable_node_in_other_chain != nil && node_1_reachable_node_in_other_chain <= node_2
    end

    if reachable_list_2 != nil
      node_2_reachable_node_in_other_chain = reachable_list_2[chain_1]
      has_cycle_from_node_2 = node_2_reachable_node_in_other_chain != nil && node_2_reachable_node_in_other_chain <= node_1
    end

    has_cycle = has_cycle_from_node_1 || has_cycle_from_node_2

    return has_cycle
  end

  # interval 1 has never nils, interval 2 can have nils
  def _intervals_overlap(interval_1, interval_2)
    start_1, end_1 = interval_1
    test_start_2, test_end_2 = interval_2

    return false if start_1 == nil || test_end_2 == nil

    if test_end_2 < start_1
      return false
    elsif test_start_2 > end_1
      return false
    end

    return true
  end

  # if edge is proved, propagate the reachable lists
  # @return true: some entry was modified, false: no entry was modified
  def _merge_reachable_lists_into_1(reachable_list_1, reachable_list_2, edge = nil)
    # we only get here if both nodes have reachable lists -> separate reachable lists

    was_modified = false

    merged_list = reachable_list_1
    reachable_list_1.each_with_index do |reachable_node_1, chain_index|
      reachable_node_2 = reachable_list_2[chain_index]

      if reachable_node_1 == nil && reachable_node_2 == nil
        # keep nil
      elsif reachable_node_1 == nil
        merged_list[chain_index] = reachable_node_2
        was_modified = true
      elsif reachable_node_2 == nil
        merged_list[chain_index] = reachable_node_1
      else
        merged_list[chain_index] = [reachable_node_1, reachable_node_2].min
        was_modified = was_modified || merged_list[chain_index] != reachable_node_1
      end
    end

    if edge != nil
      chain_2, node_2 = edge[1]
      # now make sure all the connected nodes have the same reachable list (same reference)
      # connected_nodes_to_list_1 = @reachable_list_to_connected_nodes[reachable_list_1]
      connected_nodes_to_list_2 = @reachable_list_to_connected_nodes[reachable_list_2] # this includes node 2

      connected_nodes_to_list_2.each do |connected_node_pair|
        other_chain, other_node = connected_node_pair
        @nodes_to_reachable_lists_by_chain[other_chain][other_node] = merged_list
        @reachable_list_to_connected_nodes[reachable_list_1] << connected_node_pair
      end

      # delete entry reachable_list_2
      @reachable_list_to_connected_nodes.delete(reachable_list_2)
    end

    return was_modified
  end

  def _merge_reachable_lists_into_1_for_remove(reachable_list_1, new_reachable_list_2, old_reachable_list_2)
    # compare pair-wise with old reachable list
    # if they have different entries, keep reachable list 1
    # if they are the same, use the value from the new reachable list 2

    was_modified = false

    merged_list = reachable_list_1
    reachable_list_1.each_with_index do |reachable_node_1, chain_index|
      reachable_node_2 = old_reachable_list_2[chain_index]

      if reachable_node_1 != reachable_node_2
        # ok, keep
      else
        # they are the same, so reachable list reach came from list 2
        # but now list 2 has updated data

        new_reachable_node_2 = new_reachable_list_2[chain_index]

        # if the new is the same, nothing has to be changed
        if new_reachable_node_2 == reachable_node_1
          next
        end

        # only if the old reaches were equal but the new one is not we have to do something
        # it could be the case that some node was only reachable via the merge-edge we just deleted
        # however, there could exist multiple paths to a node (not directly [would be a circle] but any node before this)
        # because the old entries were the same we don't know if there were multiple paths (same number)

        # we need to check if there is a different path, use the horizontal directly connected nodes
        # and from all of them the next merge node

        # min is not right here because before they had the same reach
        # and we only change the reach at points where the reach came over the node with list 2
        # and as list 2 already has updated reach (with the next merge node) the value is always correct in list 2
        #   (but only for reaches that came exclusively over node 2)
        merged_list[chain_index] = new_reachable_node_2
        was_modified = was_modified || reachable_node_1 != new_reachable_node_2
      end
    end

    return was_modified
  end

  # this does not check for cycles!
  # this does not check if the nodes are inside other lengths!
  # it also ignores the lengths of both nodes are already part of merge edges
  # @param edge [[chain, node, len], [chain, node, len]]
  def add_edge(edge)
    chain_1, node_1, len_1 = edge[0]
    chain_2, node_2, len_2 = edge[1]

    # duplicates are already handled by _get_next_merge_node_improved
    #   it will find the nodes themselves

    direct_reach_list_1 = @merge_nodes_to_direct_reach[chain_1][node_1]
    direct_reach_list_2 = @merge_nodes_to_direct_reach[chain_2][node_2]

    if direct_reach_list_1 == nil
      direct_reach_list_1 = []
      @merge_nodes_to_direct_reach[chain_1][node_1] = direct_reach_list_1
    end
    direct_reach_list_1 << [chain_2, node_2]

    if direct_reach_list_2 == nil
      direct_reach_list_2 = []
      @merge_nodes_to_direct_reach[chain_2][node_2] = direct_reach_list_2
    end
    direct_reach_list_2 << [chain_1, node_1]

    # the new edge is a merge edge, its nodes are merge edges
    # we can use the next merge node (excluding the current) because
    # if it's not the current node -> same
    # if it's the current node we connect horizontally and then we have at least one reach list already
    #   and the min of with the next merge node would not change anything
    next_merge_node_1 = self._get_next_merge_node_improved(chain_1, node_1)
    next_merge_node_2 = self._get_next_merge_node_improved(chain_2, node_2)

    reachable_list_1 = @nodes_to_reachable_lists_by_chain[chain_1][node_1]
    reachable_list_2 = @nodes_to_reachable_lists_by_chain[chain_2][node_2]

    if reachable_list_1 == nil && reachable_list_2 == nil
      # both are new
      reachable_list_1 = Array.new(@nodes_to_reachable_lists_by_chain.length) { |p| nil }
      reachable_list_1[chain_1] = node_1
      reachable_list_1[chain_2] = node_2
      reachable_list_2 = reachable_list_1 # same reference

      @reachable_list_to_connected_nodes[reachable_list_1] << [chain_1, node_1]
      @reachable_list_to_connected_nodes[reachable_list_1] << [chain_2, node_2]

      @nodes_to_reachable_lists_by_chain[chain_1][node_1] = reachable_list_1
      @nodes_to_reachable_lists_by_chain[chain_2][node_2] = reachable_list_2 # is the same as 1

      @merge_nodes_to_end_nodes_by_chain[chain_1][node_1] = node_1 + len_1 - 1
      @merge_nodes_to_end_nodes_by_chain[chain_2][node_2] = node_2 + len_2 - 1

      self._insert_merge_node(chain_1, node_1)
      self._insert_merge_node(chain_2, node_2)

    elsif reachable_list_1 == nil
      # we already have list 2, we might have to update it (entry of chain 1)
      reachable_list_2[chain_1] = node_1
      reachable_list_1 = reachable_list_2 # same reference

      @reachable_list_to_connected_nodes[reachable_list_2] << [chain_1, node_1]

      @nodes_to_reachable_lists_by_chain[chain_1][node_1] = reachable_list_1

      @merge_nodes_to_end_nodes_by_chain[chain_1][node_1] = node_1 + len_1 - 1

      self._insert_merge_node(chain_1, node_1)

    elsif reachable_list_2 == nil
      # we already have list 1, we might have to update it (entry of chain 1)
      reachable_list_1[chain_2] = node_2
      reachable_list_2 = reachable_list_1 # same reference

      @reachable_list_to_connected_nodes[reachable_list_1] << [chain_2, node_2]

      @nodes_to_reachable_lists_by_chain[chain_2][node_2] = reachable_list_2

      @merge_nodes_to_end_nodes_by_chain[chain_2][node_2] = node_2 + len_2 - 1

      self._insert_merge_node(chain_2, node_2)

    else
      # we have both lists, we have to merge them
      # merge reachable lists
      self._merge_reachable_lists_into_1(reachable_list_1, reachable_list_2, edge)

      # these are always true/reachable (ensure these are correct)
      # reachable_list_1[chain_1] = node_1
      # reachable_list_1[chain_2] = node_2
    end

    # now the lists for node_1 and node_2 are correct...

    if next_merge_node_1 != nil
      if next_merge_node_1 != node_1
        prev_merge_node_1 = @chain_node_to_same_chain_predecessor[chain_1][next_merge_node_1]
      else
        # next merge node is the node itself, nothing to do here (horizontally connected nodes)
        # because real next merge node has this node as prev node already
        prev_merge_node_1 = nil
      end
    else
      # there is no next node
      # but our node will be the next (last) merge node
      # this cannot be the current node else next_merge_node_1 would not be nil
      prev_merge_node_1 = self._get_prev_merge_node_excluding_self_improved(chain_1, node_1)
      # we cannot use @chain_node_to_same_chain_successor here because [chain_1, node_1] is not a merge node yet
    end

    if next_merge_node_2 != nil
      if next_merge_node_2 != node_2
        prev_merge_node_2 = @chain_node_to_same_chain_predecessor[chain_2][next_merge_node_2]
      else
        # next merge node is the node itself, nothing to do here (horizontally connected nodes)
        # because real next merge node has this node as prev node already
        prev_merge_node_2 = nil
      end
    else
      prev_merge_node_2 = self._get_prev_merge_node_excluding_self_improved(chain_2, node_2)
    end


    # set prev for curr node
    if prev_merge_node_1 != nil
      @chain_node_to_same_chain_predecessor[chain_1][node_1] = prev_merge_node_1
      @chain_node_to_same_chain_successor[chain_1][prev_merge_node_1] = node_1
    end
    if prev_merge_node_2 != nil
      @chain_node_to_same_chain_predecessor[chain_2][node_2] = prev_merge_node_2
      @chain_node_to_same_chain_successor[chain_2][prev_merge_node_2] = node_2
    end

    if next_merge_node_1 != nil
      next_reachable_list_1 = @nodes_to_reachable_lists_by_chain[chain_1][next_merge_node_1]
      self._merge_reachable_lists_into_1(reachable_list_1, next_reachable_list_1, nil)

      if next_merge_node_1 != node_1
        # the prev node probably changed because we have a new prev node
        @chain_node_to_same_chain_predecessor[chain_1][next_merge_node_1] = node_1
        @chain_node_to_same_chain_successor[chain_1][node_1] = next_merge_node_1
      end
    end

    if next_merge_node_2 != nil
      next_reachable_list_2 = @nodes_to_reachable_lists_by_chain[chain_2][next_merge_node_2]
      self._merge_reachable_lists_into_1(reachable_list_2, next_reachable_list_2, nil)

      if next_merge_node_2 != node_2
        @chain_node_to_same_chain_predecessor[chain_2][next_merge_node_2] = node_2
        @chain_node_to_same_chain_successor[chain_2][node_2] = next_merge_node_2
      end
    end

    # but now the previous merge nodes in the chains could reach other chains or different nodes...
    # update hte previous merge nodes in the chains
    # this has to be done recursively

    self._update_reachable_lists([chain_1, node_1], reachable_list_1)
  end

  def _update_reachable_lists(root_node_pos, root_reachable_list)
    # we only have to update upward the chains (and connected horizontal nodes), we never update downward
    # thus, we can first update horizontal nodes and then the chain
    # we can encounter the same node multiple times (we don't care because we use min)

    marked_lists = Set.new
    marked_lists.compare_by_identity

    lists_to_visit = [root_reachable_list]

    while lists_to_visit.length > 0
      reachable_list = lists_to_visit.pop

      # these nodes are all connected to the same reachable list (horizontally)
      merge_nodes_pos_set = @reachable_list_to_connected_nodes[reachable_list]

      merge_nodes_pos_set.each do |node_pos|
        chain_2, node_2 = node_pos
        # prev_merge_node = self._get_prev_merge_node(chain_2, node_2)
        # prev_merge_node = self._get_prev_merge_node_excluding_self_improved(chain_2, node_2)
        prev_merge_node = @chain_node_to_same_chain_predecessor[chain_2][node_2]
        next if prev_merge_node == nil

        prev_reachable_list = @nodes_to_reachable_lists_by_chain[chain_2][prev_merge_node]

        # if we already processed this list, do not process it again
        # this is because we can have multiple paths to the same list
        # but as only one edge was added any path from this list to the new edge
        # gives the correct min
        if marked_lists.include?(prev_reachable_list)
          next
        end

        # update prev list
        was_modified = self._merge_reachable_lists_into_1(prev_reachable_list, reachable_list, nil)

        if was_modified
          # only if the list changes, then we need to check further
          lists_to_visit << prev_reachable_list
        end

      end

    end

  end

  def _split_connected_nodes_list(edge, reachable_list_1)
    chain_1, node_1 = edge[0]
    chain_2, node_2 = edge[1]

    reachable_nodes_0 = @reachable_list_to_connected_nodes[reachable_list_1]
    found_nodes = Set.new

    node_queue = [edge[0]]

    while node_queue.length > 0
      _node = node_queue.pop
      chain, node_idx = _node
      found_nodes.add(_node)

      direct_reachable_1 = @merge_nodes_to_direct_reach[chain][node_idx]

      direct_reachable_1.each do |connected_node|
        if found_nodes.include?(connected_node)
          next
        end
        found_nodes.add(connected_node)
        node_queue << connected_node
      end
    end

    other_connected_nodes = reachable_nodes_0.difference(found_nodes)

    return [found_nodes, other_connected_nodes]
  end

  def remove_edge(edge)
    chain_1, node_1, len_1 = edge[0]
    chain_2, node_2, len_2 = edge[1]
    plain_edge = [[chain_1, node_1], [chain_2, node_2]]

    # deleting is more difficult than adding because we don't know
    # what nodes are reachable anymore when we delete only this edge
    # some observations:
    # - we only have to update reach lists above the affected nodes (and propagate upwards)
    # - when we compare the current nodes reach and the prev reach in the chain point-wise:
    #   - if the entries are different, the prev entry is ok because it does not depend on the current reach
    #     - the prev entry is always lower (because != and top node can reach every node the current node can)
    #   - if the entries are the same the prev entry comes from the current node
    #     - because there are no two paths from this and the prev node to any other node
    #       - would be a cycle and on the same alignment line
    # - if the node has no other connected nodes -> deleting reach would work (but propagation??)
    # - if the node has connected nodes we don't easily know which connection was removed and what are left
    #   - we don't store the edges, we don't know how to change the reach??
    # solution: just recalculate the reaches of all connected nodes
    #   - this is done by using every next node (of the connected nodes) and point-wise min
    #   - then propagate the new reaches upward

    reachable_list_1 = @nodes_to_reachable_lists_by_chain[chain_1][node_1]
    reachable_list_2 = @nodes_to_reachable_lists_by_chain[chain_2][node_2]

    # check if the edge exists
    # if they are connected, then they have the same reach
    if reachable_list_1 == nil || reachable_list_1 != reachable_list_2
      return false
    end

    direct_reachable_1 = @merge_nodes_to_direct_reach[chain_1][node_1]
    direct_reachable_2 = @merge_nodes_to_direct_reach[chain_2][node_2]

    # we cannot use edge[1], edge[0] directly because it includes the lengths
    direct_reachable_1.delete(plain_edge[1])
    direct_reachable_2.delete(plain_edge[0])

    # because they have an edge, they have the same reach list and connected nodes
    # horizontally all nodes with the same list are reachable, thus these are all nodes (max = number of chains)
    # follow the edges until one of the remove nodes is found, the remaining nodes in reachable_nodes_0 are in the other set

    reachable_nodes_1, reachable_nodes_2 = self._split_connected_nodes_list(plain_edge, reachable_list_1)

    # this is enough because we have the same list for both nodes
    @reachable_list_to_connected_nodes.delete(reachable_list_1)

    reachable_nodes_lists = [reachable_nodes_1, reachable_nodes_2]

    reachable_nodes_lists.each_with_index do |reachable_nodes, i|
      curr_chain = i == 0 ? chain_1 : chain_2
      curr_node = i == 0 ? node_1 : node_2

      _new_reach_list = Array.new(@nodes_to_reachable_lists_by_chain.length) { |p| nil }

      # includes self
      reachable_nodes.each_with_index do |node, j|
        chain, node_idx = node

        # this is always true because the next on has lass reach (for this chain)
        _new_reach_list[chain] = node_idx

        # next_merge_node = _get_next_merge_node_improved(chain, node_idx + 1) # currently the node itself is still there -> +1
        next_merge_node = @chain_node_to_same_chain_successor[chain][node_idx]
        next if next_merge_node == nil

        next_reachable_list = @nodes_to_reachable_lists_by_chain[chain,][next_merge_node]

        self._merge_reachable_lists_into_1(_new_reach_list, next_reachable_list, nil)
      end

      # update data
      @nodes_to_reachable_lists_by_chain[curr_chain][curr_node] = _new_reach_list
      @reachable_list_to_connected_nodes[_new_reach_list] = reachable_nodes
    end

    # propagate lists
    reachable_nodes_lists.each_with_index do |reachable_nodes, i|

      curr_chain = i == 0 ? chain_1 : chain_2
      curr_node = i == 0 ? node_1 : node_2
      new_reach_list = @nodes_to_reachable_lists_by_chain[curr_chain][curr_node]

      # using a reach list of a node that will be removed (because not longer a merge node) is ok
      # because any previous node in the same change will use itself as entry for the current chain entry

      self._rebuild_reachable_lists_upward(new_reach_list)

      if reachable_nodes.length == 1
        reach_list = @nodes_to_reachable_lists_by_chain[curr_chain][curr_node]
        @nodes_to_reachable_lists_by_chain[curr_chain].delete(curr_node)
        @merge_nodes_by_chain_sorted[curr_chain].delete(curr_node)
        @reachable_list_to_connected_nodes.delete(reach_list)
        @merge_nodes_to_end_nodes_by_chain[curr_chain].delete(curr_node)

        # we only have to update the prev node when we actually remove the node
        # when we have > 3 horizontally connected nodes and we remove one edge, we keep some nodes

        # get prev node
        prev_node_chain_curr = @chain_node_to_same_chain_predecessor[curr_chain][curr_node]
        @chain_node_to_same_chain_predecessor[curr_chain].delete(curr_node)

        next_merge_node_chain_curr = self._get_next_merge_excluding_self_node_improved(curr_chain, curr_node)
        @chain_node_to_same_chain_successor[curr_chain].delete(curr_node)

        if next_merge_node_chain_curr != nil

          if prev_node_chain_curr != nil
            # the next merge node now has the prev node as predecessor
            @chain_node_to_same_chain_predecessor[curr_chain][next_merge_node_chain_curr] = prev_node_chain_curr
            @chain_node_to_same_chain_successor[curr_chain][prev_node_chain_curr] = next_merge_node_chain_curr
          else
            # we have a next node but no prev -> next is now the last node
            @chain_node_to_same_chain_predecessor[chain_1].delete(next_merge_node_chain_curr)
          end
        else
          # we have NO next merge node, so the current node is the last one
          if prev_node_chain_curr != nil
            @chain_node_to_same_chain_successor[curr_chain].delete(prev_node_chain_curr)
          end
        end


      end
    end

    return true
  end

  def _rebuild_reachable_lists_upward(new_root_reachable_list)

    # same as in _update_reachable_lists
    marked_lists = Set.new
    marked_lists.compare_by_identity

    lists_to_visit = [new_root_reachable_list]

    while lists_to_visit.length > 0
      new_root_reachable_list = lists_to_visit.pop

      # these nodes are all connected to the same reachable list (horizontally)
      merge_nodes_pos_set = @reachable_list_to_connected_nodes[new_root_reachable_list]

      merge_nodes_pos_set.each do |node_pos|
        chain_2, node_2 = node_pos

        # prev_merge_node = self._get_prev_merge_node_excluding_self_improved(chain_2, node_2)
        prev_merge_node = @chain_node_to_same_chain_predecessor[chain_2][node_2]
        next if prev_merge_node == nil

        prev_reachable_list = @nodes_to_reachable_lists_by_chain[chain_2][prev_merge_node]

        if marked_lists.include?(prev_reachable_list)
          next
        end
        marked_lists << prev_reachable_list

        # rebuild the prev reachable list (because reach list further down could have changed because of edge removal)

        was_modified = self._rebuild_reachable_list(prev_reachable_list)

        if was_modified
          # only if the list changes, then we need to check further
          lists_to_visit << prev_reachable_list
        end

      end

    end

  end

  def _rebuild_reachable_list(current_reach_list)

    merge_nodes_pos_set = @reachable_list_to_connected_nodes[current_reach_list]

    new_reach_list = Array.new(@nodes_to_reachable_lists_by_chain.length) { |p| nil }

    merge_nodes_pos_set.each do |node_pos|
      chain_1, node_1 = node_pos

      new_reach_list[chain_1] = node_1
      
      # next_merge_node_1 = self._get_next_merge_node_improved(chain_1, node_1 + 1)
      next_merge_node_1 = @chain_node_to_same_chain_successor[chain_1][node_1]
      next if next_merge_node_1 == nil

      next_reach_list_1 = @nodes_to_reachable_lists_by_chain[chain_1][next_merge_node_1]
      self._merge_reachable_lists_into_1(new_reach_list, next_reach_list_1, nil)
    end

    # we need to modify current_reach_list in place because we use references to reach lists
    was_modified = false
    current_reach_list.each_with_index do | entry, i|
      if current_reach_list[i] != new_reach_list[i]
        current_reach_list[i] = new_reach_list[i]
        was_modified = true
      end
    end

    return was_modified
  end
  
  def _insert_merge_node(chain, node)
    # the nodes are just numbers, we can use binary search to find the position
    # value is not important
    @merge_nodes_by_chain_sorted[chain][node] = node

  end

  def _get_prev_merge_node_improved(chain, node)

    # -1 because it also finds the node itself
    prev_node = @merge_nodes_by_chain_sorted[chain].upper_bound(node)
    return nil if prev_node == nil
    return prev_node[0]
  end

  def _get_prev_merge_node_excluding_self_improved(chain, node)

    # -1 because it also finds the node itself
    prev_node = @merge_nodes_by_chain_sorted[chain].upper_bound(node - 1)
    return nil if prev_node == nil
    return prev_node[0]
  end

  # this can find the node itself if
  def _get_next_merge_node_improved(chain, node)

    next_node = @merge_nodes_by_chain_sorted[chain].lower_bound(node)

    return nil if next_node == nil
    return next_node[0]
  end

  def _get_next_merge_excluding_self_node_improved(chain, node)

    next_node = @merge_nodes_by_chain_sorted[chain].lower_bound(node+1)

    return nil if next_node == nil
    return next_node[0]
  end

  # @return the alignment (array of rows) table but with indices
  # because we can have many-to-many edges, every cell is an array with sentence indices (creating a segment)
  def get_alignment_table

    num_texts = @chain_ranges.size

    align_table = []
    # curr nodes are already processed, thus -1
    curr_node_indices = Array.new(num_texts, -1)

    nodes_processed = 0
    # + size because we start with -1
    total_nodes = @chain_ranges.sum { |range| range.size }
    prev_processed_nodes = 0

    while nodes_processed < total_nodes

      prev_processed_nodes = nodes_processed

      curr_node_indices.each_with_index do |_, chain_index|
        # finished this chain?
        last_node_in_chain = @chain_ranges[chain_index].max
        next if curr_node_indices[chain_index] == last_node_in_chain
        node = curr_node_indices[chain_index]

        next_merge_node = self._get_next_merge_node_improved(chain_index, node + 1) # can be the node itself

        if next_merge_node == nil
          # we can take all sentences in this chain until the end
          while node < last_node_in_chain
            node += 1
            nodes_processed += 1
            row = Array.new(num_texts, nil)
            row[chain_index] = [node]
            align_table << row
            curr_node_indices[chain_index] = node
          end
          next
        end

        while node < next_merge_node - 1
          # we can take all sentences until right before the next merge node
          node += 1
          nodes_processed += 1
          row = Array.new(num_texts, nil)
          row[chain_index] = [node]

          align_table << row
          curr_node_indices[chain_index] = node
        end

        # now the node is the next merge node...
        # but we only can take the node if all the nodes before (higher up in the chains)
        #   the connected nodes (to the current node, from other chains) are processed
        reachable_list = @nodes_to_reachable_lists_by_chain[chain_index][next_merge_node]
        # we have to process all previous nodes before the connected nodes
        connected_nodes_to_list = @reachable_list_to_connected_nodes[reachable_list]

        # check if all previous nodes are processed
        all_prev_nodes_processed = true

        connected_nodes_to_list.each do |connected_node_tuple|
          chain_2, node_2 = connected_node_tuple
          if curr_node_indices[chain_2] != node_2 - 1 # -1 because prev node must have been processed
            all_prev_nodes_processed = false
            break
          end
        end

        # only merge nodes can be m-n edges

        if all_prev_nodes_processed
          # we can finally take the edge
          row = Array.new(num_texts, nil)
          connected_nodes_to_list.each do |connected_node_tuple|
            chain_2, node_2 = connected_node_tuple
            node_2_end_index = @merge_nodes_to_end_nodes_by_chain[chain_2][node_2]
            segment_indices = (node_2..node_2_end_index).to_a
            row[chain_2] = segment_indices
            curr_node_indices[chain_2] = node_2_end_index # processed
            nodes_processed += segment_indices.size
          end
          align_table << row
        end

      end

      if prev_processed_nodes == nodes_processed
        raise "possible infinite loop detected, check that added edges and chain ranges are correct"
      end

    end

    align_table
  end


end