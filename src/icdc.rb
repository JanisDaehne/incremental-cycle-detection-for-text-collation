# frozen_string_literal: true
require 'set'
require 'rbtree'

class IncrementalCycleDetectionWithChains

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
  attr_accessor :merge_nodes_by_chain

  # [reachable list] -> set of nodes that have this reachable list
  attr_accessor :reachable_list_to_connected_nodes
  attr_accessor :chain_ranges
  attr_accessor :merge_nodes_to_edges

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

  def can_add_edge?(edge)
    !self.edge_introduces_cycle?(edge)
  end

  def edge_introduces_cycle?(edge)
    chain_1, node_1 = edge[0]
    chain_2, node_2 = edge[1]

    # get next merging edge for both nodes (in same chain)

    # next_merge_edge_1 = self._get_next_merge_node(chain_1, node_1)
    # next_merge_edge_2 = self._get_next_merge_node(chain_2, node_2)
    next_merge_node_1 = self._get_next_merge_node_improved(chain_1, node_1)
    next_merge_node_2 = self._get_next_merge_node_improved(chain_2, node_2)

    reachable_list_1 = @nodes_to_reachable_lists_by_chain[chain_1][next_merge_node_1]
    reachable_list_2 = @nodes_to_reachable_lists_by_chain[chain_2][next_merge_node_2]

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

  # this does not check for cycles!
  # @param edge [[chain idx, node idx], [chain idx, node idx]]
  def add_edge(edge)
    chain_1, node_1 = edge[0]
    chain_2, node_2 = edge[1]

    # todo check duplicate edge?

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
    # next_merge_node_1 = self._get_next_merge_node(chain_1, node_1)
    # next_merge_node_2 = self._get_next_merge_node(chain_2, node_2)
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

      self._insert_merge_node(chain_1, node_1)
      self._insert_merge_node(chain_2, node_2)

    elsif reachable_list_1 == nil
      # we already have list 2, we might have to update it (entry of chain 1)
      reachable_list_2[chain_1] = node_1
      reachable_list_1 = reachable_list_2 # same reference

      @reachable_list_to_connected_nodes[reachable_list_2] << [chain_1, node_1]

      @nodes_to_reachable_lists_by_chain[chain_1][node_1] = reachable_list_1

      self._insert_merge_node(chain_1, node_1)

    elsif reachable_list_2 == nil
      # we already have list 1, we might have to update it (entry of chain 1)
      reachable_list_1[chain_2] = node_2
      reachable_list_2 = reachable_list_1 # same reference

      @reachable_list_to_connected_nodes[reachable_list_1] << [chain_2, node_2]

      @nodes_to_reachable_lists_by_chain[chain_2][node_2] = reachable_list_2

      self._insert_merge_node(chain_2, node_2)

    else
      # we have both lists, we have to merge them
      # merge reachable lists
      self._merge_reachable_lists_into_1(reachable_list_1, reachable_list_2, edge)

      # these are always true/reachable (ensure these are correct)
      reachable_list_1[chain_1] = node_1
      reachable_list_1[chain_2] = node_2
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

    # however, node_1 and node_2 probably have a next merge node in their respective chain
    # currently, we only have the reachable list for node_1 and node_2 but all other nodes further down
    # are also reachable (via the next merge node)
    # so, we have to update the reachable lists for node_1/node_2 with the next merge edge

    # the next merge edges may or may not be connected
    # (if they were connected then they have the same list, same reference -> only one merge needed
    #  but this is often not the case)
    #
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


    self._update_reachable_lists([chain_1, node_1], reachable_list_1)

  end

  def _update_reachable_lists(root_node_pos, root_reachable_list)
    # we only have to update upward the chains (and connected horizontal nodes), we never update downward
    # thus, we can first update horizontal nodes and then the chain
    # we can encounter the same node multiple times (we don't care because we use min)

    marked_lists = Set.new
    marked_lists.compare_by_identity
    # counts = Hash.new
    # counts.compare_by_identity

    lists_to_visit = [root_reachable_list]

    while lists_to_visit.length > 0
      reachable_list = lists_to_visit.pop

      # these nodes are all connected to the same reachable list (horizontally)
      merge_nodes_pos_set = @reachable_list_to_connected_nodes[reachable_list]

      merge_nodes_pos_set.each do |node_pos|
        chain_2, node_2 = node_pos
        # prev_merge_node = self._get_prev_merge_node(chain_2, node_2)

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
        marked_lists << prev_reachable_list

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

    _start_node = edge[0]
    node_queue = [_start_node]
    found_nodes.add(_start_node)

    while node_queue.length > 0
      _node = node_queue.pop
      chain, node_idx = _node

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
    chain_1, node_1 = edge[0]
    chain_2, node_2 = edge[1]

    # deleting is more difficult than adding because we don't know
    # version 4 remove did not work so a new idea:
    # after we removed the edge and we have the two remaining direct connected node sets
    # we go up the tree from these nodes and fully remove/invalid the reach list (rebuild it)
    #   if the reach list changed, do this recursively upward
    #   rebuilding works because adding an edge works and we only need the next merge nodes
    #   (almost same as adding)

    reachable_list_1 = @nodes_to_reachable_lists_by_chain[chain_1][node_1]
    reachable_list_2 = @nodes_to_reachable_lists_by_chain[chain_2][node_2]

    # check if the edge exists
    # if they are connected, then they have the same reach
    if reachable_list_1 == nil || reachable_list_1 != reachable_list_2
      return false
    end

    direct_reachable_1 = @merge_nodes_to_direct_reach[chain_1][node_1]
    direct_reachable_2 = @merge_nodes_to_direct_reach[chain_2][node_2]

    direct_reachable_1.delete(edge[1])
    direct_reachable_2.delete(edge[0])

    # because they have an edge, they have the same reach list and connected nodes
    # horizontally all nodes with the same list are reachable, thus these are all nodes (max = number of chains)
    # follow the edges until one of the remove nodes is found, the remaining nodes in reachable_nodes_0 are in the other set

    reachable_nodes_1, reachable_nodes_2 = self._split_connected_nodes_list(edge, reachable_list_1)

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
      # because any previous node in the same change will use itself as an entry for the current chain entry

      self._rebuild_reachable_lists_upward(new_reach_list)

      if reachable_nodes.length == 1
        # remove the node because it is not longer a merge node
        reach_list = @nodes_to_reachable_lists_by_chain[curr_chain][curr_node]
        @nodes_to_reachable_lists_by_chain[curr_chain].delete(curr_node)
        @merge_nodes_by_chain_sorted[curr_chain].delete(curr_node)
        @reachable_list_to_connected_nodes.delete(reach_list)

        # get prev node
        prev_node_chain_curr = @chain_node_to_same_chain_predecessor[curr_chain][curr_node]
        @chain_node_to_same_chain_predecessor[curr_chain].delete(curr_node)

        # next_merge_node_chain_curr = self._get_next_merge_excluding_self_node_improved(curr_chain, curr_node)
        next_merge_node_chain_curr = @chain_node_to_same_chain_successor[curr_chain][curr_node]
        @chain_node_to_same_chain_successor[curr_chain].delete(curr_node)

        if next_merge_node_chain_curr != nil

          if prev_node_chain_curr != nil
            # the next merge node now has the prev node as a predecessor
            @chain_node_to_same_chain_predecessor[curr_chain][next_merge_node_chain_curr] = prev_node_chain_curr
            @chain_node_to_same_chain_successor[curr_chain][prev_node_chain_curr] = next_merge_node_chain_curr
          else
            # we have a next node but no prev -> next is now the last node
            @chain_node_to_same_chain_predecessor[curr_chain].delete(next_merge_node_chain_curr)
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

  def _get_prev_merge_node_excluding_self_improved(chain, node)

    # -1 because it also finds equal nodes
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

  # @return the alignment table but with indices
  def get_alignment_table

    num_texts = @chain_ranges.size

    align_table = []
    # curr nodes are already processed, thus -1
    curr_node_indices = Array.new(num_texts, -1)

    nodes_processed = 0
    # + size because we start with -1
    total_nodes = @chain_ranges.sum { |range| range.size }

    while nodes_processed < total_nodes

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
            row[chain_index] = node
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
          row[chain_index] = node
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

        if all_prev_nodes_processed
          # we can finally take the edge
          row = Array.new(num_texts, nil)
          connected_nodes_to_list.each do |connected_node_tuple|
            chain_2, node_2 = connected_node_tuple
            row[chain_2] = node_2
            curr_node_indices[chain_2] = node_2 # processed
            nodes_processed += 1
          end
          align_table << row
        end

      end

    end

    align_table
  end


end