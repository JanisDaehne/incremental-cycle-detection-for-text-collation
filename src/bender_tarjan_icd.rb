# frozen_string_literal: true
require 'set'
require 'json'

# paper: A New Approach to Incremental Cycle Detection and Related Problems
class BenderTarjanIcd

  attr_accessor :level_k
  attr_accessor :outs
  attr_accessor :ins
  attr_accessor :all_ins
  attr_accessor :delta
  # original node -> merged node
  attr_accessor :merged_nodes
  attr_accessor :node_to_chain_mapping
  attr_accessor :num_chains
  attr_accessor :chain_node_sums # this has 1 more for the last chain (so we know the total sum)

  def initialize()
    self.node_to_chain_mapping = {}
    self.num_chains = 0
    self.chain_node_sums = []
  end

  def init(num_nodes, m)
    # pseudo-topological order
    self.level_k = Array.new(num_nodes, 1)
    self.outs = Array.new(num_nodes)
    self.ins = Array.new(num_nodes)
    # we sometimes empty the ins for a node
    # because it gets into a new level
    # for merging nodes we need all ins
    self.all_ins = Array.new(num_nodes)
    self.delta = Math.sqrt(m)
    self.merged_nodes = Array.new(num_nodes)

    (0...num_nodes).each do |i|
      # better use sets in case of duplicates?
      self.outs[i] = Set.new # entries: [x,y]
      self.ins[i] = Set.new # entries: [x,y]
      self.all_ins[i] = Set.new
      self.merged_nodes[i] = i
    end

  end

  def set_node_to_chain_mapping(chain_ranges, num_chains)

    cumulative_chain_length = 0
    chain_ranges.each_with_index do |node_range, chain_index|
      @chain_node_sums << cumulative_chain_length
      cumulative_chain_length += node_range.size
      node_range.each do |node|
        @node_to_chain_mapping[node] = chain_index
      end
    end
    @chain_node_sums << cumulative_chain_length
    @num_chains = num_chains
  end

  def add_chain_edges

    @chain_node_sums.drop(1).each_with_index do |sum, index|
      pre_sum = @chain_node_sums[index]

      (sum - pre_sum - 1).times.each do |i|
        node = pre_sum + i
        self.add_edge_with_rollback(node, node + 1)
      end
    end
  end

  def chain_edge_to_our_coords_edge(edge)
    # edge: [ [chain, node], [chain, node] ]
    chain_1 = edge[0][0]
    chain_2 = edge[1][0]
    node_1 = edge[0][1]
    node_2 = edge[1][1]

    node_1 += @chain_node_sums[chain_1]
    node_2 += @chain_node_sums[chain_2]

    [node_1, node_2]
  end

  def align_edge(our_edge)
    # our_edge: [node, node] (from chain_edge_to_our_coords_edge)

    self.add_bi_edge_and_merge(our_edge[0], our_edge[1])
  end

  def _get_real_node_rec(_node_v)
    node_v = @merged_nodes[_node_v]

    return node_v if node_v == _node_v
    _get_real_node_rec(node_v)
  end

  # rolls back the state if the given edge introduces a cycle
  def add_edge_with_rollback(_node_v, _node_w)
    # puts "inc check cycle"
    # node_v = @merged_nodes[_node_v]
    # node_w = @merged_nodes[_node_w]
    node_v = self._get_real_node_rec(_node_v)
    node_w = self._get_real_node_rec(_node_w)

    self.all_ins[node_w].add([node_v, node_w])

    # step 1 (test order)
    k_v = self.level_k[node_v]
    k_w = self.level_k[node_w]

    rollback_levels = {}
    rollback_levels[node_w] = k_w
    rollback_ins_list_copy = {}
    rollback_ins_list_copy[node_w] = self.ins[node_w].clone
    # only contains node_v ever but to make it uniform
    rollback_node_v_outs = {}
    rollback_node_v_outs[node_v] = self.outs[node_v].clone

    rollback_state = {
      :rollback_levels => rollback_levels,
      :rollback_ins_list_copy => rollback_ins_list_copy,
      :rollback_node_v_outs => rollback_node_v_outs,
      :rollback_all_ins_from_w => [node_v, node_w]
    }

    # if k_v < k_w goto step 4
    # else goto step 2
    if k_v >= k_w

      # step 2 (search backward)
      # visited nodes (not arcs)
      visited_nodes = Set.new

      used_arcs = Set.new
      nodes_to_visit = Queue.new
      nodes_to_visit << node_v
      # debug_nodes_to_visit = [node_v]
      nodes_to_visit_and_visited = Set.new
      nodes_to_visit_and_visited.add(node_v)
      stop_forward_search = false

      while nodes_to_visit.length > 0
        node_curr = nodes_to_visit.pop
        # debug_nodes_to_visit.shift
        level = self.level_k[node_curr]

        visited_nodes.add(node_curr)
        nodes_to_visit_and_visited.add(node_curr)

        self.ins[node_curr].each do |edge_back|
          node_prev = edge_back[0]

          # the node_prev could have already been visited
          # or the node_prev could be already in the nodes to visit

          # only nodes on the same level
          if self.level_k[node_prev] != level
            next
          end

          if node_prev == node_w # cycle
            # no rollback needed
            self.all_ins[node_w].delete([node_v, node_w])
            return false, nil
          end

          # skip if we already visited this node
          if nodes_to_visit_and_visited.include?(node_prev)
            # we add the edge as visited, we have/will visit the node
            # but the edge is not traversed but we compare it with delta?
          else
            # node not yet discovered
            nodes_to_visit_and_visited.add(node_prev)
            nodes_to_visit.push(node_prev)
            # debug_nodes_to_visit.push(node_prev)
          end

          used_arcs.add(edge_back)

          # at least delta many arcs visited
          if used_arcs.size >= self.delta
            stop_forward_search = true
            break
          end

        end

        if stop_forward_search
          break
        end

      end

      goto_step_4 = false
      rollback_node_w_old_ins = self.ins[node_w]

      if used_arcs.size < self.delta

        if k_w == k_v
          goto_step_4 = true

        elsif k_w < k_v
          self.level_k[node_w] = k_v
          self.ins[node_w] = Set.new
        end

      else
        # used_arcs.size >= self.delta
        self.level_k[node_w] = k_v + 1
        self.ins[node_w] = Set.new
        visited_nodes.clear
        visited_nodes.add(node_v)
      end

      unless goto_step_4 # if not

        # step 3
        nodes_to_visit = Queue.new
        nodes_to_visit << node_w

        nodes_to_visit_set = Set.new
        nodes_to_visit_set.add(node_w)

        while nodes_to_visit.length > 0
          node_curr = nodes_to_visit.pop

          self.outs[node_curr].each do |edge_forward|
            node_x = edge_forward[0]
            node_y = edge_forward[1]

            # cycle?
            if visited_nodes.include?(node_y)

              # rollback state
              self._rollback_with_state(rollback_state)

              return false, nil
            end

            k_x = self.level_k[node_x]
            k_y = self.level_k[node_y]

            if k_x == k_y
              # can we visit this node again??
              if not rollback_ins_list_copy.has_key?(node_y)
                rollback_ins_list_copy[node_y] = self.ins[node_y].clone
              end

              self.ins[node_y].add(edge_forward)

            elsif k_y < k_x # <=> k(x) > k(y)
              # can we visit this node again??
              if not rollback_levels.has_key?(node_y)
                rollback_levels[node_y] = k_y
              end
              # can we visit this node again??
              if not rollback_ins_list_copy.has_key?(node_y)
                rollback_ins_list_copy[node_y] = self.ins[node_y].clone
              end

              self.level_k[node_y] = k_x
              self.ins[node_y] = Set.new([edge_forward])

              self.outs[node_y].each do |edge|

                if nodes_to_visit_set.include?(edge[0])
                  next
                end
                nodes_to_visit_set.add(edge[0])

                nodes_to_visit << edge[0]
              end
            end

          end

        end

      end

    end

    # step 4 (insert arc)

    # might have changed
    k_v = self.level_k[node_v]
    k_w = self.level_k[node_w]

    self.outs[node_v].add([node_v, node_w])

    if k_v == k_w
      self.ins[node_w].add([node_v, node_w])
    end

    [true, rollback_state]
  end

  # rolls back the state if the given edge introduces a cycle
  def add_back_edge_with_rollback(_node_v, _node_w, first_edge)
    # puts "inc check cycle"
    # node_v = @merged_nodes[_node_v]
    # node_w = @merged_nodes[_node_w]
    node_v = self._get_real_node_rec(_node_v)
    node_w = self._get_real_node_rec(_node_w)

    self.all_ins[node_w].add([node_v, node_w])

    # step 1 (test order)
    k_v = self.level_k[node_v]
    k_w = self.level_k[node_w]

    # if k_v < k_w goto step 4
    # else goto step 2
    if k_v >= k_w

      # step 2 (search backward)
      # visited nodes (not arcs)
      visited_nodes = Set.new

      used_arcs = Set.new
      nodes_to_visit = Queue.new
      nodes_to_visit << node_v
      # debug_nodes_to_visit = [node_v]
      nodes_to_visit_and_visited = Set.new
      nodes_to_visit_and_visited.add(node_v)
      stop_forward_search = false

      while nodes_to_visit.length > 0
        node_curr = nodes_to_visit.pop
        # debug_nodes_to_visit.shift
        level = self.level_k[node_curr]

        visited_nodes.add(node_curr)
        nodes_to_visit_and_visited.add(node_curr)

        self.ins[node_curr].each do |edge_back|

          if edge_back == first_edge
            next
          end

          node_prev = edge_back[0]

          # the node_prev could have already been visited
          # or the node_prev could be already in the nodes to visit

          # only nodes on the same level
          if self.level_k[node_prev] != level
            next
          end

          if node_prev == node_w # cycle
            # no rollback needed
            self.all_ins[node_w].delete([node_v, node_w])
            return false
          end

          # skip if we already visited this node
          if nodes_to_visit_and_visited.include?(node_prev)
            # we add the edge as visited, we have/will visit the node
            # but the edge is not traversed but we compare it with delta?
          else
            # node not yet discovered
            nodes_to_visit_and_visited.add(node_prev)
            nodes_to_visit.push(node_prev)
            # debug_nodes_to_visit.push(node_prev)
          end

          used_arcs.add(edge_back)

          # at least delta many arcs visited
          if used_arcs.size >= self.delta
            stop_forward_search = true
            break
          end

        end

        if stop_forward_search
          break
        end

      end

      goto_step_4 = false
      rollback_node_w_old_ins = self.ins[node_w]

      if used_arcs.size < self.delta

        if k_w == k_v
          goto_step_4 = true

        elsif k_w < k_v
          self.level_k[node_w] = k_v
          self.ins[node_w] = Set.new
        end

      else
        # used_arcs.size >= self.delta
        self.level_k[node_w] = k_v + 1
        self.ins[node_w] = Set.new
        visited_nodes.clear
        visited_nodes.add(node_v)
      end

      unless goto_step_4 # if not

        # step 3
        nodes_to_visit = Queue.new
        nodes_to_visit << node_w

        nodes_to_visit_set = Set.new
        nodes_to_visit_set.add(node_w)

        rollback_ins_list_copy = {}
        rollback_levels = {}

        while nodes_to_visit.length > 0
          node_curr = nodes_to_visit.pop

          self.outs[node_curr].each do |edge_forward|

            if edge_forward == first_edge
              next
            end

            node_x = edge_forward[0]
            node_y = edge_forward[1]

            # cycle?
            if visited_nodes.include?(node_y)

              # rollback state
              begin
                self.level_k[node_w] = k_w
                self.ins[node_w] = rollback_node_w_old_ins

                rollback_levels.each do |node_idx, level|
                  self.level_k[node_idx] = level
                end
                rollback_ins_list_copy.each do |node_idx, ins_set|
                  self.ins[node_idx] = ins_set
                end

                self.all_ins[node_w].delete([node_v, node_w])
              end

              return false
            end

            k_x = self.level_k[node_x]
            k_y = self.level_k[node_y]

            if k_x == k_y
              if not rollback_ins_list_copy.has_key?(node_y)
                rollback_ins_list_copy[node_y] = self.ins[node_y].clone
              end

              self.ins[node_y].add(edge_forward)

            elsif k_y < k_x # <=> k(x) > k(y)
              if not rollback_levels.has_key?(node_y)
                rollback_levels[node_y] = k_y
              end
              if not rollback_ins_list_copy.has_key?(node_y)
                rollback_ins_list_copy[node_y] = self.ins[node_y].clone
              end

              self.level_k[node_y] = k_x
              self.ins[node_y] = Set.new([edge_forward])

              self.outs[node_y].each do |edge|

                if nodes_to_visit_set.include?(edge[0])
                  next
                end
                nodes_to_visit_set.add(edge[0])

                nodes_to_visit << edge[0]
              end
            end

          end

        end

      end

    end

    # step 4 (insert arc)

    # might have changed
    k_v = self.level_k[node_v]
    k_w = self.level_k[node_w]

    self.outs[node_v].add([node_v, node_w])

    if k_v == k_w
      self.ins[node_w].add([node_v, node_w])
    end

    true
  end

  def _rollback_with_state(rollback_state)
    rollback_levels = rollback_state[:rollback_levels]
    rollback_ins_list_copy = rollback_state[:rollback_ins_list_copy]
    rollback_node_v_outs = rollback_state[:rollback_node_v_outs]
    rollback_all_ins_from_w = rollback_state[:rollback_all_ins_from_w]

    rollback_levels.each do |node_idx, level|
      self.level_k[node_idx] = level
    end
    rollback_ins_list_copy.each do |node_idx, ins_set|
      self.ins[node_idx] = ins_set
    end

    rollback_node_v_outs.each do |node_idx, out_set|
      self.outs[node_idx] = out_set
    end

    node_v = rollback_all_ins_from_w[0]
    node_w = rollback_all_ins_from_w[1]
    self.all_ins[node_w].delete([node_v, node_w])
  end

  def print_level_stats
    level_stats = {}
    self.level_k.each do |level|
      if level_stats.has_key?(level)
        level_stats[level] += 1
      else
        level_stats[level] = 1
      end
    end

    puts level_stats.to_json

  end

  # add a bidirectional edge [v,w] AND then [w,v]
  def add_bi_edge_and_merge(_node_v, _node_w)
    # node_v = @merged_nodes[_node_v]
    # node_w = @merged_nodes[_node_w]
    node_v = self._get_real_node_rec(_node_v)
    node_w = self._get_real_node_rec(_node_w)

    return false if node_v == node_w

    # check if we already have this edge...
    # if we already have this edge, we must not ignore it in the second check

    if @outs[node_v].include?([node_v, node_w])
      return false
    end

    # this already rolls back the state internally if a cycle is detected
    was_added, rollback_state = self.add_edge_with_rollback(node_v, node_w)
    # puts state_to_dot(true)
    return false if !was_added

    # we essentially look for a circle with more than 2 nodes
    first_edge = [node_v, node_w]
    was_added = self.add_back_edge_with_rollback(node_w, node_v, first_edge)

    # if second check is false but first was ok, rollback the first arcs too
    if not was_added
      self._rollback_with_state(rollback_state)
    end

    # puts state_to_dot(true)
    return false unless was_added

    # no cycle here
    # but if we really add the back edge we would get a cycle
    # thus, we merge the nodes -> no cycle
    self._merge_nodes(node_v, node_w)

    # puts state_to_dot(true)

    true
  end

  def _merge_nodes(_node_v, _node_w)


    # node_v = @merged_nodes[_node_v]
    # node_w = @merged_nodes[_node_w]
    node_v = self._get_real_node_rec(_node_v)
    node_w = self._get_real_node_rec(_node_w)
    tmp = node_v
    node_v = [node_v, node_w].min
    node_w = [tmp, node_w].max

    # we don't need to use _get_real_node_rec below
    # because the internal edges are always up to date when merged
    # only when we add edges (from outside) we need to get the real mapped/merged node

    # merge w into v (only v will be kept)

    # change all parents of w (parent has out[] with w)
    # we need to use all_ins because normally we only have ins from the same level
    self.all_ins[node_w].each do |edge|
      node_parent = @merged_nodes[edge[0]]
      next if node_parent == node_v # we just added this edge

      # no include check here because outs are never deleted/reset
      self.outs[node_parent].delete(edge)
      self.outs[node_parent].add([node_parent, node_v])

      self.all_ins[node_v].add([node_parent, node_v])
    end

    self.ins[node_w].each do |edge|
      node_parent = @merged_nodes[edge[0]]
      self.ins[node_v].add([node_parent, node_v])
    end

    # change all children of w (child has in[] with w)
    # outs is never deleted/reset only added -> always correct
    self.outs[node_w].each do |edge|
      node_child = @merged_nodes[edge[1]]
      next if node_child == node_v # we just added this edge

      # only add in edge, if it was there already
      if self.ins[node_child].include?(edge)
        self.ins[node_child].delete(edge)
        self.ins[node_child].add([node_v, node_child])
      end

      if self.all_ins[node_child].include?(edge)
        self.all_ins[node_child].delete(edge)
        self.all_ins[node_child].add([node_v, node_child])
      end

      self.outs[node_v].add([node_v, node_child])
    end

    self.ins[node_v].delete([node_v, node_w])
    self.ins[node_v].delete([node_w, node_v])
    self.ins[node_v].delete([node_v, node_v])

    self.all_ins[node_v].delete([node_v, node_w])
    self.all_ins[node_v].delete([node_w, node_v])
    self.all_ins[node_v].delete([node_v, node_v])

    self.outs[node_v].delete([node_v, node_w])
    self.outs[node_v].delete([node_w, node_v])
    self.outs[node_v].delete([node_v, node_v])

    self.level_k[node_v] = [self.level_k[node_v], self.level_k[node_w]].min

    self.level_k[node_w] = nil
    self.ins[node_w] = Set.new
    self.all_ins[node_w] = Set.new
    self.outs[node_w] = Set.new

    self.merged_nodes[node_w] = node_v

  end

  def _clone_state()
    outs_deep_clone = Array.new(self.outs.size)
    self.outs.each_with_index do |_out, i|
      outs_deep_clone[i] = _out.clone
    end

    ins_deep_clone = Array.new(self.outs.size)
    self.ins.each_with_index do |_ins, i|
      ins_deep_clone[i] = _ins.clone
    end

    _all_ins_deep_clone = Array.new(self.outs.size)
    self.all_ins.each_with_index do |_all_ins, i|
      _all_ins_deep_clone[i] = _all_ins.clone
    end

    rollback_state = {
      :level_k => self.level_k.clone,
      :outs => outs_deep_clone,
      :ins => ins_deep_clone,
      :all_ins => _all_ins_deep_clone,
      :merged_nodes => self.merged_nodes.clone,
    }
    rollback_state

  end

  def _clone_state_as_str()
    rollback_state = {
      :level_k => self.level_k,
      :outs => self.outs,
      :ins => self.ins,
      :all_ins => self.all_ins,
      :merged_nodes => self.merged_nodes,
    }
    JSON.dump(rollback_state)
  end


  def get_all_nodes_mapping_to_node(node)

    nodes_to_check = [node]
    all_nodes = Set.new

    while nodes_to_check.length > 0
      curr_node = nodes_to_check.pop
      @merged_nodes.each_with_index do |mapped_node, src_node|
        if mapped_node == curr_node
          if not all_nodes.include?(src_node)
            all_nodes << src_node
            nodes_to_check << src_node
          end
        end
      end
    end

    all_nodes
  end

  def get_as_alignment
    # make a topological sort
    # simply use Kahn's algorithm

    total_vertices_original = @merged_nodes.length

    in_degree = Array.new(total_vertices_original, 0)
    @all_ins.each_with_index do |neighbors_set, node|
      neighbors_set.each do |edge|
        neighbor = edge[1]
        in_degree[neighbor] += 1
      end
    end

    queue = []
    @all_ins.each_with_index.map { |p, node| node }.each do |node|
      # filter out neighbors that were merged
      mapped_node = @merged_nodes[node]
      next if mapped_node != node

      queue << node if in_degree[node] == 0
    end

    alignment = []
    topological_sorting = []
    while !queue.empty?
      node = queue.shift
      topological_sorting << node

      mapped_to_node = @merged_nodes[node]
      # get all nodes that are mapped to the mapped node (the real merge node)
      full_node = self.get_all_nodes_mapping_to_node(mapped_to_node)
      _new_row = Array.new(@num_chains, nil)
      full_node.each do |n|
        _new_row[@node_to_chain_mapping[n.to_i]] = "#{n}"
      end

      alignment << _new_row

      # @adj_list[node].each do |neighbor|
      @outs[node].each do |edge|
        neighbor = edge[1]
        in_degree[neighbor] -= 1
        queue.unshift(neighbor) if in_degree[neighbor] == 0
      end
    end

    alignment
  end

end
