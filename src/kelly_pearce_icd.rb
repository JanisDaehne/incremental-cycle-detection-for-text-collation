# frozen_string_literal: true
require 'set'

# from the paper A Dynamic Topological Sort Algorithm for Directed Acyclic Graphs
# maintains a topological order of a directed acyclic raph (DAG)
class KellyPearceIcd

  def initialize(num_nodes)
    @ord = Array.new(num_nodes) { |i| i }
    @outgoing_nodes = Hash.new { |hash, key| hash[key] = Set.new }
    @incoming_nodes = Hash.new { |hash, key| hash[key] = Set.new }

    @visited = Array.new(num_nodes, false)

    @_delta_F_xy_set = Set.new
    @_delta_B_xy_set = Set.new

    @merged_nodes = Array.new(num_nodes) { |i| i }
  end

  # # chain edges never introduce a cycle
  # def add_chain_edge(x,y)
  #
  # end

  def _get_real_node_rec(_node_v)
    node_v = @merged_nodes[_node_v]

    return node_v if node_v == _node_v
    _get_real_node_rec(node_v)
  end

  # merge y into x
  def can_merge_nodes(_x, _y)
    node_x = self._get_real_node_rec(_x)
    node_y = self._get_real_node_rec(_y)

    return false if node_x == node_y

    # special case: edge is a chain edge because of merged nodes
    if @outgoing_nodes[node_x].include?(node_y)
      return false
    end

    can_add = self.add_edge(node_x, node_y)
    self.remove_edge(node_x, node_y)
    return false if !can_add

    can_add = self.add_edge(node_y, node_x)
    self.remove_edge(node_y, node_x)
    return false if !can_add

    true
  end

  def merge_nodes(_x, _y)
    node_x = self._get_real_node_rec(_x)
    node_y = self._get_real_node_rec(_y)

    # no cycle -> merge edges
    @merged_nodes[node_y] = node_x

    # outgoing
    @outgoing_nodes[node_y].each do |target_node|
      @outgoing_nodes[node_x].add(target_node)
    end
    @outgoing_nodes[node_x].delete(node_y)
    @outgoing_nodes[node_x].delete(node_x)
    @outgoing_nodes.delete(node_y)

    # incoming
    @incoming_nodes[node_y].each do |node|
      next if node == node_x
      @incoming_nodes[node_x] << node
    end

    @incoming_nodes.delete(node_y)
    @visited[node_y] = nil

    @ord[node_y] = nil

  end

  def add_edge(x, y)

    @outgoing_nodes[x] << y
    @incoming_nodes[y] << x

    lb = @ord[y]
    ub = @ord[x]

    if lb < ub
      @_delta_F_xy_set.clear
      @_delta_B_xy_set.clear

      # discovery
      has_cycle = self.dfs_f(y, ub)

      @_delta_F_xy_set.each_with_index do |node_w, i|
        @visited[node_w] = false
      end

      if has_cycle
        return false
      end

      has_cycle = self.dfs_b(x, lb)

      @_delta_B_xy_set.each_with_index do |node_w, i|
        @visited[node_w] = false
      end

      if has_cycle
        return false
      end
      # reassignment
      self.reorder()
    end

    true
  end

  # paper: remove is trivial as this does not destroy the topoligical order
  def remove_edge(x, y)
    @outgoing_nodes[x].delete(y)
    @incoming_nodes[y].delete(x)
  end

  # forward
  def dfs_f(_node_index, ub)
    stack = [_node_index] # Use a tuple/array for [node, ub_for_this_path]

    while !stack.empty?
      current_node_param = stack.pop
      node_index = self._get_real_node_rec(current_node_param)

      # If we have already visited and processed this node's children in the *current* DFS exploration,
      # we can skip it. The @visited array is reset for @_delta_F_xy_set and @_delta_B_xy_set
      # before dfs_f or dfs_b are called again in add_edge, or after they complete.
      next if @visited[node_index]

      @visited[node_index] = true
      @_delta_F_xy_set << node_index

      child_nodes = []

      @outgoing_nodes[node_index].each do |_node_w|
        node_w_real = self._get_real_node_rec(_node_w)
        ord_w = @ord[node_w_real]

        if ord_w == ub # Cycle detected
          return true
        end

        # Is w unvisited (in this DFS call) and in the affected region?
        if !@visited[node_w_real] && ord_w < ub
          child_nodes << node_w_real
        end
      end

      stack.push(*child_nodes.reverse!)
    end

    false # No cycle found
  end

  # backward
  def dfs_b(_node_index, lb)
    stack = [_node_index] # Start with the initial node parameter

    while !stack.empty?
      current_node_param = stack.pop
      node_index = self._get_real_node_rec(current_node_param)

      # If this actual node was already visited and processed in this DFS traversal, skip
      # @visited array uses the actual node index.
      next if @visited[node_index]

      @visited[node_index] = true
      @_delta_B_xy_set << node_index

      child_nodes = []
      # Iterate over incoming neighbors of the current actual node.
      # We use the resolved 'node_index' to access its neighbors.
      @incoming_nodes[node_index].each do |_neighbor_node_param|
        node_w_real = self._get_real_node_rec(_neighbor_node_param)
        ord_w = @ord[node_w_real]
        if ord_w == lb # Cycle detected
          return true
        end

        # If the actual neighbor 'node_w' is unvisited (in this DFS traversal, checked using its actual form)
        # and is in the affected region (lb < ord_w), push its actual form to stack.
        if !@visited[node_w_real] && lb < ord_w
          child_nodes.push(node_w_real)
        end
      end

      stack.push(*child_nodes.reverse!)
    end

    false # No cycle found
  end

  def reorder()

    delta_B_xy = @_delta_B_xy_set.to_a
    delta_F_xy = @_delta_F_xy_set.to_a

    delta_B_xy.sort_by!{|p|  @ord[p]}
    delta_F_xy.sort_by!{|p|  @ord[p]}
    var_l = []

    delta_B_xy.each_with_index do |node_w, i|
      delta_B_xy[i] = @ord[node_w]
      # @visited[node_w] = false
      var_l << node_w
    end

    delta_F_xy.each_with_index do |node_w, i|
      delta_F_xy[i] = @ord[node_w]
      # @visited[node_w] = false
      var_l << node_w
    end

    # merge
    var_R = []
    self._merge(delta_B_xy, delta_F_xy, var_R)

    var_l.each_with_index do |node_w, i|
      @ord[node_w] = var_R[i]
    end

  end

  def _merge(delta_B_xy, delta_F_xy, out_R)

    index_b = 0
    index_f = 0
    max_index_sum = delta_B_xy.length + delta_F_xy.length

    (0...max_index_sum).each do |i|
      el_b = index_b < delta_B_xy.length ? delta_B_xy[index_b] : @ord.length
      el_f = index_f < delta_F_xy.length ? delta_F_xy[index_f] : @ord.length

      if el_b <= el_f
        out_R << el_b
        index_b += 1
      else
        out_R << el_f
        index_f += 1
      end
    end

  end

end