# frozen_string_literal: true

class DfsDagIcd
  def initialize(num_vertices)
    @vertices = (0...num_vertices).to_a
    @adj_list = Hash.new { |hash, key| hash[key] = Set.new }
    @node_names = @vertices.map { |p| "#{p}" } # index to name
    @merged_nodes = Array.new(num_vertices)
    @node_to_chain_mapping = {}
    @num_chains = 0
    @chain_node_sums = [] # this has 1 more for the last chain (so we know the total sum)

    (0...num_vertices).each do |i|
      @merged_nodes[i] = i
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
        self.add_edge(node, node + 1)
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

  def align_edge(edge)
    can_merge = self.can_merge_nodes(edge[0], edge[1])

    if not can_merge
      return false
    end

    self.merge_nodes(edge[0], edge[1])
    return true
  end

  def add_edge(_node_v, _node_w)
    node_v = self._get_real_node_rec(_node_v)
    node_w = self._get_real_node_rec(_node_w)

    if @adj_list[node_v].include?(node_w)
      return false
    end

    @adj_list[node_v] << node_w
    true
  end

  def _add_edge(node_v, node_w)
    if @adj_list[node_v].include?(node_w)
      return false
    end

    @adj_list[node_v] << node_w
    true
  end

  def remove_edge(_node_v, _node_w)
    node_v = self._get_real_node_rec(_node_v)
    node_w = self._get_real_node_rec(_node_w)

    @adj_list[node_v].delete(node_w)
  end

  def _remove_edge(node_v, node_w)
    @adj_list[node_v].delete(node_w)
  end

  def can_merge_nodes(_node_v, _node_w)
    node_v = self._get_real_node_rec(_node_v)
    node_w = self._get_real_node_rec(_node_w)

    was_added = self._add_edge(node_v, node_w)

    return false if not was_added

    has_cycle = self.detect_cycle(node_v, node_w)
    self._remove_edge(node_v, node_w)
    return false if has_cycle

    was_added = self._add_edge(node_w, node_v)
    has_cycle = self.detect_cycle(node_w, node_v)
    self._remove_edge(node_w, node_v) if was_added
    return false if has_cycle

    true
  end

  def _get_real_node_rec(_node_v)
    node_v = @merged_nodes[_node_v]

    return node_v if node_v == _node_v
    _get_real_node_rec(node_v)
  end

  def merge_nodes(_node_v, _node_w)
    node_v = self._get_real_node_rec(_node_v)
    node_w = self._get_real_node_rec(_node_w)

    # merge w into v (only v will be present)
    # make sure there are no duplicate edges (hash already does that)
    # all incoming edges to w --> convert to incoming edges to v
    # all outgoing edges from w --> convert to outgoing edges from v
    # remove all edges between node v, w
    @node_names[node_v] = "#{@node_names[node_v]},#{@node_names[node_w]}"
    @node_names[node_w] = "MERGED"
    @vertices.delete(node_w)
    @merged_nodes[node_w] = node_v

    # outgoing
    @adj_list[node_w].each do |target_node|
      @adj_list[node_v].add(target_node)
    end
    @adj_list[node_v].delete(node_w)
    @adj_list[node_v].delete(node_v)
    @adj_list.delete(node_w)

    # incoming
    @adj_list.each do |node, neighbors|
      next if node == node_v

      if neighbors.include?(node_w)
        neighbors.delete(node_w)
        neighbors.add(node_v)
      end
    end

  end

  def detect_cycle(node_from, node_to)

    # forward search
    has_path_forward = dfs(node_from, node_to)
    has_path_backward = dfs(node_to, node_from)

    has_path_forward && has_path_backward
  end

  def get_as_alignment()
    # make a topological sort
    # simply use Kahn's algorithm

    total_vertices_original = @merged_nodes.length
    # @vertices.each do |node|
    #   total_vertices_original = [total_vertices_original, node+1].max
    # end

    in_degree = Array.new(total_vertices_original, 0)
    @adj_list.each do |node, neighbors|
      neighbors.each do |neighbor|
        in_degree[neighbor] += 1
      end
    end

    queue = []
    @vertices.each do |node|
      queue << node if in_degree[node] == 0
    end

    alignment = []
    topological_sorting = []
    while !queue.empty?
      node = queue.shift
      topological_sorting << node

      _new_row = Array.new(@num_chains, nil)
      node_name = @node_names[node]
      if node_name.include?(",")
        # merged node
        node_name.split(",").each do |n|
          _new_row[@node_to_chain_mapping[n.to_i]] = "#{n}"
        end
      else
        _new_row[@node_to_chain_mapping[node]] = @node_names[node]
      end

      alignment << _new_row

      @adj_list[node].each do |neighbor|
        in_degree[neighbor] -= 1
        # queue << neighbor if in_degree[neighbor] == 0
        queue.unshift(neighbor) if in_degree[neighbor] == 0
      end
    end

    alignment
  end

  private

  def dfs(start_v, end_w)

    visited = Set.new

    dfs_stack = [start_v]

    while dfs_stack.length > 0
      next_node = dfs_stack.shift

      @adj_list[next_node].each do |neighbor|
        return true if neighbor == end_w

        if visited.include?(neighbor)
          next
        end

        visited << neighbor
        dfs_stack.unshift(neighbor)
      end
    end

    false
  end
end

# graph = TiefensucheDAGAlign.new(5)
# graph.add_edge(0, 1)
# graph.add_edge(1, 2)
# graph.add_edge(2, 3)
# graph.add_edge(3, 1) # Kreis
#
# has_cycle = graph.detect_cycle(1,3)
