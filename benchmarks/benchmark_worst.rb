# frozen_string_literal: true

require 'benchmark'
require_relative '../src/icdc'
require_relative '../src/multi_icdc'
require_relative '../src/dfs_dag'
require_relative '../src/kelly_pearce_icd'
require_relative '../src/bender_tarjan_icd'

### helper functions

# convert normal edge to many-to-many 1-1 edge
def _normal_edge_to_1_1_edge(edge)
  [[edge[0][0], edge[0][1], 1], [edge[1][0], edge[1][1], 1]]
end

def generate_worst_case_graph_bottom_to_top(nodes_per_chain, chains)
  edges = Set.new

  # last chain has remaining nodes
  nodes = nodes_per_chain * chains
  chains_with_nodes = []

  chain_edges = []

  chains.times.each_with_index do |chain_index|
    chain_start_node = chain_index * nodes_per_chain
    chain_nodes = [chain_start_node]

    (nodes_per_chain - 1).times.each_with_index do |i|
      start_node = chain_start_node + i
      end_node = chain_start_node + i + 1
      chain_edges.push([start_node, end_node])
      chain_nodes << end_node
    end

    chains_with_nodes << chain_nodes
  end

  # worst case is adding all edges from bottom to top from left to right
  # starting from the first with chain 3, all reach information has to be updated

  end_chain = chains - 1

  (0...chains - 1).each do |chain_1|
    chain_2 = chain_1 + 1

    nodes_chain_1 = chains_with_nodes[chain_1]
    nodes_chain_2 = chains_with_nodes[chain_2]

    nodes_chain_1.reverse.each_with_index do |node_1, node_index|
      node_2 = nodes_chain_2[nodes_chain_2.length - 1 - node_index]
      edges.add([node_1, node_2])
    end

  end

  edges = edges.to_a
  [chain_edges, edges]
end

def generate_graph_top_to_bottom(nodes_per_chain, chains)
  edges = Set.new

  # last chain has remaining nodes
  nodes = nodes_per_chain * chains
  chains_with_nodes = []

  chain_edges = []

  chains.times.each_with_index do |chain_index|
    chain_start_node = chain_index * nodes_per_chain
    chain_nodes = [chain_start_node]

    (nodes_per_chain - 1).times.each_with_index do |i|
      start_node = chain_start_node + i
      end_node = chain_start_node + i + 1
      chain_edges.push([start_node, end_node])
      chain_nodes << end_node
    end

    chains_with_nodes << chain_nodes
  end

  # worst case is adding all edges from top to bottom from left to right
  # starting from the first with chain 3, all reach information has to be updated

  end_chain = chains - 1

  (0...chains - 1).each do |chain_1|
    chain_2 = chain_1 + 1

    nodes_chain_1 = chains_with_nodes[chain_1]
    nodes_chain_2 = chains_with_nodes[chain_2]

    nodes_chain_1.each_with_index do |node_1, node_index|
      node_2 = nodes_chain_2[node_index]
      edges.add([node_1, node_2])
    end

  end

  edges = edges.to_a
  [chain_edges, edges]
end

def _get_edge_as_chain_pos(node_to_chain_ranges, edge)
  # e.g. node_to_chain_ranges = [
  #   0..9,
  #   10..19,
  #   20..29,
  # ]

  node_1 = edge.first
  node_2 = edge.last
  mapped_edge = []

  node_to_chain_ranges.each_with_index do |node_range, chain_index|
    if node_range.include?(node_1)
      mapped_edge << [chain_index, node_1 - node_range.begin]
      break
    end
  end

  node_to_chain_ranges.each_with_index do |node_range, chain_index|
    if node_range.include?(node_2)
      mapped_edge << [chain_index, node_2 - node_range.begin]
      break
    end
  end

  if mapped_edge.size != 2
    raise RuntimeError()
  end

  mapped_edge
end

def array_avg(array)
  array.sum / array.length.to_f
end

### end helper functions

def create_icdc(chain_ranges)

  aligner = IncrementalCycleDetectionWithChains.new
  aligner.init(chain_ranges)

  return aligner
end

def create_multi_icdc(chain_ranges)

  aligner = MultiIncrementalCycleDetectionWithChains.new
  aligner.init(chain_ranges)

  return aligner
end

def create_dfs(num_nodes)
  dfs = DfsDagIcd.new(num_nodes)

  return dfs
end

def create_kelly_icd(num_nodes)
  kelly = KellyPearceIcd.new(num_nodes)

  return kelly
end

def create_bender_icd(num_nodes, chain_edges, edges)
  icd = BenderTarjanIcd.new
  total_edges = chain_edges.length + edges.length
  icd.init(num_nodes, total_edges)

  return icd
end


# bottom to top is worst case for our approach
def bench_worst_case_graph(chains, nodes_per_chain, num_runs, include_graph_edges_in_times, only_chain_graphs, bottom_to_top = true)

  num_nodes = chains * nodes_per_chain
  if bottom_to_top
    chain_edges, edges = generate_worst_case_graph_bottom_to_top(nodes_per_chain, chains)
  else
    chain_edges, edges = generate_graph_top_to_bottom(nodes_per_chain, chains)
  end

  node_to_chain_ranges = []
  chain_ranges = []
  chains.times.each do |chain_index|
    node_to_chain_ranges << Range.new(nodes_per_chain * chain_index, nodes_per_chain * (chain_index + 1) - 1)
    chain_ranges << Range.new(0, nodes_per_chain - 1)
  end

  mapped_edges = edges.map { |e| _get_edge_as_chain_pos(node_to_chain_ranges, e) }

  puts ""
  puts "--- worst case edges, #{bottom_to_top ? "bottom to top" : "top to bottom"}, chains: #{chains}, nodes_per_chain: #{nodes_per_chain}, edge_count: #{edges.length}, num_runs (avg): #{num_runs}, runtimes in seconds"

  times_dfs_icd = []
  times_kelly_icd = []
  times_bender_icd = []
  times_icdc = []
  times_multi_icdc = []

  dfs_icd_merged_count = 0
  kelly_icd_merged_count = 0
  bender_icd_merged_count = 0
  icdc_merged_count = 0
  multi_icdc_merged_count = 0

  num_runs.times do |i|

    dfs_icd = create_dfs(num_nodes)
    kelly_icd = create_kelly_icd(num_nodes)
    bender_icd = create_bender_icd(num_nodes, chain_edges, edges)
    icdc = create_icdc(chain_ranges)
    multi_icdc = create_multi_icdc(chain_ranges)

    dfs_icd_merged_count = 0
    kelly_icd_merged_count = 0
    bender_icd_merged_count = 0
    icdc_merged_count = 0
    multi_icdc_merged_count = 0

    unless only_chain_graphs
      times_dfs_icd << Benchmark.measure do

        chain_edges.each do |edge|
          node_v, node_w = edge
          dfs_icd.add_edge(node_v, node_w)
        end

        edges.each do |edge|
          node_v, node_w = edge
          can_merge = dfs_icd.can_merge_nodes(node_v, node_w)

          if can_merge
            dfs_icd.merge_nodes(node_v, node_w)
            dfs_icd_merged_count += 1
          end
        end
      end
    end

    unless only_chain_graphs
      times_kelly_icd << Benchmark.measure do
        edges.each do |edge|
          node_v, node_w = edge
          can_merge = kelly_icd.can_merge_nodes(node_v, node_w)

          if can_merge
            kelly_icd.merge_nodes(node_v, node_w)
            kelly_icd_merged_count += 1
          end
        end
      end
    end

    unless only_chain_graphs
      times_bender_icd << Benchmark.measure do
        chain_edges.each do |edge|
          bender_icd.add_edge_with_rollback(edge[0], edge[1])
        end

        edges.each do |edge|
          icd_merged = bender_icd.add_bi_edge_and_merge(edge[0], edge[1])

          if icd_merged
            bender_icd_merged_count += 1
          end
        end
      end
    end

    times_icdc << Benchmark.measure do
      mapped_edges.each do |mapped_edge|
        node_v, node_w = mapped_edge
        can_merge = icdc.can_add_edge?(mapped_edge)

        if can_merge
          icdc.add_edge(mapped_edge)
          icdc_merged_count += 1
        end
      end
    end

    times_multi_icdc << Benchmark.measure do
      mapped_edges.each do |mapped_edge|
        node_v, node_w = mapped_edge
        # t1 = Time.now
        mapped_multi_edge = _normal_edge_to_1_1_edge(mapped_edge)
        can_merge = multi_icdc.can_add_edge?(mapped_multi_edge)

        if can_merge
          multi_icdc.add_edge(mapped_multi_edge)
          multi_icdc_merged_count += 1
        end
        # t2 = Time.now
        # puts "#{t2 - t1}"
      end
    end

  end

  if dfs_icd_merged_count != bender_icd_merged_count ||
     dfs_icd_merged_count != kelly_icd_merged_count ||
     dfs_icd_merged_count != icdc_merged_count ||
     dfs_icd_merged_count != multi_icdc_merged_count
    raise "not all equal"
  end

  puts "merge count:\t #{dfs_icd_merged_count} / #{edges.length}"
  puts "density:\t\t #{dfs_icd_merged_count} / #{num_nodes} = #{dfs_icd_merged_count.to_f / num_nodes.to_f}"

  puts "dfs icd:\t\t #{array_avg(times_dfs_icd.map { |p| p.real })}" if times_dfs_icd.length > 0
  puts "bender icd:\t\t #{array_avg(times_bender_icd.map { |p| p.real })}" if times_bender_icd.length > 0
  puts "topoOrd icd:\t #{array_avg(times_kelly_icd.map { |p| p.real })}" if times_bender_icd.length > 0
  puts "icdc:\t\t\t #{array_avg(times_icdc.map { |p| p.real })}"
  puts "multi icdc:\t\t #{array_avg(times_multi_icdc.map { |p| p.real })}"

end

# num_runs = 1
num_runs = 5

include_graph_edges_in_times = true

puts "--- times including chain edges" if include_graph_edges_in_times
bench_worst_case_graph(5, 100, num_runs, include_graph_edges_in_times, false, true)
bench_worst_case_graph(5, 200, num_runs, include_graph_edges_in_times, false, true)
bench_worst_case_graph(5, 300, num_runs, include_graph_edges_in_times, false, true)
bench_worst_case_graph(5, 400, num_runs, include_graph_edges_in_times, false, true)
bench_worst_case_graph(5, 500, num_runs, include_graph_edges_in_times, false, true)
bench_worst_case_graph(5, 800, num_runs, include_graph_edges_in_times, false, true)
bench_worst_case_graph(5, 1000, num_runs, include_graph_edges_in_times, false, true)

# bench_worst_case_graph(5, 100, num_runs, include_graph_edges_in_times, false, false)
# bench_worst_case_graph(5, 200, num_runs, include_graph_edges_in_times, false, false)
# bench_worst_case_graph(5, 300, num_runs, include_graph_edges_in_times, false, false)
# bench_worst_case_graph(5, 400, num_runs, include_graph_edges_in_times, false, false)
# bench_worst_case_graph(5, 500, num_runs, include_graph_edges_in_times, false, false)
# bench_worst_case_graph(5, 800, num_runs, include_graph_edges_in_times, false, false)
# bench_worst_case_graph(5, 1000, num_runs, include_graph_edges_in_times, false, false)

puts "finished"
