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

# from https://stackoverflow.com/questions/15442298/is-sort-in-ruby-stable
module Enumerable
  def stable_sort_by
    sort_by.with_index { |x, idx| [yield(x), idx] }
  end
end

def _get_edge_as_chain_pos(node_to_chain_ranges, edge)
  # e.g. node_to_chain_ranges = [
  #   0..9,
  #   10..19,
  #   20..29,
  # ]

  node_1 = edge[0]
  node_2 = edge[1]
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

  if mapped_edge[0][0] == mapped_edge[1][0]
    raise RuntimeError("same chain")
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

def read_sentences(file_path)
  sentences = []
  File.open(file_path, "r:utf-8") do |file|
    file.each_line do |line|
      sentences << line.strip
    end
  end

  sentences
end

def jaccard_similarity(sentence_i, sentence_j)
  sentence_i_words = sentence_i.split(" ")
  sentence_j_words = sentence_j.split(" ")
  intersection = sentence_i_words & sentence_j_words
  union = sentence_i_words | sentence_j_words
  intersection.length.to_f / union.length
end

def jaccard_similarity_word_indices(sentence_i, sentence_j)
  intersection = sentence_i & sentence_j
  union = sentence_i | sentence_j
  intersection.length.to_f / union.length
end

def calculate_edges_ranked(texts_as_sentences, sim_threshold, min_words_threshold)

  # create pairs of all sentences between two texts
  # prepare for fast similarity calculation
  time_start = Time.now

  all_vocab = Hash.new
  all_vocab_index = 0
  texts_as_sentences.each do |sentences|
    sentences.each do |sentence|
      sentence.split(" ").each do |word|
        if !all_vocab.has_key?(word)
          all_vocab[word] = all_vocab_index
          all_vocab_index += 1
        end
      end
    end
  end

  texts_as_word_indices = Array.new(texts_as_sentences.length) { [] }
  texts_as_sentences.each_with_index do |sentences, i|
    sentences.each do |sentence|
      sent_word_indices = []
      sentence_words = sentence.split(" ")
      if sentence_words.length < min_words_threshold
        texts_as_word_indices[i] << nil
        next
      end

      sentence_words.each do |word|
        sent_word_indices << all_vocab[word]
      end
      texts_as_word_indices[i] << sent_word_indices
    end
  end

  edges = []
  num_texts = texts_as_sentences.length

  num_texts.times do |i|
    ((i + 1)..num_texts - 1).each do |j|
      texts_as_sentences[i].each_with_index do |sentence_i, _i|
        print "\033[0K\r"
        percentage = ((_i + 1).to_f / texts_as_word_indices[i].length * 100).round(2)
        print "calculating similarities #{i}-#{j}: #{percentage}% (#{_i + 1}/#{texts_as_word_indices[i].length})"
        next if texts_as_word_indices[i][_i].nil?

        texts_as_sentences[j].each_with_index do |sentence_j, _j|
          next if texts_as_word_indices[j][_j].nil?

          similarity = jaccard_similarity_word_indices(texts_as_word_indices[i][_i], texts_as_word_indices[j][_j])
          if similarity >= sim_threshold
            # edges << [[i, _i], [j, _j], similarity, sentence_i, sentence_j]
            edges << [[i, _i], [j, _j], similarity]
          end

        end
      end
      puts "\n"
    end
  end

  # edges.sort_by! { |edge| -edge[2] } # not stable
  edges = edges.stable_sort_by { |edge| -edge[2] }

  time_end = Time.now
  puts "Time taken for similarities: #{time_end - time_start} seconds\n"
  edges
end

def bench_align_edges(test_name, input_file_paths, num_runs, sim_threshold, min_words_threshold, only_chain_graphs, check_results)

  texts_as_sentences = []

  was_data_loaded = false

  input_file_paths.each do |input_file_path|
    sentences = read_sentences(input_file_path)
    texts_as_sentences << sentences
  end

  chains = texts_as_sentences.length

  num_nodes = 0
  node_to_chain_ranges = []
  chain_ranges = []
  start_index = 0
  chain_edges = []
  texts_as_sentences.each_with_index do |sentences, chain_index|
    node_to_chain_ranges << Range.new(start_index, start_index + sentences.length - 1)
    chain_ranges << Range.new(0, sentences.length - 1)

    node_to_chain_ranges[node_to_chain_ranges.size - 1].drop(1).each_with_index do |range, i|
      chain_edges << [start_index + i, start_index + i + 1]
    end

    start_index += sentences.length
    num_nodes = start_index

  end

  f_name = "cache/edges_" + test_name + "_" + sim_threshold.to_s + ".json"
  relative_edges = []
  mapped_edges = []
  if File.exist?(f_name)
    File.open(f_name, "r") do |f|
      json_string = f.read
      data = JSON.parse(json_string)
      relative_edges = data["edges"]
    end
    puts "[INFO] loaded edges from cache file: #{f_name}"
  else
    relative_edges = calculate_edges_ranked(texts_as_sentences, sim_threshold, min_words_threshold)
  end

  mapped_edges = relative_edges.map { |e| [e[0], e[1]] }

  real_edges = relative_edges.map do |edge|
    text_1, sent_1 = edge[0]
    text_2, sent_2 = edge[1]

    real_sent_index1 = node_to_chain_ranges[text_1].begin + sent_1
    real_sent_index2 = node_to_chain_ranges[text_2].begin + sent_2
    [real_sent_index1, real_sent_index2]
  end

  if not File.exist?(f_name)
    Dir.mkdir(File.dirname(f_name)) unless Dir.exist?(File.dirname(f_name))
    File.open(f_name, "w") do |f|
      # json_string = JSON.pretty_generate(all_aligner_states)
      data = {
        :meta => {
          :name => test_name,
          :texts => texts_as_sentences.length,
          :lengths => texts_as_sentences.map(&:length),
        },
        :edges => relative_edges,
      }
      json_string = data.to_json
      f.write(json_string)
    end
  end

  puts "--- #{test_name}: ranked edges, chains: #{chains}, edge_count: #{relative_edges.length}, num_runs (avg): #{num_runs}, runtimes in seconds"

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

  dfs_icd_merged_check = []
  kelly_icd_merged_check = []
  bender_icd_merged_check = []
  icdc_merged_check = []
  multi_icdc_merged_check = []

  num_runs.times do |i|

    dfs_icd = create_dfs(num_nodes) unless only_chain_graphs
    kelly_icd = create_kelly_icd(num_nodes)
    bender_icd = create_bender_icd(num_nodes, chain_edges, real_edges) unless only_chain_graphs
    icdc = create_icdc(chain_ranges)
    multi_icdc = create_multi_icdc(chain_ranges)

    dfs_icd_merged_count = 0
    kelly_icd_merged_count = 0
    bender_icd_merged_count = 0
    icdc_merged_count = 0
    multi_icdc_merged_count = 0

    dfs_icd_merged_check = []
    kelly_icd_merged_check = []
    bender_icd_merged_check = []
    icdc_merged_check = []
    multi_icdc_merged_check = []

    unless only_chain_graphs
      times_dfs_icd << Benchmark.measure do

        chain_edges.each do |edge|
          node_v, node_w = edge
          dfs_icd.add_edge(node_v, node_w)
        end

        real_edges.each_with_index do |edge, i|
          node_v, node_w = edge
          can_merge = dfs_icd.can_merge_nodes(node_v, node_w)
          dfs_icd_merged_check << can_merge if check_results

          if can_merge
            dfs_icd.merge_nodes(node_v, node_w)
            dfs_icd_merged_count += 1
          end
        end
      end
    end

    times_icdc << Benchmark.measure do
      mapped_edges.each_with_index do |mapped_edge, i|
        node_v, node_w = mapped_edge

        can_merge = icdc.can_add_edge?(mapped_edge)
        icdc_merged_check << can_merge if check_results

        if can_merge
          icdc.add_edge(mapped_edge)
          icdc_merged_count += 1
        end
      end
    end

    times_multi_icdc << Benchmark.measure do
      mapped_edges.each do |mapped_edge|
        node_v, node_w = mapped_edge
        mapped_multi_edge = _normal_edge_to_1_1_edge(mapped_edge)
        can_merge = multi_icdc.can_add_edge?(mapped_multi_edge)
        multi_icdc_merged_check << can_merge if check_results

        if can_merge
          multi_icdc.add_edge(mapped_multi_edge)
          multi_icdc_merged_count += 1
        end
      end
    end

    unless only_chain_graphs

      times_kelly_icd << Benchmark.measure do

        chain_edges.each do |edge|
          node_v, node_w = edge
          kelly_icd.add_edge(node_v, node_w)
        end

        real_edges.each_with_index do |edge, i|
          node_v, node_w = edge

          can_merge = kelly_icd.can_merge_nodes(node_v, node_w)
          kelly_icd_merged_check << can_merge if check_results

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

        real_edges.each_with_index do |edge, i|
          # puts "#{i}/#{real_edges.size}" if i % 100 == 0
          icd_merged = bender_icd.add_bi_edge_and_merge(edge[0], edge[1])
          bender_icd_merged_check << icd_merged if check_results

          if icd_merged
            bender_icd_merged_count += 1
          end
        end
      end

    end

  end

  if only_chain_graphs
    dfs_icd_merged_count = icdc_merged_check
    if dfs_icd_merged_count != icdc_merged_count ||
       dfs_icd_merged_count != multi_icdc_merged_check
      raise "not all equal (count)"
    end
  else
    if dfs_icd_merged_count != bender_icd_merged_count ||
       dfs_icd_merged_count != icdc_merged_count ||
       dfs_icd_merged_count != multi_icdc_merged_count ||
       dfs_icd_merged_count != kelly_icd_merged_count
      raise "not all equal (count)"
    end
  end

  if only_chain_graphs
    dfs_icd_merged_check = icdc_merged_check
    if check_results
      if dfs_icd_merged_check != icdc_merged_check ||
         dfs_icd_merged_check != multi_icdc_merged_check # ||
        raise "not all equal (different edges)"
      end
    end
  else
    if check_results
      if dfs_icd_merged_check != bender_icd_merged_check ||
         dfs_icd_merged_check != icdc_merged_check ||
         dfs_icd_merged_check != multi_icdc_merged_check ||
         dfs_icd_merged_check != kelly_icd_merged_check
        raise "not all equal (different edges)"
      end
    end
  end

  puts "merge count:\t\t\t #{dfs_icd_merged_count} / #{mapped_edges.length}"
  puts "chain edges:\t\t\t #{chain_edges.length}"
  puts "density:\t\t\t\t #{dfs_icd_merged_count} / #{num_nodes} = #{dfs_icd_merged_count.to_f / num_nodes.to_f}"
  puts "density (with chain):\t #{dfs_icd_merged_count + chain_edges.length} / #{num_nodes} = #{(dfs_icd_merged_count.to_f + chain_edges.length) / num_nodes.to_f}"

  puts "density (with merge):\t #{dfs_icd_merged_count + chain_edges.length} / #{num_nodes - dfs_icd_merged_count} = #{(dfs_icd_merged_count.to_f + chain_edges.length) / (num_nodes.to_f - dfs_icd_merged_count)}"

  puts "dfs icd:\t\t\t\t #{array_avg(times_dfs_icd.map { |p| p.real })}" if times_dfs_icd.length > 0
  puts "bender icd:\t\t\t\t #{array_avg(times_bender_icd.map { |p| p.real })}" if times_bender_icd.length > 0
  puts "topoOrd icd:\t\t\t #{array_avg(times_kelly_icd.map { |p| p.real })}" if times_kelly_icd.length > 0
  puts "icdc:\t\t\t\t\t #{array_avg(times_icdc.map { |p| p.real })}"
  puts "multi icdc:\t\t\t\t #{array_avg(times_multi_icdc.map { |p| p.real })}" if times_multi_icdc.length > 0

end

# num_runs = 1
num_runs = 5

align_benchmark_test_sets = [
  {
    :num_runs => num_runs,
    :name => "nahar",
    :min_words_threshold => 5,
    :sim_threshold => 0.6,
    :files => [
      "benchmark_data/nahar/nahar_1922.sentences",
      "benchmark_data/nahar/nahar_1930.sentences"
    ]
  },
  {
    :num_runs => num_runs,
    :name => "nahar",
    :min_words_threshold => 5,
    :sim_threshold => 0.2,
    :files => [
      "benchmark_data/nahar/nahar_1922.sentences",
      "benchmark_data/nahar/nahar_1930.sentences"
    ]
  },
  {
    :num_runs => num_runs,
    :name => "nahar",
    :min_words_threshold => 5,
    :sim_threshold => 0.1,
    :files => [
      "benchmark_data/nahar/nahar_1922.sentences",
      "benchmark_data/nahar/nahar_1930.sentences"
    ]
  },
  {
    :num_runs => num_runs,
    :name => "rahel",
    :min_words_threshold => 5,
    :sim_threshold => 0.6,
    :files => [
      "benchmark_data/rahel/rahel_0.de.sentences",
      "benchmark_data/rahel/rahel_1.de.sentences",
      "benchmark_data/rahel/rahel_2.de.sentences",
    ]
  },
  {
    :num_runs => num_runs,
    :name => "rahel",
    :min_words_threshold => 5,
    :sim_threshold => 0.2,
    :files => [
      "benchmark_data/rahel/rahel_0.de.sentences",
      "benchmark_data/rahel/rahel_1.de.sentences",
      "benchmark_data/rahel/rahel_2.de.sentences",
    ]
  },
  {
    :num_runs => num_runs,
    :name => "rahel",
    :min_words_threshold => 5,
    :sim_threshold => 0.1,
    :only_chain_graphs => false,
    :files => [
      "benchmark_data/rahel/rahel_0.de.sentences",
      "benchmark_data/rahel/rahel_1.de.sentences",
      "benchmark_data/rahel/rahel_2.de.sentences",
    ]
  },
  {
    :num_runs => num_runs,
    :name => "heinrich",
    :min_words_threshold => 5,
    :sim_threshold => 0.6,
    :files => [
      "benchmark_data/heinrich/derGrüneHeinrich_1855_data.sentences",
      "benchmark_data/heinrich/derGrüneHeinrich_1879_data.sentences"
    ]
  },
  {
    :num_runs => num_runs,
    :name => "heinrich",
    :min_words_threshold => 5,
    :sim_threshold => 0.2,
    :only_chain_graphs => false,
    :files => [
      "benchmark_data/heinrich/derGrüneHeinrich_1855_data.sentences",
      "benchmark_data/heinrich/derGrüneHeinrich_1879_data.sentences"
    ]
  },
  #### makes no sens, because >> 30 min for dfs & icd
  {
    :num_runs => num_runs,
    :name => "heinrich",
    :min_words_threshold => 5, # 4440 / 5952, 160s / 87s
    :sim_threshold => 0.1,
    :only_chain_graphs => false,
    :files => [
      "benchmark_data/heinrich/derGrüneHeinrich_1855_data.sentences",
      "benchmark_data/heinrich/derGrüneHeinrich_1879_data.sentences"
    ]
  },
]

check_results = true
# check_results = false

# align_benchmark_test_sets_chain_only.each_with_index do |test_set, index|
align_benchmark_test_sets.each_with_index do |test_set, index|
  puts "\n\n"
  puts "--- times including chain edges"
  puts "--- test set #{index + 1}, name: #{test_set[:name]}, sim_threshold: #{test_set[:sim_threshold]}, min_words_threshold: #{test_set[:min_words_threshold]} ---"
  only_chain_graphs = test_set[:only_chain_graphs] || false
  bench_align_edges(test_set[:name], test_set[:files], test_set[:num_runs], test_set[:sim_threshold], test_set[:min_words_threshold], only_chain_graphs, check_results)
  GC.start
end


