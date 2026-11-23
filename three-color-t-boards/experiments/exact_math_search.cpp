// Experimental residual-component/subset-length prune.
// Build with c++ -O3 -std=c++20 experiments/exact_math_search.cpp -o /tmp/exact_math_search
// Add -DEXACT_COMPONENT_PRUNE=0 for the instrumented original baseline.
// Run ./splice_search FLAT_PREFIX LIMIT [MODULUS RESIDUES SALT].
// Alternatively pass --after TAIL after LIMIT to resume after a 64-digit tail.
// A zero limit exhausts the selected region. RESIDUES is a comma-separated list.
#include <algorithm>
#include <array>
#include <bit>
#include <charconv>
#include <chrono>
#ifndef EXACT_COMPONENT_PRUNE
#define EXACT_COMPONENT_PRUNE 1
#endif
#ifndef EXACT_COMPONENT_LOOKUP
#define EXACT_COMPONENT_LOOKUP 0
#endif
#ifndef EXACT_COMPONENT_LOOPS_ONLY
#define EXACT_COMPONENT_LOOPS_ONLY 0
#endif
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <string_view>
#include <vector>

namespace {
constexpr int first_open_row = 6;
constexpr int last_row = 9;

struct RowSixSample {
    std::uint32_t modulus = 0, salt = 0;
    std::vector<std::uint32_t> residues;

    bool includes(std::uint32_t word) const {
        std::uint32_t hash = word + salt;
        hash ^= hash >> 16;
        hash *= 0x7feb352du;
        hash ^= hash >> 15;
        hash *= 0x846ca68bu;
        hash ^= hash >> 16;
        return std::binary_search(residues.begin(), residues.end(), hash % modulus);
    }

    bool accepts(const std::array<int, 2 * last_row + 1> &row) const {
        if (modulus == 0) return true;
        std::uint32_t forward = 0, reverse = 0;
        for (int j = 0; j < 13; ++j) {
            forward = 3 * forward + row[j];
            reverse = 3 * reverse + row[12 - j];
        }
        return includes(forward) || includes(reverse);
    }
};

template<typename UInt>
bool read_unsigned(std::string_view text, UInt &value) {
    const char *end = text.data() + text.size();
    auto result = std::from_chars(text.data(), end, value);
    return result.ec == std::errc{} && result.ptr == end;
}

bool read_sample(char **argv, RowSixSample &sample) {
    if (!read_unsigned(argv[3], sample.modulus) || sample.modulus == 0 ||
        !read_unsigned(argv[5], sample.salt)) return false;
    std::string_view terms(argv[4]);
    while (true) {
        auto comma = terms.find(',');
        std::uint32_t value;
        if (!read_unsigned(terms.substr(0, comma), value) || value >= sample.modulus) return false;
        sample.residues.push_back(value);
        if (comma == std::string_view::npos) break;
        terms.remove_prefix(comma + 1);
    }
    std::sort(sample.residues.begin(), sample.residues.end());
    return true;
}

class Search {
public:
    Search(std::uint64_t limit, const RowSixSample &sample, std::string_view after)
        : limit_(limit), sample_(sample), after_(after) {
        available_triples_.fill((1u << 27) - 1);
        // Expand each selected source pair to its three outgoing edges.
        // In reverse, compress each nine-edge slice to its three source bits.
        for (unsigned mask = 0; mask < 512; ++mask) {
            for (unsigned pair = 0; pair < 9; ++pair)
                if (mask & (1u << pair)) expanded_[mask] |= 7u << (3 * pair);
            for (unsigned group = 0; group < 3; ++group)
                if (mask & (7u << (3 * group))) compressed_[mask] |= 1u << group;
        }
#if EXACT_COMPONENT_LOOKUP
        build_connectivity_lookup();
#endif
    }

    void run(std::string_view prefix) {
        for (int row = 0; row < first_open_row; ++row) {
            for (int col = 0; col <= 2 * row; ++col) {
                int color = prefix[row * row + col] - '0';
                rows_[row][col] = color;
                if (--remaining_top_[color] < 0) return;
                if (col >= 2) {
                    int pair = 3 * rows_[row][col - 2] + rows_[row][col - 1];
                    unsigned &choices = available_triples_[rows_[row - 1][col - 2]];
                    unsigned bit = 1u << (3 * pair + color);
                    if (!(choices & bit)) return;
                    choices ^= bit;
                }
            }
            if (row > 0) {
                ++balance_[3 * rows_[row][0] + rows_[row][1]];
                --balance_[3 * rows_[row][2 * row - 1] + rows_[row][2 * row]];
            }
        }
        int excess = 0;
        for (int degree : balance_) excess += std::max(degree, 0);
        start_row<first_open_row>(excess);
    }

    std::uint64_t found() const { return found_; }
    bool limit_reached() const { return limit_ != 0 && found_ == limit_; }

    void print_component_stats() const {
        for (int row = first_open_row; row <= last_row; ++row)
            std::cerr << "component row=" << row << " calls=" << component_calls_[row]
                      << " disconnected=" << component_disconnected_[row]
                      << " pruned=" << component_prunes_[row] << '\n';
    }


private:
    std::array<std::array<int, 2 * last_row + 1>, last_row + 1> rows_{};
    // For each top color, keep one bit for each unused lower triple.
    std::array<unsigned, 3> available_triples_{};
    std::array<unsigned, 512> expanded_{}, compressed_{};
    std::vector<std::array<char, 100>> batch_;
    // All 81 patterns use each top color 27 times. Rows 0 through 8
    // are exactly the cells that appear as tops, each once.
    std::array<int, 3> remaining_top_{27, 27, 27};
    // Project (top, left, middle, right) to the directed edge
    // (left, middle) -> (middle, right). The full edge set is balanced.
    // A horizontal row contributes a path with just two endpoints.
    std::array<int, 9> balance_{};
    std::uint64_t limit_;
    const RowSixSample &sample_;
    std::string_view after_;
    std::uint64_t found_ = 0;
    std::array<std::uint64_t, 10> component_calls_{}, component_disconnected_{}, component_prunes_{};

#if EXACT_COMPONENT_LOOKUP
    std::array<std::array<unsigned, 512>, 3> undirected_chunks_{};
    std::vector<std::uint16_t> connected_vertices_;

    void build_connectivity_lookup() {
        // The 27 directed triples reduce to 21 undirected non-loop edges.
        // A connected-support lookup is 4 MiB. It does not encode the three
        // self-loops, whose possible isolated vertices are checked separately.
        std::array<std::array<int, 9>, 9> indices{};
        for (auto &row : indices) row.fill(-1);
        std::array<unsigned, 27> encoded{};
        std::array<unsigned, 21> endpoints{};
        int count = 0;
        for (int e = 0; e < 27; ++e) {
            int u = e / 3, v = e % 9;
            if (u == v) continue;
            if (u > v) std::swap(u, v);
            if (indices[u][v] < 0) {
                indices[u][v] = count;
                endpoints[count++] = (1u << u) | (1u << v);
            }
            encoded[e] = 1u << indices[u][v];
        }
        if (count != 21) std::abort();
        for (int part = 0; part < 3; ++part)
            for (unsigned bits = 1; bits < 512; ++bits) {
                unsigned bit = bits & -bits;
                undirected_chunks_[part][bits] =
                    undirected_chunks_[part][bits ^ bit] | encoded[9 * part + std::countr_zero(bit)];
            }
        std::array<unsigned, 512> incident{};
        for (unsigned vertices = 1; vertices < 512; ++vertices)
            for (int e = 0; e < 21; ++e)
                if (vertices & endpoints[e]) incident[vertices] |= 1u << e;
        std::array<std::array<unsigned, 2048>, 2> vertex_chunks{};
        for (int part = 0; part < 2; ++part)
            for (unsigned bits = 1; bits < (part ? 1024u : 2048u); ++bits) {
                unsigned bit = bits & -bits;
                vertex_chunks[part][bits] = vertex_chunks[part][bits ^ bit] |
                    endpoints[11 * part + std::countr_zero(bit)];
            }
        auto vertices_of = [&vertex_chunks](unsigned edges) {
            return vertex_chunks[0][edges & 2047u] | vertex_chunks[1][edges >> 11];
        };
        connected_vertices_.resize(1u << 21);
        for (unsigned edges = 1; edges < (1u << 21); ++edges) {
            unsigned active = vertices_of(edges);
            unsigned reached = active & -active;
            while (true) {
                unsigned next = vertices_of(edges & incident[reached]);
                if (next == reached) break;
                reached = next;
            }
            if (reached == active) connected_vertices_[edges] = reached;
        }
    }

    bool connected_lookup(unsigned support) const {
        unsigned edges = undirected_chunks_[0][support & 511u] |
                         undirected_chunks_[1][(support >> 9) & 511u] |
                         undirected_chunks_[2][support >> 18];
        unsigned connected = connected_vertices_[edges];
        unsigned loops = (support & 1u) | ((support >> 9) & 16u) |
                         ((support >> 18) & 256u);
        return connected && !(loops & ~connected);
    }
#endif

    // At a completed-row boundary the remaining distinct pattern edges must
    // split into trails of lengths 2*row-1, 2*row+1, ..., 17. A trail cannot
    // leave a weak component. Components must partition the prescribed lengths.
    bool components_feasible(int row) {
#if !EXACT_COMPONENT_PRUNE
        (void)row;
        return true;
#else
        ++component_calls_[row];
        unsigned support = available_triples_[0] | available_triples_[1] | available_triples_[2];
#if EXACT_COMPONENT_LOOPS_ONLY
        // A remaining aaa loop with no edge to another pair forms a component
        // containing at most three edges. Every remaining row has >=11 edges,
        // so such a component cannot be covered by any remaining row.
        constexpr std::array<unsigned, 3> loop{1u, 1u << 13, 1u << 26};
        constexpr std::array<unsigned, 3> bridge{
            (1u << 1) | (1u << 2) | (1u << 9) | (1u << 18),
            (1u << 12) | (1u << 14) | (1u << 4) | (1u << 22),
            (1u << 24) | (1u << 25) | (1u << 8) | (1u << 17)
        };
        for (int color = 0; color < 3; ++color)
            if ((support & loop[color]) && !(support & bridge[color])) {
                ++component_disconnected_[row];
                ++component_prunes_[row];
                return false;
            }
        return true;
#endif
#if EXACT_COMPONENT_LOOKUP
        if (connected_lookup(support)) return true;
#endif
        auto sources = [this](unsigned edges) {
            return compressed_[edges & 511u] |
                   (compressed_[(edges >> 9) & 511u] << 3) |
                   (compressed_[edges >> 18] << 6);
        };
        unsigned active = sources(support) | ((support | (support >> 9) | (support >> 18)) & 511u);
        if (!active) return row > last_row;
        std::array<unsigned, 9> components{};
        int component_count = 0;
        unsigned unseen = active;
        while (unseen) {
            unsigned reached = unseen & -unseen;
            while (true) {
                unsigned outgoing = support & expanded_[reached];
                unsigned incoming = support & (reached | (reached << 9) | (reached << 18));
                unsigned next = reached | sources(incoming) |
                    ((outgoing | (outgoing >> 9) | (outgoing >> 18)) & 511u);
                if (next == reached) break;
                reached = next;
            }
            if (reached == active) return true;
            components[component_count++] = reached;
            unseen &= ~reached;
        }
        ++component_disconnected_[row];
        const int count = last_row - row + 1;
        const unsigned full = (1u << count) - 1;
        if (component_count > count) {
            ++component_prunes_[row];
            return false;
        }
        std::array<int, 16> sums{}, sizes{};
        for (unsigned mask = 1; mask <= full; ++mask) {
            unsigned bit = mask & -mask;
            int k = std::countr_zero(bit);
            sums[mask] = sums[mask ^ bit] + 2 * (row + k) - 1;
            sizes[mask] = sizes[mask ^ bit] + 1;
        }
        std::array<bool, 16> possible{};
        possible[0] = true;
        for (int c = 0; c < component_count; ++c) {
            unsigned vertices = components[c];
            unsigned mask_edges = expanded_[vertices];
            int edges = 0, minimum_rows = 0;
            for (unsigned available : available_triples_)
                edges += std::popcount(available & mask_edges);
            for (int v = 0; v < 9; ++v)
                if (vertices & (1u << v)) minimum_rows += std::max(-balance_[v], 0);
            minimum_rows = std::max(1, minimum_rows);
            std::array<bool, 16> next{};
            for (unsigned mask = 1; mask <= full; ++mask) {
                if (sums[mask] != edges || sizes[mask] < minimum_rows) continue;
                for (unsigned prior = 0; prior <= full; ++prior)
                    if (possible[prior] && !(prior & mask)) next[prior | mask] = true;
            }
            possible = next;
        }
        if (!possible[full]) ++component_prunes_[row];
        return possible[full];
#endif
    }


    template<int row>
    void start_row(int excess) {
        if constexpr (row != 8) if (!components_feasible(row)) return;
        for (int pair = 0; pair < 9 && !limit_reached(); ++pair) {
            // Having added this start, each positive unit needs a future
            // path end. The current row and all remaining rows provide one each.
            int with_start = excess + (balance_[pair] >= 0);
            if (with_start > last_row - row + 1) continue;
            int left = pair / 3;
            int middle = pair % 3;
            if constexpr (row < last_row) {
                if (remaining_top_[left] == 0 ||
                    remaining_top_[middle] <= int(left == middle)) continue;
                --remaining_top_[left];
                --remaining_top_[middle];
            }
            rows_[row][0] = left;
            rows_[row][1] = middle;
            ++balance_[pair];
            fill_row<row>(2, pair, with_start);
            --balance_[pair];
            if constexpr (row < last_row) {
                ++remaining_top_[left];
                ++remaining_top_[middle];
            }
        }
    }

    template<int row>
    void fill_row(int col, int pair, int excess) {
        int top = rows_[row - 1][col - 2];
        unsigned &available = available_triples_[top];
        unsigned choices = (available >> (3 * pair)) & 7u;
        while (choices && !limit_reached()) {
            int color = std::countr_zero(choices); // ascending color order
            choices &= choices - 1;
            if constexpr (row < last_row) {
                if (remaining_top_[color] == 0) continue;
                --remaining_top_[color];
            }
            unsigned bit = 1u << (3 * pair + color);
            available ^= bit;
            rows_[row][col] = color;
            int next_pair = 3 * (pair % 3) + color;
            if (col < 2 * row) {
                fill_row<row>(col + 1, next_pair, excess);
            } else {
                int with_end = excess - (balance_[next_pair] > 0);
                if (with_end <= last_row - row) {
                    --balance_[next_pair];
                    if constexpr (row == last_row) collect();
                    else if constexpr (row == 7) {
                        finish_row_eight(with_end);
                        flush_batch();
                    } else if constexpr (row == first_open_row) {
                        if (at_or_after_resume_row() && sample_.accepts(rows_[6]))
                            start_row<7>(with_end);
                    } else start_row<row + 1>(with_end);
                    ++balance_[next_pair];
                }
            }
            available |= bit;
            if constexpr (row < last_row) ++remaining_top_[color];
        }
    }

    // Every bit in available_triples_[t] is an edge (l,m) -> (m,r)
    // that can still use top color t. Reachability allows repeated edges,
    // which makes it a necessary condition for a bottom-row completion.
    static constexpr unsigned all_pairs = (1u << 9) - 1;
    static constexpr unsigned repeat_pairs(unsigned pairs) {
        return pairs | (pairs << 9) | (pairs << 18);
    }

    unsigned forward_pairs(unsigned pairs, int top) const {
        unsigned edges = available_triples_[top] & expanded_[pairs];
        return (edges | (edges >> 9) | (edges >> 18)) & all_pairs;
    }

    unsigned backward_pairs(unsigned pairs, int top) const {
        unsigned edges = available_triples_[top] & repeat_pairs(pairs);
        return compressed_[edges & all_pairs] |
               (compressed_[(edges >> 9) & all_pairs] << 3) |
               (compressed_[edges >> 18] << 6);
    }

    unsigned supported_colors(unsigned edges) const {
        unsigned colors = 0;
        for (unsigned top = 0; top < 3; ++top)
            colors |= unsigned((edges & available_triples_[top]) != 0) << top;
        return colors;
    }

    // Fill the gap in row 8 from whichever end has fewer choices. Forward
    // and backward are the possible bottom-row pairs at the two gap edges.
    void fill_gap(int left, int right, int excess, unsigned forward, unsigned backward) {
        const int left_pair = 3 * rows_[8][left - 2] + rows_[8][left - 1];
        const int left_shift = 3 * left_pair;
        unsigned &left_edges = available_triples_[rows_[7][left - 2]];
        if (left > right) {
            if (!(forward & backward)) return;
            // Two windows straddle the split between the completed ends.
            unsigned first = 1u << (left_shift + rows_[8][left]);
            if (!(left_edges & first)) return;
            left_edges ^= first;
            unsigned &middle_edges = available_triples_[rows_[7][left - 1]];
            unsigned second = 1u << (9 * rows_[8][left - 1] +
                                     3 * rows_[8][left] + rows_[8][left + 1]);
            if (middle_edges & second) {
                middle_edges ^= second;
                start_row<9>(excess);
                middle_edges |= second;
            }
            left_edges |= first;
            return;
        }

        unsigned palette = unsigned(remaining_top_[0] > 0) |
                           (unsigned(remaining_top_[1] > 0) << 1) |
                           (unsigned(remaining_top_[2] > 0) << 2);
        unsigned left_choices = (left_edges >> left_shift) & palette;
        if (!left_choices) return;
        const int right_pair = 3 * rows_[8][right + 1] + rows_[8][right + 2];
        unsigned &right_edges = available_triples_[rows_[7][right]];
        unsigned right_options = right_edges >> right_pair;
        // Select bits 0, 9 and 18, one per candidate left color.
        unsigned right_choices = ((right_options & 1u) | ((right_options >> 8) & 2u) |
                         ((right_options >> 16) & 4u)) & palette;
        if (!right_choices) return;

        unsigned forward_edges = expanded_[forward];
        unsigned backward_edges = repeat_pairs(backward);
        left_choices &= supported_colors(forward_edges);
        right_choices &= supported_colors(backward_edges);
        if (!left_choices || !right_choices) return;
        constexpr std::array<int, 8> choice_count{0, 1, 1, 2, 1, 2, 2, 3};
        bool from_left = choice_count[left_choices] <= choice_count[right_choices];
        unsigned choices = from_left ? left_choices : right_choices;
        unsigned &edges = from_left ? left_edges : right_edges;
        while (choices) {
            int color = std::countr_zero(choices);
            choices &= choices - 1;
            unsigned bit = 1u << (from_left ? left_shift + color : 9 * color + right_pair);
            edges ^= bit;
            --remaining_top_[color];
            if (from_left) {
                rows_[8][left] = color;
                unsigned next = forward_pairs(forward, color);
                if (next) fill_gap(left + 1, right, excess, next, backward);
            } else {
                rows_[8][right] = color;
                unsigned next = backward_pairs(backward, color);
                if (next) fill_gap(left, right - 1, excess, forward, next);
            }
            ++remaining_top_[color];
            edges |= bit;
        }
    }

    void finish_row_eight(int excess) {
        if (!components_feasible(8)) return;
        // A balanced prefix permits every endpoint pair. The ordinary
        // left-to-right search avoids iterating over all endpoint combinations.
        if (excess == 0) {
            start_row<8>(excess);
            return;
        }
        for (int start = 0; start < 9; ++start) {
            int with_start = excess + (balance_[start] >= 0);
            if (with_start > 2) continue;
            ++balance_[start];
            for (int end = 0; end < 9; ++end) {
                int with_end = with_start - (balance_[end] > 0);
                if (with_end > 1) continue;
                --balance_[end];
                std::array<int, 4> colors{start / 3, start % 3, end / 3, end % 3};
                for (int color : colors) --remaining_top_[color];
                if (std::min({remaining_top_[0], remaining_top_[1], remaining_top_[2]}) >= 0) {
                    rows_[8][0] = colors[0];
                    rows_[8][1] = colors[1];
                    rows_[8][15] = colors[2];
                    rows_[8][16] = colors[3];
                    // The last row must cancel the residual pair imbalance.
                    unsigned starts = all_pairs, ends = all_pairs;
                    if (with_end) {
                        starts = ends = 0;
                        for (int pair = 0; pair < 9; ++pair) {
                            if (balance_[pair] < 0) starts |= 1u << pair;
                            if (balance_[pair] > 0) ends |= 1u << pair;
                        }
                    }
                    unsigned forward = forward_pairs(forward_pairs(starts, colors[0]), colors[1]);
                    unsigned backward = backward_pairs(backward_pairs(ends, colors[3]), colors[2]);
                    if (forward && backward) fill_gap(2, 14, with_end, forward, backward);
                }
                for (int color : colors) ++remaining_top_[color];
                ++balance_[end];
            }
            --balance_[start];
        }
    }

    bool at_or_after_resume_row() const {
        if (after_.empty()) return true;
        for (int j = 0; j < 13; ++j) {
            int floor = after_[j] - '0';
            if (rows_[6][j] != floor) return rows_[6][j] > floor;
        }
        return true;
    }

    void collect() {
        std::array<char, 100> flat;
        for (int row = 0; row <= last_row; ++row)
            for (int col = 0; col <= 2 * row; ++col)
                flat[row * row + col] = static_cast<char>('0' + rows_[row][col]);
        batch_.push_back(flat);
    }

    // Rows through 7 are already lexicographic. Only the completions of
    // this one prefix can have arrived out of order from the two-ended DFS.
    void flush_batch() {
        if (batch_.empty()) return;
        std::sort(batch_.begin(), batch_.end());
        for (const auto &flat : batch_) {
            if (limit_reached()) break;
            if (!after_.empty()) {
                if (std::string_view(flat.data() + 36, 64) <= after_) continue;
                // Later batches have strictly larger row-six/row-seven prefixes.
                after_ = {};
            }
            std::cout.write(flat.data(), flat.size()).put('\n');
            ++found_;
        }
        batch_.clear();
    }
};
} // namespace

int main(int argc, char **argv) {
    if (argc != 3 && argc != 5 && argc != 6) {
        std::cerr << "Usage: splice_search FLAT_PREFIX LIMIT [--after TAIL | MODULUS RESIDUES SALT]\n";
        return 2;
    }
    std::string_view prefix(argv[1]), limit_text(argv[2]);
    if (prefix.size() != first_open_row * first_open_row ||
        prefix.find_first_not_of("012") != std::string_view::npos) {
        std::cerr << "FLAT_PREFIX must contain 36 ternary digits (rows 0 through 5).\n";
        return 2;
    }
    std::uint64_t limit = 0;
    if (!read_unsigned(limit_text, limit)) {
        std::cerr << "LIMIT must be a nonnegative integer; 0 requests exhaustive search.\n";
        return 2;
    }
    RowSixSample sample;
    if (argc == 6 && !read_sample(argv, sample)) {
        std::cerr << "Expected a positive 32-bit modulus, residues below it, and a 32-bit salt.\n";
        return 2;
    }
    std::string_view after;
    if (argc == 5) {
        after = argv[4];
        if (std::string_view(argv[3]) != "--after" || after.size() != 64 ||
            after.find_first_not_of("012") != std::string_view::npos) {
            std::cerr << "Expected --after followed by a 64-digit ternary tail.\n";
            return 2;
        }
    }
    auto prepare_started = std::chrono::steady_clock::now();
    Search search(limit, sample, after);
    auto started = std::chrono::steady_clock::now();
    search.run(prefix);
    auto elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now() - started).count();
    search.print_component_stats();
    std::cerr << "component_prune=" << EXACT_COMPONENT_PRUNE << " connectivity_lookup=" << EXACT_COMPONENT_LOOKUP
              << " loops_only=" << EXACT_COMPONENT_LOOPS_ONLY << " prepare_seconds=" << std::chrono::duration<double>(started - prepare_started).count()
              << " elapsed_seconds=" << elapsed << "\n";
    if (!std::cout.flush()) {
        std::cerr << "Could not write the boards to standard output.\n";
        return 1;
    }
    std::cerr << search.found() << " boards ("
              << (search.limit_reached() ? "limit reached" :
                  (sample.modulus ? "sample exhausted" : "prefix exhausted")) << ")\n";
}
