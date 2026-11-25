// Derived experimental copy of splice_search.cpp; only final-row enumeration
// is replaced by reusable prescribed-label Euler-trail counting.
// Build with c++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror splice_search.cpp -o splice_search
// Run ./splice_search FLAT_PREFIX LIMIT [MODULUS RESIDUES SALT].
// Alternatively pass --after TAIL after LIMIT to resume after a 64-digit tail.
// A zero limit exhausts the selected region. RESIDUES is a comma-separated list.
#include "exact_lastrow.hpp"
#include <chrono>
#include <ctime>
#include <limits>
#include <algorithm>
#include <array>
#include <bit>
#include <charconv>
#include <cstdint>
#include <iostream>
#include <string_view>
#include <vector>

namespace {
int memo_depth=0;
size_t memo_capacity=0;
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

[[maybe_unused]] bool read_sample(char **argv, RowSixSample &sample) {
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
    LastRow terminal{3,memo_depth,memo_capacity};
    double terminal_cpu=0;
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

    template<int row>
    void start_row(int excess) {
        if constexpr(row==last_row){
            unsigned starts=0;
            for(int pair=0;pair<9;++pair)if(excess+(balance_[pair]>=0)<=1)starts|=1u<<pair;
            auto terminal_start=std::clock();
            auto amount=terminal.count(rows_[8].data(),17,available_triples_,starts);
            terminal_cpu+=double(std::clock()-terminal_start)/CLOCKS_PER_SEC;
            if(amount>std::numeric_limits<std::uint64_t>::max()-found_)throw std::overflow_error("count overflow");
            found_+=amount;
            return;
        }
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

int main(int argc,char**argv){try{
 if(argc!=4){std::cerr<<"Usage: exact_lastrow_search PREFIX MEMO_DEPTH MEMO_CAPACITY\n";return 2;}
 std::string_view prefix(argv[1]);if(prefix.size()!=36||prefix.find_first_not_of("012")!=std::string_view::npos)return 2;
 memo_depth=std::stoi(argv[2]);memo_capacity=std::stoull(argv[3]);
 RowSixSample sample;Search search(0,sample,{});auto start=std::chrono::steady_clock::now();auto cpu_start=std::clock();search.run(prefix);
 std::cout<<"status=COMPLETE count="<<search.found()<<" memo_depth="<<memo_depth<<" memo_capacity="<<memo_capacity<<" entries="<<search.terminal.entries()<<" requests="<<search.terminal.requests<<" cpu_seconds="<<double(std::clock()-cpu_start)/CLOCKS_PER_SEC<<" terminal_cpu_seconds="<<search.terminal_cpu<<" elapsed="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<'\n';
 for(int d=0;d<=17;++d)if(search.terminal.calls[d])std::cout<<"remaining="<<d<<" calls="<<search.terminal.calls[d]<<" lookups="<<search.terminal.lookups[d]<<" hits="<<search.terminal.hits[d]<<'\n';
}catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 2;}}
