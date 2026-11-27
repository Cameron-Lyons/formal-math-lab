// Verify an upper bound for the sixteen-point problem using signed-rank.md.
// Verify rank.weights as in rank-mark.md and the small-set bound as in five-or-more.md.
// Verify the size limit for targets >= 130 with large_members 12 130.
// Build with c++ -O3 -std=c++20 profile_bound.cpp -o profile_bound.
#include <algorithm>
#include <array>
#include <bit>
#include <charconv>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

using Mask = unsigned;
using Bits = std::uint64_t;
constexpr int N = 16;
constexpr Mask Limit = 1u << N;
constexpr int PairDimension = 1 + N * (N - 1) / 2;
std::vector<Mask> sevens, ordered;
std::vector<Mask> extra;
std::array<bool, Limit> ap, is_marked;
std::array<Mask, Limit> covers, conflicts;
std::array<int, Limit> degree;
int goal = 133;

// The separate large-member verifier excludes every member of size 12–16
// from a family of at least 130. This makes each longer row a pure interval.
int maximum_size() { return goal >= 130 ? 11 : N; }

Mask reflect(Mask m) {
    Mask r = 0;
    for (int i = 0; i < N; ++i) r = (r << 1) | ((m >> i) & 1);
    return r;
}

void prepare() {
    for (int first = 0; first < N; ++first) {
        for (int step = 1; step <= N; ++step) {
            Mask p = 0;
            for (int i = first; i < N; i += step) ap[p |= 1u << i] = true;
        }
    }
    for (Mask p = 1; p < Limit; ++p) {
        if (!ap[p]) continue;
        int k = std::popcount(p);
        if (k == 7) sevens.push_back(p);
        bool equality = k == 9 || k == 10 || k == 13;
        if (equality || k == 7 || k == 11 || k == 15 || k == 16)
            extra.push_back(p);
    }
    for (Mask a = 1; a < Limit; ++a) {
        for (unsigned j = 0; j < sevens.size(); ++j) {
            Mask trace = a & sevens[j];
            if (trace == sevens[j]) covers[a] |= 1u << j;
            if (trace && !ap[trace]) conflicts[a] |= 1u << j;
        }
        degree[a] = ap[a];
        if (std::popcount(a) >= 2) ordered.push_back(a);
    }
    // Count subsets with a nonempty progression trace at each A for ordering.
    for (Mask bit = 1; bit < Limit; bit <<= 1)
        for (Mask a = 1; a < Limit; ++a)
            if (a & bit) degree[a] += degree[a ^ bit];
    for (Mask a : ordered) degree[a] <<= N - std::popcount(a);
    std::sort(ordered.begin(), ordered.end(), [](Mask a, Mask b) {
        return std::pair(degree[a], a) > std::pair(degree[b], b);
    });
}

// Each long row either has its own pivot or is an interval of 11-term starts.
class LongRows {
    const std::vector<Mask>& labels;
    std::vector<int> positions;
    std::vector<std::pair<int, int>> edge;
    std::vector<Bits> maximal_cliques;
    Bits units = 0;
    int quota;
    bool usable = true;

    void list_cliques(Bits choices, Bits excluded, Bits chosen,
                      const std::vector<Bits>& adjacent) {
        if (!choices) {
            if (!excluded) maximal_cliques.push_back(chosen);
            return;
        }
        int pivot = 0, largest = -1;
        for (Bits bits = choices | excluded; bits; bits &= bits - 1) {
            int j = std::countr_zero(bits);
            int degree = std::popcount(choices & adjacent[j]);
            if (degree > largest) { pivot = j; largest = degree; }
        }
        for (Bits bits = choices & ~adjacent[pivot]; bits; bits &= bits - 1) {
            int j = std::countr_zero(bits);
            Bits bit = Bits(1) << j;
            choices ^= bit;
            list_cliques(choices & adjacent[j], excluded & adjacent[j], chosen | bit, adjacent);
            excluded |= bit;
        }
    }

    bool enough_rank(Bits pool) const {
        int rank = std::popcount(pool & units);
        std::array<unsigned, 7> component{1, 2, 4, 8, 16, 32, 64};
        for (Bits bits = pool & ~units; rank < quota && bits; bits &= bits - 1) {
            auto [a, b] = edge[std::countr_zero(bits)];
            if (component[a] == component[b]) continue;
            unsigned united = component[a] | component[b];
            for (int i = 0; i <= 6; ++i)
                if (united & (1u << i)) component[i] = united;
            ++rank;
        }
        return rank >= quota;
    }

public:
    LongRows(const std::vector<Mask>& candidates, Mask profile)
        : labels(candidates), quota(goal - PairDimension - std::popcount(profile)) {
        for (int i = 0; i < int(labels.size()); ++i) {
            Mask a = labels[i];
            int k = std::popcount(a);
            bool unit = ap[a] && (k == 9 || k == 10 || k == 13 || k >= 15);
            int first = 6, last = -1;
            for (int start = 0; start < 6; ++start) {
                Mask interval = 2047u << start;
                if ((a & interval) != interval) continue;
                first = std::min(first, start);
                last = start + 1;
            }
            if (unit || last >= 0) {
                if (positions.size() == 63) { usable = false; return; }
                if (unit) units |= Bits(1) << positions.size();
                positions.push_back(i);
                edge.emplace_back(first, last);
            }
        }
    }

    const std::vector<int>& vertices() const { return positions; }

    template<class Alive, class Adjacent>
    void refresh(Alive alive, Adjacent compatible) {
        if (!usable || quota <= 0) return;
        Bits present = 0;
        std::vector<Bits> adjacent(positions.size());
        for (int i = 0; i < int(positions.size()); ++i) {
            int a = positions[i];
            if (alive(a)) present |= Bits(1) << i;
            for (int j = 0; j < int(positions.size()); ++j) {
                if (compatible(a, positions[j])) adjacent[i] |= Bits(1) << j;
            }
        }
        maximal_cliques.clear();
        list_cliques(present, 0, 0, adjacent);
    }

    bool possible(Bits pool) const {
        if (!usable || quota <= 0) return true;
        for (Bits clique : maximal_cliques) {
            if (std::popcount(pool & clique) >= quota && enough_rank(pool & clique))
                return true;
        }
        return false;
    }
};

using Set = std::vector<Bits>;
bool contains(const Set& set, int i) { return (set[i / 64] >> (i % 64)) & 1; }
void insert(Set& set, int i) { set[i / 64] |= Bits(1) << (i % 64); }
void erase(Set& set, int i) { set[i / 64] &= ~(Bits(1) << (i % 64)); }
int population(const Set& set) {
    int total = 0;
    for (Bits word : set) total += std::popcount(word);
    return total;
}

class ProfileGraph {
    std::vector<Mask> labels;
    int n, words;
    std::vector<Set> edges;
    Set alive, smalls, marked;
    std::vector<int> holders;
    std::vector<Set> witness;
    Set marked_holders;
    LongRows long_rows;
    std::vector<bool> long_member;

    int interval_quota;
    std::vector<Bits> nearby_intervals;
    std::unordered_map<Bits, Set> interval_cache;

    void refresh_intervals() {
        interval_cache.clear();
        if (interval_quota <= 0) return;
        const auto& intervals = long_rows.vertices();
        std::fill(nearby_intervals.begin(), nearby_intervals.end(), 0);
        for (int i = 0; i < n; ++i) if (contains(alive, i)) {
            for (int j = 0; j < int(intervals.size()); ++j) {
                int h = intervals[j];
                if (contains(alive, h) && (h == i || contains(edges[i], h)))
                    nearby_intervals[i] |= Bits(1) << j;
            }
        }
    }

    // Every additional clique member must share enough possible intervals with
    // the endpoints, including any intervals equal to the selected vertices.
    void restrict_intervals(Set& candidates, Bits window) {
        if (interval_quota <= 0) return;
        auto [it, first] = interval_cache.try_emplace(window);
        if (first) {
            it->second.resize(words);
            for (int i = 0; i < n; ++i)
                if (std::popcount(nearby_intervals[i] & window) >= interval_quota)
                    insert(it->second, i);
        }
        for (int b = 0; b < words; ++b) candidates[b] &= it->second[b];
    }

    bool color_fits(Set rest, int required) const {
        if (required <= 0) return true;
        int remaining = population(rest);
        if (remaining < required) return false;
        Set available(words);
        for (int color = 1; color < required; ++color) {
            available = rest;
            for (int b = 0; b < words; ++b) {
                while (available[b]) {
                    int k = std::countr_zero(available[b]);
                    int i = 64 * b + k;
                    Bits bit = Bits(1) << k;
                    available[b] ^= bit;
                    rest[b] ^= bit;
                    --remaining;
                    for (int j = b; j < words; ++j) available[j] &= ~edges[i][j];
                }
            }
            if (remaining < required - color) return false;
        }
        return true;
    }

    void delete_edge(int i, int j) { erase(edges[i], j); erase(edges[j], i); }

    // Record the holders which could occur in a completion containing i.
    std::size_t filter_supports() {
        int hwords = marked_holders.size();
        std::vector<Set> compatible(n, Set(hwords));
        std::vector<Bits> compatible_long(n);
        const auto& longer = long_rows.vertices();
        for (int i = 0; i < n; ++i) if (contains(alive, i)) {
            for (int j = 0; j < int(holders.size()); ++j) {
                int h = holders[j];
                if (contains(alive, h) && (h == i || contains(edges[i], h))) insert(compatible[i], j);
            }
            for (int j = 0; j < int(longer.size()); ++j) {
                int h = longer[j];
                if (contains(alive, h) && (h == i || contains(edges[i], h))) compatible_long[i] |= Bits(1) << j;
            }
        }
        std::unordered_map<Bits, bool> long_cache;
        std::size_t removed = 0;
        Set common(hwords);
        for (int i = 0; i < n; ++i) if (contains(alive, i)) {
            for (int j = 0; j < i; ++j) if (contains(alive, j) && contains(edges[i], j)) {
                int num_marked = 0;
                for (int b = 0; b < hwords; ++b) {
                    common[b] = compatible[i][b] & compatible[j][b];
                    num_marked += std::popcount(common[b] & marked_holders[b]);
                }
                bool ok = num_marked >= goal - PairDimension;
                for (const Set& pool : witness) {
                    if (!ok) break;
                    Bits found = 0;
                    for (int b = 0; b < hwords; ++b) found |= common[b] & pool[b];
                    ok = bool(found);
                }
                if (ok) {
                    Bits both = compatible_long[i] & compatible_long[j];
                    auto [it, fresh] = long_cache.try_emplace(both, false);
                    if (fresh) it->second = long_rows.possible(both);
                    ok = it->second;
                }
                if (!ok) { delete_edge(i, j); ++removed; }
            }
        }
        return removed;
    }

    std::size_t filter_colors() {
        std::size_t removed = 0;
        refresh_intervals();
        Set possible(words), restricted(words);
        for (int i = 0; i < n; ++i) if (contains(alive, i)) {
            for (int b = 0; b < words; ++b) possible[b] = alive[b] & edges[i][b];
            restrict_intervals(possible, nearby_intervals[i]);
            if (!color_fits(possible, goal - 1)) { erase(alive, i); ++removed; }
        }
        for (int i = 0; i < n; ++i) if (contains(alive, i)) {
            for (int j = 0; j < i; ++j) {
                if (!contains(alive, j) || !contains(edges[i], j)) continue;
                if (!(long_member[i] || long_member[j] || (covers[labels[i]] && covers[labels[j]])))
                    continue;
                for (int b = 0; b < words; ++b) possible[b] = alive[b] & edges[i][b] & edges[j][b];
                restrict_intervals(possible, nearby_intervals[i] & nearby_intervals[j]);
                auto enough = [&](const Set& group, int minimum) {
                    for (int b = 0; b < words; ++b) restricted[b] = possible[b] & group[b];
                    return color_fits(restricted, minimum - contains(group, i) - contains(group, j));
                };
                if (!enough(marked, goal - PairDimension) || !enough(smalls, goal - 93) ||
                    !color_fits(possible, goal - 2)) {
                    delete_edge(i, j); ++removed;
                }
            }
        }
        return removed;
    }

public:
    ProfileGraph(std::vector<Mask> vertices, Mask profile)
        : labels(std::move(vertices)), n(labels.size()), words((n + 63) / 64),
          edges(n, Set(words)), alive(words), smalls(words), marked(words),
          long_rows(labels, profile), long_member(n),
          interval_quota(maximum_size() <= 11 ? goal - PairDimension - std::popcount(profile) : 0),
          nearby_intervals(n) {
        for (int i = 0; i < n; ++i) {
            insert(alive, i);
            if (std::popcount(labels[i]) <= 4) insert(smalls, i);
            if (is_marked[labels[i]]) insert(marked, i);
            if (covers[labels[i]]) holders.push_back(i);
            for (int j = 0; j < i; ++j) if (ap[labels[i] & labels[j]]) {
                insert(edges[i], j);
                insert(edges[j], i);
            }
        }
        for (int h : long_rows.vertices()) long_member[h] = true;
        int hwords = (holders.size() + 63) / 64;
        marked_holders.resize(hwords);
        for (int i = 0; i < int(holders.size()); ++i)
            if (is_marked[labels[holders[i]]]) insert(marked_holders, i);
        for (Mask bits = profile; bits; bits &= bits - 1) {
            Mask bit = bits & -bits;
            Set pool(hwords);
            for (int i = 0; i < int(holders.size()); ++i)
                if (covers[labels[holders[i]]] & bit) insert(pool, i);
            witness.push_back(std::move(pool));
        }
    }

    bool excludes() {
        for (int phase = 0; phase < 16; ++phase) {
            long_rows.refresh([&](int i) { return contains(alive, i); },
                              [&](int i, int j) { return contains(edges[i], j); });
            std::size_t changed = 0;
            for (int round = 0; round < 3; ++round) {
                auto removed = filter_supports();
                changed += removed;
                if (!removed) break;
            }
            for (int round = 0; round < 4; ++round) {
                auto removed = filter_colors();
                changed += removed;
                if (population(alive) < goal) return true;
                if (!removed) break;
            }
            if (!color_fits(alive, goal)) return true;
            if (!changed) break;
        }
        return false;
    }
};
bool check_profile(Mask profile, int& searched) {
    int dimension = PairDimension;
    for (Mask p : extra) dimension += std::popcount(p) <= maximum_size() && (covers[p] & ~profile) == 0;
    if (dimension < goal) return true;
    ++searched;
    std::vector<Mask> candidates;
    for (Mask a : ordered)
        if (std::popcount(a) <= maximum_size() && !(conflicts[a] & profile) && !(covers[a] & ~profile))
            candidates.push_back(a);
    return ProfileGraph(std::move(candidates), profile).excludes();
}

bool load_marks() {
    std::ifstream input("rank.weights");
    if (!input) return false;
    int mask, weight, marked = 0;
    while (input >> mask) {
        if (!(input >> weight) || mask <= 0 || mask >= int(Limit) || weight < 0) return false;
        if (weight != 0) continue;
        if (is_marked[mask]) return false;
        is_marked[mask] = true;
        ++marked;
    }
    return input.eof() && marked == 363;
}

bool parse_unsigned(std::string_view input, unsigned& result) {
    const char* end = input.data() + input.size();
    auto [position, error] = std::from_chars(input.data(), end, result);
    return error == std::errc{} && position == end;
}

int main(int argc, char** argv) {
    if (argc != 1 && argc != 2 && argc != 4) return 2;
    if (argc >= 2) {
        unsigned upper;
        if (!parse_unsigned(argv[1], upper) || upper < 124 || upper > 163) return 2;
        goal = int(upper) + 1;
    }
    unsigned lo = 0, hi = (1u << 14) - 1;
    if (argc == 4 && (!parse_unsigned(argv[2], lo) || !parse_unsigned(argv[3], hi) ||
                      lo > hi || hi >= (1u << 14))) return 2;
    prepare();
    if (sevens.size() != 14 || extra.size() != 42 || !load_marks()) {
        std::cerr << "Expected the sixteen-point data and rank.weights in the working directory.\n";
        return 2;
    }
    std::array<Mask, 14> reflection;
    for (unsigned i = 0; i < sevens.size(); ++i) {
        auto image = std::find(sevens.begin(), sevens.end(), reflect(sevens[i]));
        if (image == sevens.end()) return 2;
        reflection[i] = 1u << (image - sevens.begin());
    }
    int checked = 0, filtered = 0;
    for (Mask s = lo; s <= hi; ++s) {
        Mask r = 0;
        for (Mask bits = s; bits; bits &= bits - 1) r |= reflection[std::countr_zero(bits)];
        if (r < s) continue;
        if (!check_profile(s, filtered)) {
            std::cerr << "Further work required in profile " << s << "\n";
            return 1;
        }
        ++checked;
    }
    if (argc != 4 && checked != 8256) return 2;
    std::cout << checked << " profiles, " << checked - filtered << " excluded by dimension, "
              << filtered << " excluded by graph pruning. Upper bound " << goal - 1 << ".\n";
}
