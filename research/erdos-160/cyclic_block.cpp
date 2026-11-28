// Seven-color interval words containing a contiguous, cyclically valid 23-block.
// c++ -std=c++20 -O3 -march=native cyclic_block.cpp -o cyclic_block
// ./cyclic_block [23|73|74]    With no argument, run all three searches.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>

namespace {
constexpr int p = 23, colors = 7, max_length = 74;
using Small = std::uint32_t;
using Mask = __uint128_t;
using AffineMap = std::array<int, p>;
constexpr Small cycle = (Small{1} << p) - 1;
Small small_bit(int i) {
    return Small{1} << i;
}
Mask bit(int i) {
    return Mask{1} << i;
}
int first(Mask m) {
    auto lo = static_cast<std::uint64_t>(m);
    return lo ? std::countr_zero(lo) : 64 + std::countr_zero(static_cast<std::uint64_t>(m >> 64));
}
int count(Mask m) {
    return std::popcount(static_cast<std::uint64_t>(m)) +
           std::popcount(static_cast<std::uint64_t>(m >> 64));
}
std::string normalize(std::string w) {
    std::array<char, colors> name{};
    char next = '0';
    for (char &c : w) {
        char &label = name[c - '0'];
        if (!label)
            label = next++;
        c = label;
    }
    return w;
}
std::string canonical_interval(std::string w) {
    std::string forward = normalize(w);
    std::reverse(w.begin(), w.end());
    return std::min(forward, normalize(w));
}
bool valid_four(char a, char b, char c, char d) {
    return (a == b) + (a == c) + (a == d) + (b == c) + (b == d) + (c == d) <= 1;
}
bool valid_interval(const std::string &w) {
    for (int d = 1; 3 * d < int(w.size()); ++d)
        for (int i = 0; i + 3 * d < int(w.size()); ++i)
            if (!valid_four(w[i], w[i + d], w[i + 2 * d], w[i + 3 * d]))
                return false;
    return true;
}
bool valid_cycle(const std::string &w) {
    if (w.size() != p)
        return false;
    for (int i = 0; i < p; ++i)
        for (int d = 1; d < p; ++d)
            if (!valid_four(w[i], w[(i + d) % p], w[(i + 2 * d) % p], w[(i + 3 * d) % p]))
                return false;
    return true;
}

// Enumerate partitions of Z/23 into seven disjoint nonempty classes. A single
// class may contain at most two points of each cyclic AP, and two classes together
// may contain at most three. These are necessary and sufficient conditions.
struct CyclicCensus {
    std::vector<AffineMap> affine;
    std::set<Small> edges;
    std::array<std::array<Small, p>, p> third{};
    std::vector<Small> support;
    std::vector<std::vector<bool>> compatible;
    std::set<std::string> representatives;
    std::vector<int> selected;

    CyclicCensus() {
        for (int a = 0; a < p; ++a)
            for (int d = 1; d < p; ++d) {
                Small e = 0;
                AffineMap map{};
                for (int j = 0; j < p; ++j)
                    map[j] = (a + j * d) % p;
                for (int j = 0; j < 4; ++j)
                    e |= small_bit(map[j]);
                edges.insert(e);
                affine.push_back(map);
            }
        for (Small e : edges)
            for (Small a = e; a; a &= a - 1)
                for (Small b = a & (a - 1); b; b &= b - 1) {
                    int i = std::countr_zero(a), j = std::countr_zero(b);
                    third[i][j] |= e & ~small_bit(i) & ~small_bit(j);
                    third[j][i] = third[i][j];
                }
        generate(0, cycle);
        std::sort(support.begin(), support.end());
        compatible.assign(support.size(), std::vector<bool>(support.size()));
        for (std::size_t i = 0; i < support.size(); ++i) {
            std::vector<Small> forbidden;
            for (Small e : edges)
                if (std::popcount(e & ~support[i]) == 2)
                    forbidden.push_back(e & ~support[i]);
            for (std::size_t j = i + 1; j < support.size(); ++j)
                if (!(support[i] & support[j])) {
                    bool ok = std::none_of(forbidden.begin(), forbidden.end(),
                                           [&](Small pair) { return !(pair & ~support[j]); });
                    compatible[i][j] = compatible[j][i] = ok;
                }
        }
    }
    void generate(Small set, Small available) {
        if (set)
            support.push_back(set);
        while (available) {
            int x = std::countr_zero(available);
            available &= available - 1;
            Small next = available;
            for (Small a = set; a; a &= a - 1)
                next &= ~third[std::countr_zero(a)][x];
            generate(set | small_bit(x), next);
        }
    }
    std::set<std::string> images(const std::string &w) const {
        std::set<std::string> result;
        for (const auto &map : affine) {
            std::string image;
            for (int i : map)
                image.push_back(w[i]);
            result.insert(normalize(image));
        }
        return result;
    }
    void search(Small left, const std::vector<int> &available, int largest) {
        int slots = colors - int(selected.size()), points = std::popcount(left);
        if (!slots) {
            if (left)
                return;
            std::string word(p, '?');
            for (int c = 0; c < colors; ++c)
                for (Small m = support[selected[c]]; m; m &= m - 1)
                    word[std::countr_zero(m)] = char('0' + c);
            if (!valid_cycle(word))
                throw std::logic_error("invalid cyclic witness");
            representatives.insert(*images(word).begin());
            return;
        }
        if (points < slots || points > slots * largest)
            return;
        int lo = std::max(1, points - (slots - 1) * largest), hi = points - (slots - 1);
        std::array<int, p> freq{};
        for (int id : available) {
            int n = std::popcount(support[id]);
            if (n < lo || n > hi)
                continue;
            for (Small m = support[id]; m; m &= m - 1)
                ++freq[std::countr_zero(m)];
        }
        int x = std::countr_zero(left);
        for (Small m = left; m; m &= m - 1)
            if (freq[std::countr_zero(m)] < freq[x])
                x = std::countr_zero(m);
        for (int id : available) {
            Small set = support[id];
            int n = std::popcount(set);
            if (!(set & small_bit(x)) || n < lo || n > hi)
                continue;
            std::vector<int> next;
            for (int other : available)
                if (compatible[id][other])
                    next.push_back(other);
            selected.push_back(id);
            search(left ^ set, next, largest);
            selected.pop_back();
        }
    }
    std::set<std::string> run() {
        // Choose a largest class. An affine coordinate change sends its mask to
        // the smallest member of its orbit. Ties can duplicate a solution.
        for (int i = 0; i < int(support.size()); ++i) {
            Small s = support[i];
            int largest = std::popcount(s);
            if (largest * colors < p)
                continue;
            bool least = true;
            for (const auto &map : affine) {
                Small image = 0;
                for (Small m = s; m; m &= m - 1)
                    image |= small_bit(map[std::countr_zero(m)]);
                if (image < s) {
                    least = false;
                    break;
                }
            }
            if (!least)
                continue;
            std::vector<int> options;
            for (int j = 0; j < int(support.size()); ++j)
                if (compatible[i][j] && std::popcount(support[j]) <= largest)
                    options.push_back(j);
            selected = {i};
            search(cycle ^ s, options, largest);
        }
        std::set<std::string> patterns;
        for (const auto &w : representatives) {
            auto expanded = images(w);
            patterns.insert(expanded.begin(), expanded.end());
        }
        std::printf("Z/23: %zu supports, %zu affine/color orbits, %zu ordered patterns.\n",
                    support.size(), representatives.size(), patterns.size());
        for (const auto &w : representatives)
            std::puts(w.c_str());
        return patterns;
    }
};

// Once two vertices of an interval AP receive the same color, its other two
// vertices must differ from that color and from each other. Propagate those
// requirements, then try all remaining colors of the smallest-domain vertex.
struct IntervalCensus {
    struct State {
        Mask open{}, singletons{};
        std::array<Mask, colors> classes{};
        std::array<Mask, max_length> unequal{};
        std::array<unsigned char, max_length> domain{}, value{};
    };
    using Pair = std::array<int, 2>;
    int n;
    std::array<std::array<std::vector<Pair>, max_length>, max_length> other;
    std::array<Mask, max_length> neighbor{};
    std::array<int, max_length> degree{}, order{};
    std::set<std::string> solutions;
    std::uint64_t hits = 0, nodes = 0;

    explicit IntervalCensus(int length) : n(length) {
        for (int d = 1; 3 * d < n; ++d)
            for (int i = 0; i + 3 * d < n; ++i) {
                std::array<int, 4> e{i, i + d, i + 2 * d, i + 3 * d};
                for (int x : e)
                    ++degree[x];
                for (int x : e)
                    for (int y : e)
                        if (x != y) {
                            Pair rest{};
                            int j = 0;
                            for (int z : e)
                                if (z != x && z != y)
                                    rest[j++] = z;
                            other[x][y].push_back(rest);
                            neighbor[x] |= bit(y);
                        }
            }
        for (int i = 0; i < n; ++i)
            order[i] = i;
        std::stable_sort(order.begin(), order.begin() + n,
                         [&](int a, int b) { return degree[a] > degree[b]; });
    }
    bool remove(State &s, int x, unsigned forbidden) const {
        unsigned dom = (s.domain[x] &= ~forbidden);
        if (!dom)
            return false;
        if (std::has_single_bit(dom))
            s.singletons |= bit(x);
        return true;
    }
    bool assign(State &s, int x, int c) const {
        unsigned color_bit = 1u << c;
        for (Mask m = s.unequal[x] & s.open; m; m &= m - 1)
            if (!remove(s, first(m), color_bit))
                return false;
        for (Mask m = s.classes[c] & neighbor[x]; m; m &= m - 1)
            for (auto [a, b] : other[x][first(m)]) {
                int ca = s.value[a], cb = s.value[b];
                if (ca == c || cb == c || (ca < colors && ca == cb))
                    return false;
                if (ca == colors && !remove(s, a, color_bit | (cb < colors ? 1u << cb : 0)))
                    return false;
                if (cb == colors && !remove(s, b, color_bit | (ca < colors ? 1u << ca : 0)))
                    return false;
                if (ca == colors && cb == colors) {
                    s.unequal[a] |= bit(b);
                    s.unequal[b] |= bit(a);
                }
            }
        s.open &= ~bit(x);
        s.singletons &= ~bit(x);
        s.classes[c] |= bit(x);
        s.value[x] = c;
        return true;
    }
    void search(State &s) {
        ++nodes;
        while (s.singletons) {
            int x = first(s.singletons), c = std::countr_zero(s.domain[x]);
            if (!assign(s, x, c))
                return;
        }
        if (!s.open) {
            std::string w;
            for (int i = 0; i < n; ++i)
                w.push_back(char('0' + s.value[i]));
            if (!valid_interval(w))
                throw std::logic_error("invalid interval witness");
            solutions.insert(canonical_interval(w));
            ++hits;
            return;
        }
        int x = -1, best = -100000;
        for (int j = 0; j < n; ++j) {
            int i = order[j];
            if (!(s.open & bit(i)))
                continue;
            int rank =
                -1000 * std::popcount(s.domain[i]) + 5 * count(s.unequal[i] & s.open) + degree[i];
            if (rank > best) {
                x = i;
                best = rank;
            }
        }
        for (unsigned m = s.domain[x]; m; m &= m - 1) {
            State t = s;
            if (assign(t, x, std::countr_zero(m)))
                search(t);
        }
    }
    void run(const std::set<std::string> &patterns) {
        std::uint64_t cases = 0, viable = 0;
        // Reflecting the whole interval sends offset j to n-p-j, and reverses
        // the block. The family of patterns includes the reversal of each one.
        for (int offset = 0; 2 * offset <= n - p; ++offset)
            for (const auto &pattern : patterns) {
                State s{};
                s.open = bit(n) - 1;
                s.domain.fill((1u << colors) - 1);
                s.value.fill(colors);
                for (int j = 0; j < p; ++j) {
                    s.domain[offset + j] = 1u << (pattern[j] - '0');
                    s.singletons |= bit(offset + j);
                }
                auto before = hits;
                search(s);
                ++cases;
                if (before != hits)
                    ++viable;
            }
        std::printf("N=%d: %llu placements, %llu feasible, %llu model hits, %zu interval orbits, "
                    "%llu nodes.\n",
                    n, static_cast<unsigned long long>(cases),
                    static_cast<unsigned long long>(viable), static_cast<unsigned long long>(hits),
                    solutions.size(), static_cast<unsigned long long>(nodes));
        if (!solutions.empty())
            std::puts(solutions.begin()->c_str());
    }
};
} // namespace

int main(int argc, char **argv) {
    int which = argc > 1 ? std::atoi(argv[1]) : 0;
    if (argc > 2 || (which != 0 && which != 23 && which != 73 && which != 74))
        return 2;
    CyclicCensus cycle_search;
    auto patterns = cycle_search.run();
    if (patterns.size() != 506 || cycle_search.representatives.size() != 1)
        return 1;
    // A cyclic solution using fewer colors could be refined to exactly seven.
    // The last split could then be undone in the resulting seven-color word.
    for (const auto &w : cycle_search.representatives)
        for (int a = 0; a < colors; ++a)
            for (int b = 0; b < a; ++b) {
                auto merged = w;
                std::replace(merged.begin(), merged.end(), char('0' + a), char('0' + b));
                if (valid_cycle(merged))
                    return 1;
            }
    const std::string witness =
        "0012231004541233156162564042350045412311561625630423500454123105616252146";
    bool has_block = false;
    for (std::size_t i = 0; i + p <= witness.size(); ++i)
        if (valid_cycle(witness.substr(i, p)))
            has_block = true;
    if (witness.size() != 73 || !valid_interval(witness) || !has_block)
        return 1;
    for (int n : {73, 74})
        if (!which || which == n) {
            IntervalCensus search(n);
            search.run(patterns);
            if ((n == 73 && search.solutions.size() != 76) ||
                (n == 74 && !search.solutions.empty()))
                return 1;
        }
}
