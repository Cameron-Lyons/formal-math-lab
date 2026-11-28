// Six-color completions of an ordered 10-position cube on [74] minus 25,30,35.
// After fixing the cube exactly 61 positions remain, all represented by one mask.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <stdexcept>
#include <string>
#include <vector>
namespace {
constexpr int span = 74, total = 71, free_n = 61, K = 6;
using M = std::uint64_t;
using Small = std::uint8_t;
using Edge = std::array<int, 4>;
struct Pair {
    Small a, b;
};
struct Pairs {
    Small n = 0;
    std::array<Pair, 6> entries{};
};
M bit(int x) {
    return M{1} << x;
}
int first(M m) {
    return std::countr_zero(m);
}
struct State {
    M open = bit(free_n) - 1, forced = 0;
    std::array<M, K> classes{};
    std::array<M, free_n> unequal{};
    std::array<Small, free_n> domain{};
    std::array<Small, total> val{};
    int used = 0;
};
struct Change {
    Small x, mask;
};
struct Reactions {
    std::vector<Change> changes;
    std::vector<Pair> links;
};
struct Search {
    std::array<int, span> index;
    std::array<int, total> original{};
    std::array<int, free_n> degree{}, order{};
    std::vector<Edge> edges;
    std::array<M, free_n> neighbors{};
    std::array<std::array<Pairs, total>, free_n> pairs{};
    std::array<std::array<Reactions, K>, free_n> reactions;
    std::array<Small, total> result{};
    std::uint64_t nodes = 0;
    Search() {
        index.fill(-1);
        int next = 0;
        for (int x = 0; x < span; ++x)
            if (x != 24 && x != 29 && x != 34 && (x < 38 || x >= 48)) {
                index[x] = next;
                original[next++] = x;
            }
        if (next != free_n)
            throw std::logic_error("free count");
        for (int x = 38; x < 48; ++x) {
            index[x] = next;
            original[next++] = x;
        }
        for (int d = 1; 3 * d < span; ++d)
            for (int x = 0; x + 3 * d < span; ++x) {
                Edge e{};
                for (int t = 0; t < 4; ++t)
                    e[t] = index[x + t * d];
                if (std::find(e.begin(), e.end(), -1) != e.end())
                    continue;
                edges.push_back(e);
                for (int v : e)
                    if (v < free_n) {
                        ++degree[v];
                        for (int w : e)
                            if (w != v) {
                                Pair rem{};
                                int j = 0;
                                for (int z : e)
                                    if (z != v && z != w) {
                                        if (!j++)
                                            rem.a = z;
                                        else
                                            rem.b = z;
                                    }
                                auto &list = pairs[v][w];
                                if (list.n == list.entries.size())
                                    throw std::logic_error("pair incidence");
                                list.entries[list.n++] = rem;
                                if (w < free_n)
                                    neighbors[v] |= bit(w);
                            }
                    }
            }
        for (int i = 0; i < free_n; ++i)
            order[i] = i;
        std::stable_sort(order.begin(), order.end(),
                         [&](int a, int b) { return degree[a] > degree[b]; });
    }
    bool remove(State &s, int x, unsigned disallowed) const {
        unsigned domain = (s.domain[x] &= ~disallowed);
        if (!domain)
            return false;
        if (std::has_single_bit(domain))
            s.forced |= bit(x);
        return true;
    }
    // A pair already has color c. Its two other AP points must have two
    // different colors other than c. Fixed points have a permanent s.val.
    bool constrain(State &s, int c, int a, int b) const {
        int ca = s.val[a], cb = s.val[b];
        if (ca == c || cb == c || (ca < K && ca == cb))
            return false;
        if (ca == K && !remove(s, a, (1u << c) | (cb < K ? 1u << cb : 0)))
            return false;
        if (cb == K && !remove(s, b, (1u << c) | (ca < K ? 1u << ca : 0)))
            return false;
        if (ca == K && cb == K) {
            s.unequal[a] |= bit(b);
            s.unequal[b] |= bit(a);
        }
        return true;
    }
    bool prepare(State &s, const char *word) {
        s.val.fill(K);
        s.domain.fill((1u << K) - 1);
        for (int x = 0; x < span; ++x) {
            bool fixed = x >= 38 && x < 48;
            if (!fixed) {
                if (word[x] != '.')
                    throw std::invalid_argument("unexpected fixed position");
                continue;
            }
            int c = word[x] - '0';
            if (c < 0 || c >= K)
                throw std::invalid_argument("invalid fixed color");
            s.val[index[x]] = c;
            s.used = std::max(s.used, c + 1);
        }
        for (auto e : edges)
            for (int i = 0; i < 4; ++i)
                for (int j = 0; j < i; ++j) {
                    int x = e[i], y = e[j];
                    if (x < free_n || y < free_n || s.val[x] != s.val[y])
                        continue;
                    Pair r{};
                    int t = 0;
                    for (int z : e)
                        if (z != x && z != y) {
                            if (!t++)
                                r.a = z;
                            else
                                r.b = z;
                        }
                    if (!constrain(s, s.val[x], r.a, r.b))
                        return false;
                }
        // Compile the consequences of assigning x the same color c as one or
        // more fixed cube positions. Do this once per (x,c), outside the search.
        for (int x = 0; x < free_n; ++x)
            for (int c = 0; c < K; ++c) {
                auto &r = reactions[x][c];
                r.changes.clear();
                r.links.clear();
                std::array<unsigned, free_n> masks{};
                bool legal = true;
                for (int y = free_n; y < total; ++y)
                    if (s.val[y] == c) {
                        const auto &list = pairs[x][y];
                        for (int j = 0; j < list.n; ++j) {
                            auto [a, b] = list.entries[j];
                            int ca = s.val[a], cb = s.val[b];
                            if (ca == c || cb == c || (ca < K && ca == cb)) {
                                legal = false;
                                continue;
                            }
                            if (ca == K)
                                masks[a] |= (1u << c) | (cb < K ? 1u << cb : 0);
                            if (cb == K)
                                masks[b] |= (1u << c) | (ca < K ? 1u << ca : 0);
                            if (ca == K && cb == K)
                                r.links.push_back({a, b});
                        }
                    }
                if (!legal) {
                    if (!remove(s, x, 1u << c))
                        return false;
                    continue;
                }
                for (int v = 0; v < free_n; ++v)
                    if (masks[v])
                        r.changes.push_back({Small(v), Small(masks[v])});
            }
        return true;
    }
    bool assign(State &s, int x, int c) const {
        for (M m = s.unequal[x] & s.open; m; m &= m - 1)
            if (!remove(s, first(m), 1u << c))
                return false;
        const auto &r = reactions[x][c];
        for (auto [v, mask] : r.changes) {
            if (s.val[v] == K) {
                if (!remove(s, v, mask))
                    return false;
            } else if (mask & (1u << s.val[v]))
                return false;
        }
        for (auto [a, b] : r.links) {
            int ca = s.val[a], cb = s.val[b];
            if (ca == K && cb == K) {
                s.unequal[a] |= bit(b);
                s.unequal[b] |= bit(a);
            } else if (ca == K) {
                if (!remove(s, a, 1u << cb))
                    return false;
            } else if (cb == K) {
                if (!remove(s, b, 1u << ca))
                    return false;
            } else if (ca == cb)
                return false;
        }
        for (M m = s.classes[c] & neighbors[x]; m; m &= m - 1) {
            const auto &list = pairs[x][first(m)];
            for (int j = 0; j < list.n; ++j) {
                auto [a, b] = list.entries[j];
                if (!constrain(s, c, a, b))
                    return false;
            }
        }
        s.open &= ~bit(x);
        s.forced &= ~bit(x);
        s.classes[c] |= bit(x);
        s.val[x] = c;
        s.used = std::max(s.used, c + 1);
        return true;
    }
    bool search(State &s) {
        ++nodes;
        while (s.forced) {
            int x = first(s.forced);
            if (!assign(s, x, std::countr_zero(s.domain[x])))
                return false;
        }
        if (!s.open) {
            result = s.val;
            return true;
        }
        int best = -100000, x = -1;
        for (int j : order)
            if (s.open & bit(j)) {
                int score = -1000 * std::popcount(s.domain[j]) +
                            5 * std::popcount(s.unequal[j] & s.open) + degree[j];
                if (score > best) {
                    best = score;
                    x = j;
                }
            }
        unsigned names = (1u << std::min(K, s.used + 1)) - 1;
        for (unsigned dom = s.domain[x] & names; dom; dom &= dom - 1) {
            State t = s;
            if (assign(t, x, std::countr_zero(dom)) && search(t))
                return true;
        }
        return false;
    }
};
} // namespace
int main() {
    Search problem;
    int offset;
    char word[80];
    while (std::scanf("%d %74s", &offset, word) == 2) {
        if (offset != 0 || std::string(word).size() != span)
            return 2;
        State s{};
        problem.nodes = 0;
        bool ok = problem.prepare(s, word) && problem.search(s);
        std::printf("%s %llu 0 %s", ok ? "SAT" : "UNSAT",
                    (unsigned long long)std::max<std::uint64_t>(problem.nodes, 1), word);
        if (ok) {
            for (auto e : problem.edges) {
                unsigned mask = 0;
                for (int x : e)
                    mask |= 1u << problem.result[x];
                if (std::popcount(mask) < 3)
                    throw std::logic_error("invalid positive");
            }
            std::printf(" ");
            for (int x = 0; x < span; ++x)
                std::putchar(problem.index[x] < 0 ? '*' : '0' + problem.result[problem.index[x]]);
        }
        std::puts("");
        std::fflush(stdout);
    }
}
