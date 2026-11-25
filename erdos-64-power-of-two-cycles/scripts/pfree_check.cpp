// c++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror scripts/pfree_check.cpp -o /tmp/erdos64-pfree-check
// Independent exhaustive proof search. For each r = 2,...,13, start with an
// induced P_r and forbid an induced P_(r+1). Separately start from a
// dominating induced P14, allowing longer paths. Both searches forbid C4, C8, C16.
// An inconclusive branch or an implementation capacity limit is a failure.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <limits>

using Mask = std::uint64_t;
constexpr int capacity = std::numeric_limits<Mask>::digits;
constexpr int max_order = capacity - 1;

Mask bit(int i) { return Mask(1) << i; }

template<class Action>
bool any_bit(Mask bits, Action action) {
    while (bits) {
        const int i = std::countr_zero(bits);
        if (action(i)) return true;
        bits &= bits - 1;
    }
    return false;
}

struct Board {
    int size;
    std::array<Mask, capacity> neighbors{};
    explicit Board(int r) : size(r) {
        for (int i = 1; i < r; ++i) {
            neighbors[i] |= bit(i - 1);
            neighbors[i - 1] |= bit(i);
        }
    }
    Mask labels() const { return bit(size) - 1; }
    void append(Mask mask) {
        int v = size++;
        neighbors[v] = mask;
        any_bit(mask, [&](int w) { neighbors[w] |= bit(v); return false; });
    }
    void pop() {
        int v = --size;
        any_bit(neighbors[v], [&](int w) { neighbors[w] ^= bit(v); return false; });
    }
};

enum class Seed { longestPath, dominatingPath };

struct Rules {
    Board &board;
    int r;
    Seed seed;
    std::array<Mask, capacity> conflicts{};
    // Used only to choose which low-degree vertex to extend.
    std::array<int, capacity> fewest_options_on_path;
    Rules(Board &b, int length, Seed kind) : board(b), r(length), seed(kind) {
        fewest_options_on_path.fill(30);
    }
    Mask seed_mask() const { return bit(r) - 1; }

    // Two neighbors of the fresh vertex cannot be the ends of an old simple
    // path of 2, 6, or 14 edges. Chords of that path do not matter.
    void simple_paths(int v, Mask used, int length, Mask &ends) {
        if (length == 2 || length == 6 || length == 14) ends |= bit(v);
        if (length == 14 || ends == board.labels()) return;
        any_bit(board.neighbors[v] & ~used, [&](int w) {
            simple_paths(w, used | bit(w), length + 1, ends);
            return false;
        });
    }
    Mask incompatible(int a) {
        if (!conflicts[a]) {
            conflicts[a] = bit(a);
            simple_paths(a, bit(a), 0, conflicts[a]);
        }
        return conflicts[a];
    }

    // At the tip, available excludes used labels and the neighbors of every
    // earlier vertex. A next step is adjacent only to the current tip.
    bool induced_paths(int start, int tip, Mask used, Mask available, int length) {
        Mask next = board.neighbors[tip] & available;
        if (length == r) {
            if (next) return true;
            if (std::popcount(board.neighbors[start]) < 3) {
                const int options = std::popcount(used & ~incompatible(start));
                fewest_options_on_path[start] = std::min(fewest_options_on_path[start], options);
            }
            return false;
        }
        if (length + std::popcount(available) < r) return false;
        return any_bit(next, [&](int w) {
            return induced_paths(start, w, used | bit(w),
                                 available & ~board.neighbors[tip], length + 1);
        });
    }
    bool contains_long_path() {
        return any_bit(board.labels(), [&](int a) {
            return induced_paths(a, a, bit(a), board.labels() ^ bit(a), 1);
        });
    }

    template<class Visit>
    bool all_masks(Mask chosen, Mask available, Visit &visit) {
        if (seed == Seed::dominatingPath && !(seed_mask() & (chosen | available))) return true;
        if (!available) return visit(chosen);
        const int v = std::countr_zero(available);
        const Mask rest = available ^ bit(v);
        return all_masks(chosen, rest, visit) &&
               all_masks(chosen | bit(v), rest & ~incompatible(v), visit);
    }
};

struct Search {
    int r;
    Seed seed;
    std::uint64_t nodes = 0;
    int largest = 0;
    bool certify(Board &b) {
        ++nodes;
        largest = std::max(largest, b.size);
        if (b.size > max_order) {
            std::fprintf(stderr, "Unresolved branch at order %d\n", b.size);
            return false;
        }
        Rules rules(b, r, seed);
        if (seed == Seed::longestPath && rules.contains_long_path()) return true;
        int anchor = -1, best_score = 1000000;
        for (int v = 0; v < b.size; ++v) {
            if (std::popcount(b.neighbors[v]) >= 3) continue;
            const Mask available = b.labels() & ~rules.incompatible(v);
            const int options = std::popcount(available);
            // Each score only chooses which deficient vertex to extend.
            int score;
            if (seed == Seed::dominatingPath) {
                const int on_path = std::popcount(available & rules.seed_mask());
                if (v >= r && on_path == 0) { anchor = v; break; }
                score = 64 * (v < r ? options + 10 : on_path) + options
                        + std::popcount(b.neighbors[v]);
            } else {
                const int support = rules.fewest_options_on_path[v];
                if (support == 0) { anchor = v; break; }
                score = 80 * support + (v < r ? 100 : 0) + 16 * options - v;
            }
            if (score < best_score) { best_score = score; anchor = v; }
        }
        if (anchor < 0) {
            std::fprintf(stderr, "Unresolved minimum-degree-three board\n");
            return false;
        }
        auto visit = [&](Mask m) {
            b.append(m);
            const bool closed = certify(b);
            b.pop();
            return closed;
        };
        return rules.all_masks(bit(anchor), b.labels() & ~rules.incompatible(anchor), visit);
    }
};

bool run(int r, Seed kind) {
    Board board(r);
    Search search{r, kind};
    if (!search.certify(board)) return false;
    const char *name = kind == Seed::longestPath ? "longest" : "dominating";
    std::printf("%s P%d: %llu states, largest order %d\n", name, r,
                static_cast<unsigned long long>(search.nodes), search.largest);
    return true;
}

int main() {
    for (int r = 2; r <= 13; ++r)
        if (!run(r, Seed::longestPath)) return EXIT_FAILURE;
    return run(14, Seed::dominatingPath) ? EXIT_SUCCESS : EXIT_FAILURE;
}
