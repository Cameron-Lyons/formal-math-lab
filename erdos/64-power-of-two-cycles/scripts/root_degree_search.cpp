// Exhaust rooted graphs of minimum degree at least three up to an order bound.
// Compile with -DUSE_NAUTY and link nauty.a to cache isomorphic boards.
#include <algorithm>
#include <array>
#include <bit>
#include <charconv>
#include <cstdint>
#include <cstdio>
#include <string_view>
#ifdef USE_NAUTY
#include "nauty.h"
#include <string>
#include <unordered_set>
#endif

namespace {
using Mask = std::uint64_t;
constexpr int capacity = 62;
using Rows = std::array<Mask, capacity>;
Mask vertex(int i) { return Mask{1} << i; }
int first(Mask m) { return std::countr_zero(m); }

#ifdef USE_NAUTY
// The colors preserve the marked vertices used by the extension rules.
std::string canonical(const Rows& board, int n, Mask fixed, bool ear, bool unrooted) {
    graph input[capacity]{}, output[capacity];
    int lab[capacity], partition[capacity], orbits[capacity];
    for (int i = 0; i < n; ++i) {
        for (Mask m = board[i]; m; m &= m - 1) ADDELEMENT(&input[i], first(m));
    }
    int assigned = 0;
    for (int cell = 0; cell < (ear ? 5 : 3); ++cell) {
        for (int v = 0; v < n; ++v) {
            int color = (unrooted || v == 0) ? 0 : ((fixed & vertex(v)) ? 1 : 2);
            if (ear) {
                if (v == 0) color = 0;
                else if (v == 3) color = 1;
                else if (v == 1 || v == 2) color = 2;
                else if (v == 4 || v == 5) color = 3;
                else color = 4;
            }
            if (color != cell) continue;
            lab[assigned] = v;
            partition[assigned++] = 1;
        }
        // Empty color classes require no cell.
        if (assigned) partition[assigned - 1] = 0;
    }
    static DEFAULTOPTIONS_GRAPH(options);
    options.getcanon = TRUE;
    options.defaultptn = FALSE;
    statsblk stats;
    densenauty(input, lab, partition, orbits, &options, &stats, 1, n, output);
    std::string key((n * (n - 1) / 2 + 7) / 8, '\0');
    int index = 0;
    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < i; ++j, ++index) {
            if (ISELEMENT(&output[i], j)) key[index / 8] |= 1u << (index % 8);
        }
    }
    return key;
}
#endif

struct State {
    const Rows& board;
    int order, girth;
    Mask deficient = 0, eligible = 0, heavy = 0, cubic = 0;
    std::array<int, capacity> missing{};
    int total_missing = 0;
    Rows blocked{};

    State(const Rows& board_, int n, int girth_, int maximum, bool single_heavy)
        : board(board_), order(n), girth(girth_) {
        Mask full = 0;
        for (int v = 0; v < n; ++v) {
            const int d = std::popcount(board[v]);
            if (d >= 4) heavy |= vertex(v);
            if (d == 3) cubic |= vertex(v);
            if (d == maximum) full |= vertex(v);
            if (d >= 3) continue;
            missing[v] = 3 - d;
            total_missing += missing[v];
            deficient |= vertex(v);
        }
        eligible = deficient;
        if (!single_heavy) {
            eligible |= heavy & ~full;
            for (Mask m = cubic & ~full; m; m &= m - 1) {
                int v = first(m);
                if (!(board[v] & heavy)) eligible |= vertex(v);
            }
        }
    }

    void path(int v, Mask used, int length, int limit, Mask& excluded) const {
        if (length > 0 && (length + 2 < girth ||
                std::has_single_bit(static_cast<unsigned>(length + 2)))) {
            excluded |= vertex(v);
        }
        if (length >= limit || !(eligible & ~excluded)) return;
        for (Mask m = board[v] & ~used; m; m &= m - 1) {
            int w = first(m);
            path(w, used | vertex(w), length + 1, limit, excluded);
        }
    }

    Mask conflict(int v) {
        if (!blocked[v]) {
            int limit = 2;
            while (2 * limit + 2 < order) limit = 2 * limit + 2;
            limit = std::max(limit, girth - 3);
            blocked[v] = vertex(v);
            path(v, vertex(v), 0, limit, blocked[v]);
        }
        return blocked[v];
    }

    int anchor() {
        int best = -1, score_best = 10000;
        for (Mask m = deficient; m; m &= m - 1) {
            int v = first(m);
            const int score = 6 * std::popcount(eligible & ~conflict(v)) + 12 * missing[v];
            if (score < score_best) { best = v; score_best = score; }
        }
        return best;
    }

    bool too_few_vertices(int remaining) {
        if (total_missing <= remaining) return false;
        for (Mask m = deficient; m; m &= m - 1) {
            int v = first(m), required = missing[v];
            Mask choices = deficient & conflict(v) & ~vertex(v);
            while (choices) {
                int best = -1, score_best = -1;
                for (Mask k = choices; k; k &= k - 1) {
                    int w = first(k);
                    const int score = 5 * missing[w] + std::popcount(choices & conflict(w));
                    if (score > score_best) { best = w; score_best = score; }
                }
                required += missing[best];
                choices &= conflict(best) & ~vertex(best);
            }
            if (required > remaining) return true;
        }
        return false;
    }
};

struct Search {
    int cap, maximum, girth, cache_limit;
    bool single_heavy;
    std::uint64_t visits = 0;
    Rows board{};
    // Once a fixed vertex reaches its required degree, its neighborhood is complete.
    Mask fixed_vertices = 0;
    int triangle_gap = 0, triangle_count = 0, ear_length = 0;
    // Distinct triangles share no edge because four-cycles are forbidden.
    std::array<Mask, capacity * (capacity - 1) / 6> triangles{};
#ifdef USE_NAUTY
    std::array<std::unordered_set<std::string>, capacity + 1> cache{};
#endif

    void toggle(int v, int w) {
        board[v] ^= vertex(w);
        board[w] ^= vertex(v);
    }

    bool triangles_too_close() const {
        if (triangle_gap <= 1) return false;
        for (int i = 0; i < triangle_count; ++i) {
            Mask close = triangles[i], frontier = close;
            for (int k = 1; k < triangle_gap; ++k) {
                Mask adjacent = 0;
                for (Mask m = frontier; m; m &= m - 1) adjacent |= board[first(m)];
                frontier = adjacent & ~close;
                close |= adjacent;
            }
            for (int j = 0; j < i; ++j)
                if (!(triangles[j] & triangles[i]) && (triangles[j] & close)) return true;
        }
        return false;
    }

    bool ear_shortened() const {
        if (ear_length <= 2) return false;
        Mask reached = vertex(1) | vertex(2), frontier = reached;
        const Mask removed = vertex(0) | vertex(3), targets = vertex(4) | vertex(5);
        for (int distance = 1; distance < ear_length && frontier; ++distance) {
            Mask adjacent = 0;
            for (Mask m = frontier; m; m &= m - 1) adjacent |= board[first(m)];
            frontier = adjacent & ~reached & ~removed;
            if (frontier & targets) return true;
            reached |= frontier;
        }
        return false;
    }

    bool search(int n) {
        ++visits;
        if (triangles_too_close() || ear_shortened()) return false;
        State s(board, n, girth, maximum, single_heavy);
        s.eligible &= ~(fixed_vertices & ~s.deficient);
        if (!s.total_missing) {
            std::printf("Candidate of order %d, adjacency masks", n);
            for (int i = 0; i < n; ++i)
                std::printf(" %llu", static_cast<unsigned long long>(board[i]));
            std::puts("");
            return true;
        }
        const int remaining = cap - n, new_vertex_max = single_heavy ? 3 : maximum;
        if (!remaining || s.total_missing > new_vertex_max * remaining) return false;
#ifdef USE_NAUTY
        // Once two adjacent triangles are present, extensions need no marked
        // vertex unless the seed prescribes a cubic degree at a specific vertex.
        const bool unrooted = triangle_gap == 1 && !fixed_vertices;
        if (remaining >= 2 && static_cast<int>(cache[n].size()) < cache_limit &&
            !cache[n].insert(canonical(board, n, fixed_vertices, ear_length > 0, unrooted)).second) return false;
#endif
        int a = s.anchor();
        if (s.too_few_vertices(remaining)) return false;
        auto extend = [&](Mask neighbors, int count) {
            if (single_heavy && s.total_missing + 3 - 2 * count > 3 * (remaining - 1))
                return false;
            const int saved_count = triangle_count;
            if (triangle_gap > 1) {
                for (Mask m = neighbors; m;) {
                    int u = first(m);
                    m &= m - 1;
                    for (Mask z = board[u] & m; z; z &= z - 1)
                        triangles[triangle_count++] = vertex(n) | vertex(u) | vertex(first(z));
                }
            }
            for (Mask m = neighbors; m; m &= m - 1) toggle(n, first(m));
            bool result = search(n + 1);
            for (Mask m = neighbors; m; m &= m - 1) toggle(n, first(m));
            triangle_count = saved_count;
            return result;
        };

        auto choose = [&](auto&& self, Mask row, Mask possible, int count) -> bool {
            if (extend(row, count)) return true;
            if (count == new_vertex_max) return false;
            if (count >= 3) {
                if (row & (s.cubic | s.heavy)) return false;
                possible &= s.deficient;
            }
            while (possible) {
                int v = first(possible);
                possible &= possible - 1;
                Mask next = possible & ~s.conflict(v);
                // Two adjacent old vertices must not both become heavy.
                if (vertex(v) & s.cubic) next &= ~(board[v] & s.cubic);
                if (self(self, row | vertex(v), next, count + 1)) return true;
            }
            return false;
        };
        return choose(choose, vertex(a), s.eligible & ~s.conflict(a), 1);
    }

    bool closes_chord(int v, int target, Mask used, int length) const {
        if (v == target)
            return length >= 3 && std::has_single_bit(static_cast<unsigned>(length + 1));
        if (length >= 31) return false;
        for (Mask m = board[v] & ~used; m; m &= m - 1) {
            int w = first(m);
            if (closes_chord(w, target, used | vertex(w), length + 1)) return true;
        }
        return false;
    }

    bool adjacent_triangles(int length) {
        ear_length = length;
        for (int extra = 3; extra <= 5; ++extra)
            if (std::has_single_bit(static_cast<unsigned>(length + extra))) return false;

        toggle(0, 1); toggle(1, 2); toggle(2, 0);
        toggle(3, 4); toggle(4, 5); toggle(5, 3); toggle(0, 3);
        fixed_vertices = vertex(3);
        int previous = 1;
        for (int i = 0; i < length - 1; ++i) {
            toggle(previous, 6 + i);
            previous = 6 + i;
        }
        toggle(previous, 4);
        auto chords = [&](auto&& self, int next, int count) -> bool {
            if (search(length + 5)) return true;
            if (3 + count == maximum) return false;
            for (int w = next; w < length + 5; ++w) {
                if (closes_chord(0, w, vertex(0), 0)) continue;
                toggle(0, w);
                bool found = self(self, w + 1, count + 1);
                toggle(0, w);
                if (found) return true;
            }
            return false;
        };
        return chords(chords, 6, 0);
    }

    bool triangle_pair(int gap, int type) {
        triangle_gap = gap;
        int end = gap + 2;
        toggle(0, 1); toggle(1, 2); toggle(2, 0);
        toggle(end, end + 1); toggle(end + 1, end + 2); toggle(end + 2, end);
        int previous = 0;
        for (int v = 3; v <= end; ++v) { toggle(previous, v); previous = v; }
        triangles[triangle_count++] = vertex(0) | vertex(1) | vertex(2);
        triangles[triangle_count++] = vertex(end) | vertex(end + 1) | vertex(end + 2);
        if (type < 3) {
            // Type counts how many of the two path endpoints are fixed cubic.
            fixed_vertices = vertex(2) | vertex(end + 2);
            fixed_vertices |= vertex(type >= 2 ? 0 : 1);
            fixed_vertices |= vertex(type >= 1 ? end : end + 1);
        }
        return search(end + 3);
    }

    bool shared_center(int center_degree, int pairs) {
        if (1 + 3 * center_degree - 2 * pairs > cap) return false;
        for (int v = 1; v <= center_degree; ++v) toggle(0, v);
        for (int j = 0; j < pairs; ++j) toggle(2 * j + 1, 2 * j + 2);
        fixed_vertices = vertex(0);
        return search(center_degree + 1);
    }

    bool run(int exact_pairs) {
        for (int v = 1; v <= maximum; ++v) toggle(0, v);
        for (int pairs = 0; pairs <= maximum / 2; ++pairs) {
            if (pairs && girth > 3) break;
            if (pairs) toggle(2 * pairs - 1, 2 * pairs);
            if (exact_pairs >= 0 && exact_pairs != pairs) continue;
            if (1 + 3 * maximum - 2 * pairs > cap) continue;
#ifdef USE_NAUTY
            for (auto& layer : cache) layer.clear();
#endif
            if (search(maximum + 1)) return true;
        }
        return false;
    }
};

bool number(std::string_view value, int& result) {
    const auto parsed = std::from_chars(value.data(), value.data() + value.size(), result);
    return parsed.ec == std::errc{} && parsed.ptr == value.data() + value.size();
}
} // namespace

int main(int argc, char** argv) {
    if (argc < 5 || argc > 7) {
        std::fprintf(stderr, "Usage: %s any|single max-order max-degree girth [pairs|-1] [cache-limit]\n       shared max-order max-degree center-degree pairs [cache-limit]\n       pair max-order max-degree gap type [cache-limit]\n       ear max-order max-degree path-length -1 [cache-limit]\n", argv[0]);
        return 2;
    }
    const std::string_view mode(argv[1]);
    const bool shared = mode == "shared", pair = mode == "pair", ear = mode == "ear";
    int n, degree, girth, pairs = -1, cache_limit = 40000;
    if ((mode != "single" && mode != "any" && !shared && !pair && !ear) ||
        !number(argv[2], n) || !number(argv[3], degree) || !number(argv[4], girth) ||
        (argc >= 6 && !number(argv[5], pairs)) || (argc >= 7 && !number(argv[6], cache_limit)) ||
        n < 4 || n > capacity || degree < 3 || degree >= n || cache_limit < 0) return 2;
    if (ear) {
        if (girth < 1 || girth > n - 5 || pairs != -1) return 2;
    } else if (pair) {
        if (girth < 1 || girth > n - 5 || pairs < 0 || pairs > 3) return 2;
    } else if (girth < 3 || girth > n || pairs < -1 || pairs > degree / 2 ||
        (!shared && girth > 3 && pairs > 0) ||
        (shared && (girth > degree || pairs < 0 || pairs > girth / 2))) return 2;
#ifdef USE_NAUTY
    static_assert(WORDSIZE == 64);
    nauty_check(WORDSIZE, 1, capacity, NAUTYVERSIONID);
#endif
    if (ear) {
        Search search{n, degree, 3, cache_limit, false};
        if (search.adjacent_triangles(girth)) return 1;
        std::printf("No candidate (ear, n<=%d, maximum<=%d, path %d): %llu states.\n",
            n, degree, girth, static_cast<unsigned long long>(search.visits));
        return 0;
    }
    if (pair) {
        Search search{n, degree, 3, cache_limit, false};
        if (search.triangle_pair(girth, pairs)) return 1;
        std::printf("No candidate (pair, n<=%d, maximum<=%d, gap %d, type %d): %llu states.\n",
            n, degree, girth, pairs, static_cast<unsigned long long>(search.visits));
        return 0;
    }
    if (shared) {
        Search search{n, degree, 5, cache_limit, false};
        if (search.shared_center(girth, pairs)) return 1;
        std::printf("No candidate (shared, n<=%d, maximum<=%d, center %d, triangles %d): %llu states.\n",
            n, degree, girth, pairs, static_cast<unsigned long long>(search.visits));
        return 0;
    }
    Search search{n, degree, girth, cache_limit, mode == "single"};
    if (search.run(pairs)) return 1;
    std::printf("No candidate (%s, n<=%d, maximum %d, girth>=%d, pairs %d): %llu states.\n",
        argv[1], n, degree, girth, pairs, static_cast<unsigned long long>(search.visits));
}
