// Search simple graphs with up to two distinguished degree-two vertices.
// Ordinary vertices are cubic in the original modes, and have degree at
// least three in the *-any modes. Exit 0 certifies exhaustion through the cap.
#include <algorithm>
#include <array>
#include <bit>
#include <charconv>
#include <cstdint>
#include <cstdio>
#include <string_view>

#ifdef TERMINAL_NAUTY
#include <string>
#include <unordered_set>
#include <vector>
#include "nauty.h"
static_assert(WORDSIZE == 64, "compile with a 64-bit nauty library");
#endif

using Mask = std::uint64_t;
constexpr int capacity = 63;
using Rows = std::array<Mask, capacity>;

Mask vertexBit(int v) { return Mask{1} << v; }
int first(Mask m) { return std::countr_zero(m); }

struct Board {
    Mask terminals;
    Rows neighbors{};

    void toggle(int v, int w) {
        neighbors[v] ^= vertexBit(w);
        neighbors[w] ^= vertexBit(v);
    }
    int missing(int v) const {
        return std::max(0, ((terminals & vertexBit(v)) ? 2 : 3) - std::popcount(neighbors[v]));
    }
    bool connected(int size) const {
        Mask seen = vertexBit(0), pending = seen;
        while (pending) {
            int v = first(pending);
            pending &= pending - 1;
            Mask fresh = neighbors[v] & ~seen;
            seen |= fresh;
            pending |= fresh;
        }
        return std::popcount(seen) == size;
    }
};

#ifdef TERMINAL_NAUTY
// Canonicalization preserves the sole distinguished vertex. Storing and
// comparing the entire canonical graph makes hash collisions harmless.
enum class CacheMode { none, full, bounded };
CacheMode cacheMode = CacheMode::none;

class RootedCache {
    std::array<std::unordered_set<std::string>, capacity + 1> full;
    std::array<std::vector<std::string>, capacity + 1> bounded;
public:
    bool seen(const Board& board, int size) {
        static DEFAULTOPTIONS_GRAPH(options);
        options.getcanon = TRUE;
        options.defaultptn = FALSE;
        graph input[capacity]{}, canonical[capacity]{};
        int labels[capacity], partition[capacity], orbits[capacity];
        for (int v = 0; v < size; ++v) {
            labels[v] = v;
            partition[v] = (v != 0 && v + 1 < size);
            for (Mask row = board.neighbors[v]; row; row &= row - 1) {
                // nauty numbers vertices from the high bit of each word.
                input[v] |= setword{1} << (63 - first(row));
            }
        }
        statsblk stats;
        densenauty(input, labels, partition, orbits, &options, &stats, 1, size, canonical);
        std::string key((size * (size - 1) / 2 + 7) / 8, '\0');
        int pos = 0;
        for (int i = 0; i < size; ++i) {
            for (int j = 0; j < i; ++j, ++pos) {
                if ((canonical[i] >> (63 - j)) & 1U) key[pos / 8] |= char(1U << (pos % 8));
            }
        }
        if (cacheMode == CacheMode::full) return !full[size].insert(std::move(key)).second;
        // A collision evicts the old entry and explores the new board. The
        // direct-mapped table bounds memory without identifying different boards.
        auto& slots = bounded[size];
        if (slots.empty()) slots.resize(32768);
        auto& slot = slots[std::hash<std::string>{}(key) % slots.size()];
        if (slot == key) return true;
        slot = std::move(key);
        return false;
    }
};
RootedCache rootedCache;
#endif

struct Restrictions {
    const Board& board;
    int size;
    Mask deficient = 0;
    Mask eligible = 0;
    Mask heavy = 0;
    Mask degree_three = 0;
    int total_missing = 0;
    std::array<int, capacity> missing{};
    Rows conflicts{};
#ifdef TERMINAL_NAUTY
    Mask exact = 0;
    void inherit(const Restrictions& parent, bool pendant) {
        std::copy_n(parent.conflicts.begin(), size - 1, conflicts.begin());
        if (pendant) {
            // A new leaf supplies no new simple paths between old endpoints.
            // Its own conflict row determines all pairs involving that leaf.
            conflict(size - 1);
            exact |= parent.exact;
        }
    }
#endif

    Restrictions(const Board& board_, int size_, bool unbounded) : board(board_), size(size_) {
        for (int v = 0; v < size; ++v) {
            missing[v] = board.missing(v);
            if (missing[v] != 0) deficient |= vertexBit(v);
            total_missing += missing[v];
            const int degree = std::popcount(board.neighbors[v]);
            if (degree >= 4) heavy |= vertexBit(v);
            if (degree == 3) degree_three |= vertexBit(v);
        }
        eligible = deficient;
        if (unbounded) {
            eligible |= heavy;
            for (Mask m = degree_three; m; m &= m - 1) {
                int v = first(m);
                if (!(board.neighbors[v] & heavy)) eligible |= vertexBit(v);
            }
        }
    }

    // Two earlier neighbors cannot be the ends of a simple old path of
    // length 2, 6, 14, or 30. The new vertex would close a forbidden cycle.
    void path_ends(int v, Mask used, int length, int limit, Mask& found) const {
        if (length >= 2 && std::has_single_bit(static_cast<unsigned>(length + 2)))
            found |= vertexBit(v);
        if (length == limit || (eligible & ~found) == 0) return;
        for (Mask next = board.neighbors[v] & ~used; next; next &= next - 1) {
            int w = first(next);
            path_ends(w, used | vertexBit(w), length + 1, limit, found);
        }
    }

    Mask conflict(int v) {
        Mask& endpoints = conflicts.at(v);
#ifdef TERMINAL_NAUTY
        if (cacheMode == CacheMode::bounded && (exact & vertexBit(v))) return endpoints;
        if (cacheMode == CacheMode::bounded || endpoints == 0) {
#else
        if (endpoints == 0) {
#endif
            int limit = 2;
            while (2 * limit + 2 < size) limit = 2 * limit + 2;
            endpoints |= vertexBit(v);
            path_ends(v, vertexBit(v), 0, limit, endpoints);
#ifdef TERMINAL_NAUTY
            if (cacheMode == CacheMode::bounded) {
                for (Mask m = endpoints & eligible; m; m &= m - 1) conflicts[first(m)] |= vertexBit(v);
                exact |= vertexBit(v);
            }
#endif
        }
        return endpoints;
    }

    // Each pairwise incompatible set needs distinct fresh neighbors for
    // every missing incidence. Any clique supplies a rigorous bound.
    bool exceeds_capacity(int remaining) {
        if (total_missing <= remaining) return false;
        for (Mask starts = deficient; starts; starts &= starts - 1) {
            int v = first(starts);
            int required = missing[v];
            Mask choices = deficient & conflict(v) & ~vertexBit(v);
            while (choices) {
                int best = first(choices), best_score = -1;
                for (Mask m = choices; m; m &= m - 1) {
                    int w = first(m);
                    int score = 5 * missing[w] + std::popcount(choices & conflict(w));
                    if (score > best_score) { best_score = score; best = w; }
                }
                required += missing[best];
                if (required > remaining) return true;
                choices &= conflict(best) & ~vertexBit(best);
            }
            if (required > remaining) return true;
        }
        return false;
    }

    int anchor() {
        int best = first(deficient), best_score = 10000;
        for (Mask m = deficient; m; m &= m - 1) {
            int v = first(m);
            int score = 6 * std::popcount(eligible & ~conflict(v)) + 12 * missing[v];
            if (score < best_score) { best_score = score; best = v; }
        }
        return best;
    }
};

struct Search {
    int cap;
    Board board;
    bool unbounded;
    std::uint64_t visits = 0;

    bool candidate(int size, [[maybe_unused]] const Restrictions* parent = nullptr,
                   [[maybe_unused]] bool pendant = false) {
        ++visits;
        Restrictions rules(board, size, unbounded);
        if (rules.total_missing == 0) {
            // With unbounded degrees an ordinary vertex that already has three
            // neighbors may acquire more. A disconnected completed board is
            // itself evidence for the search allowing at most two defects.
            if (!unbounded && !board.connected(size)) return false;
            std::printf("Candidate on %d vertices, adjacency masks", size);
            for (int i = 0; i < size; ++i)
                std::printf(" %llu", static_cast<unsigned long long>(board.neighbors[i]));
            std::puts("");
            return true;
        }
        const int remaining = cap - size;
        if (remaining == 0 || (!unbounded && rules.total_missing > 3 * remaining)) return false;
#ifdef TERMINAL_NAUTY
        const bool cacheHere = (cacheMode == CacheMode::full && remaining >= 2) ||
            (cacheMode == CacheMode::bounded && remaining >= 3 && size > 9);
        if (cacheHere && rootedCache.seen(board, size)) return false;
        if (cacheMode == CacheMode::bounded && parent) rules.inherit(*parent, pendant);
#endif
        if (rules.exceeds_capacity(remaining)) return false;

        int a = rules.anchor();
        Mask available = rules.eligible & ~rules.conflict(a);
        auto extend = [&](Mask neighbors) {
            const int new_missing = rules.total_missing + 3 - 2 * std::popcount(neighbors);
            if (!unbounded && new_missing > 3 * (remaining - 1)) return false;
            for (Mask m = neighbors; m; m &= m - 1) board.toggle(size, first(m));
            bool found = candidate(size + 1, &rules, std::has_single_bit(neighbors));
            for (Mask m = neighbors; m; m &= m - 1) board.toggle(size, first(m));
            return found;
        };

        if (unbounded) {
            // In an edge-minimal example no edge joins two vertices of degree
            // >=4. Test this when the new row or two of its neighbors grow.
            auto choose = [&](auto&& self, Mask chosen, Mask choices) -> bool {
                if (extend(chosen)) return true;
                if (std::popcount(chosen) >= 3) {
                    if (chosen & (rules.heavy | rules.degree_three)) return false;
                    choices &= rules.deficient;
                }
                while (choices) {
                    int v = first(choices);
                    choices &= choices - 1;
                    if ((rules.degree_three & vertexBit(v)) &&
                        (board.neighbors[v] & chosen & rules.degree_three)) continue;
                    if (self(self, chosen | vertexBit(v), choices & ~rules.conflict(v))) return true;
                }
                return false;
            };
            return choose(choose, vertexBit(a), available);
        }
        if (extend(vertexBit(a))) return true;
        for (Mask m = available; m;) {
            int b = first(m);
            m &= m - 1;
            if (extend(vertexBit(a) | vertexBit(b))) return true;
            for (Mask rest = m & ~rules.conflict(b); rest; rest &= rest - 1)
                if (extend(vertexBit(a) | vertexBit(b) | vertexBit(first(rest)))) return true;
        }
        return false;
    }
};

int main(int argc, char** argv) {
    if (argc != 3) {
        std::fprintf(stderr, "Usage: %s one|two|zero-any|one-any|two-any"
#ifdef TERMINAL_NAUTY
                     "|one-cache|one-bounded"
#endif
                     " max-order\n", argv[0]);
        return 2;
    }
    const std::string_view mode(argv[1]), arg(argv[2]);
    const bool unbounded = mode == "zero-any" || mode == "one-any" || mode == "two-any";
    bool one = mode == "one" || mode == "one-any";
#ifdef TERMINAL_NAUTY
    if (mode == "one-cache" || mode == "one-bounded") {
        one = true;
        cacheMode = mode == "one-cache" ? CacheMode::full : CacheMode::bounded;
        nauty_check(WORDSIZE, 1, capacity, NAUTYVERSIONID);
    }
#endif
    if (!one && mode != "two" && !unbounded) return 2;
    int cap = 0;
    auto result = std::from_chars(arg.data(), arg.data() + arg.size(), cap);
    if (result.ec != std::errc{} || result.ptr != arg.data() + arg.size() ||
        cap < 3 || cap > capacity) return 2;
    const bool zero = mode == "zero-any";
    Search search{cap, Board{zero ? 0 : one ? vertexBit(0) : (vertexBit(0) | vertexBit(1))}, unbounded};
    if (zero && search.candidate(1)) return 1;
    if (one) {
        // Expose the distinguished vertex and its two neighbors.
        search.board.toggle(0, 1);
        search.board.toggle(0, 2);
        if (search.candidate(3)) return 1;
        search.board.toggle(1, 2);
        if (search.candidate(3)) return 1;
    } else if (!zero) {
        // Expose the two distinguished vertices, allowing either adjacency.
        if (search.candidate(2)) return 1;
        search.board.toggle(0, 1);
        if (search.candidate(2)) return 1;
    }
    std::printf("No candidate (%s) through order %d after %llu states.\n", argv[1], cap,
                static_cast<unsigned long long>(search.visits));
}
