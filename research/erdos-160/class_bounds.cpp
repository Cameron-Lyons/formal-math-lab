#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

// Check the sharp universal bounds 17 for one color and 31 for two colors
// on [78], where every 4-term progression must display at least three colors.
// The final tests fix two color classes and search for a completion with five other colors.
// Compile with c++ -O3 -std=c++20 class_bounds.cpp.
using Mask = __uint128_t;
constexpr int maximum_length = 78;
using Graph = std::array<Mask, maximum_length>;

static Mask bit(int vertex) { return Mask(1) << vertex; }
static int first(Mask vertices) {
    const auto lower = static_cast<std::uint64_t>(vertices);
    if (lower) return __builtin_ctzll(lower);
    return 64 + __builtin_ctzll(static_cast<std::uint64_t>(vertices >> 64));
}
static int count(Mask vertices) {
    return __builtin_popcountll(static_cast<std::uint64_t>(vertices))
         + __builtin_popcountll(static_cast<std::uint64_t>(vertices >> 64));
}

struct Search {
    int length, target;
    std::array<Graph, maximum_length> forbidden_thirds{};
    std::vector<Mask> solutions;
    std::vector<Mask> progressions;

    Search(int n, int k) : length(n), target(k) {
        for (int d = 1; 3*d < length; ++d) {
            for (int a = 0; a+3*d < length; ++a) {
                const std::array<int,4> progression{a, a+d, a+2*d, a+3*d};
                progressions.push_back(bit(a) | bit(a+d) | bit(a+2*d) | bit(a+3*d));
                for (int u : progression) for (int v : progression) {
                    if (u == v) continue;
                    for (int w : progression)
                        if (w != u && w != v) forbidden_thirds[u][v] |= bit(w);
                }
            }
        }
    }

    void visit(const Graph& graph, Mask available, Mask chosen, int size) {
        if (size == target) {
            solutions.push_back(chosen);
            return;
        }
        if (size + count(available) < target) return;

        // Every completion is a clique in graph. Greedily partition the
        // available vertices into independent sets to bound the clique size.
        std::array<int,maximum_length> order{}, bound{};
        int used = 0, colors = 0;
        for (Mask uncolored = available; uncolored; ) {
            ++colors;
            for (Mask independent = uncolored; independent; ) {
                int v = first(independent);
                uncolored ^= bit(v);
                independent &= ~(bit(v) | graph[v]);
                order[used] = v;
                bound[used++] = colors;
            }
        }
        for (int j = used-1; j >= 0; --j) {
            // The first j+1 vertices use at most bound[j] colors in the
            // coloring just built. Every clique uses each color at most once.
            if (size + bound[j] < target) return;
            const int v = order[j];
            const Mask next = available & graph[v];
            available ^= bit(v);
            if (size + 1 + count(next) < target) continue;

            // graph currently forbids pairs forming a bad triple with a
            // chosen vertex. Add the new forbidden pairs created by v.
            Graph updated;
            for (Mask m = next; m; m &= m-1) {
                const int u = first(m);
                updated[u] = graph[u] & ~forbidden_thirds[u][v];
            }
            visit(updated, next, chosen | bit(v), size+1);
        }
    }

    // With anchor forced to be a separate color, every AP with two anchor
    // points makes the other pair incompatible in a second color.
    Graph compatibility_graph(Mask anchor) const {
        const Mask available = (bit(length)-1) ^ anchor;
        Graph graph{};
        for (int v = 0; v < length; ++v) graph[v] = available & ~bit(v);
        for (Mask progression : progressions) {
            if (count(progression & anchor) != 2) continue;
            const Mask pair = progression & ~anchor;
            const int u = first(pair);
            const int v = first(pair ^ bit(u));
            graph[u] &= ~bit(v);
            graph[v] &= ~bit(u);
        }
        return graph;
    }

    void run(Mask anchor = 0) {
        solutions.clear();
        const Mask available = (bit(length)-1) ^ anchor;
        visit(compatibility_graph(anchor), available, 0, 0);
    }

    bool valid_pair(Mask a, Mask b) const {
        if (a & b) return false;
        for (Mask progression : progressions) {
            if (count(a & progression) > 2 || count(b & progression) > 2)
                return false;
            if ((progression & (a|b)) == progression) return false;
        }
        return true;
    }
};

// After two exact color classes have been fixed, the other five color names
// are interchangeable until used. In a 4-AP with two points of one color,
// the remaining two points have distinct colors, both different from that color.
struct Completion {
    struct State {
        Mask unassigned{};
        Mask singletons{};
        std::array<Mask,7> classes{};
        Graph unequal{};
        std::array<std::uint8_t,78> domain{}, color{};
        int used = 0;
    };
    using Pair = std::array<int,2>;
    std::array<std::array<std::vector<Pair>,78>,78> remaining_pairs{};
    Graph neighbors{};
    std::array<int,78> degree{};
    std::array<int,78> order{};
    std::uint64_t nodes = 0;

    Completion() {
        for (int d = 1; 3*d < 78; ++d) for (int a = 0; a+3*d < 78; ++a) {
            std::array<int,4> ap{a, a+d, a+2*d, a+3*d};
            for (int u : ap) ++degree[u];
            for (int u : ap) for (int v : ap) if (u != v) {
                Pair other{};
                int j = 0;
                for (int w : ap) if (w != u && w != v) other[j++] = w;
                remaining_pairs[u][v].push_back(other);
                neighbors[u] |= bit(v);
            }
        }
        for (int u = 0; u < 78; ++u) order[u] = u;
        std::stable_sort(order.begin(), order.end(), [&](int a, int b) {
            return degree[a] > degree[b];
        });
    }

    static bool remove_colors(State& state, int u, unsigned removed) {
        const unsigned domain = (state.domain[u] &= ~removed);
        if (!domain) return false;
        if ((domain & (domain-1)) == 0) state.singletons |= bit(u);
        return true;
    }

    bool assign(State& state, int u, int color) const {
        const unsigned color_bit = 1u << color;
        for (Mask m = state.unequal[u] & state.unassigned; m; m &= m-1) {
            if (!remove_colors(state, first(m), color_bit)) return false;
        }
        for (Mask m = state.classes[color] & neighbors[u]; m; m &= m-1) {
            for (auto [a,b] : remaining_pairs[u][first(m)]) {
                const int ca = state.color[a], cb = state.color[b];
                if (ca == color || cb == color || (ca < 7 && ca == cb)) return false;
                if (ca == 7) {
                    const unsigned forbidden = color_bit | (cb < 7 ? 1u << cb : 0);
                    if (!remove_colors(state, a, forbidden)) return false;
                }
                if (cb == 7) {
                    const unsigned forbidden = color_bit | (ca < 7 ? 1u << ca : 0);
                    if (!remove_colors(state, b, forbidden)) return false;
                }
                if (ca == 7 && cb == 7) {
                    state.unequal[a] |= bit(b);
                    state.unequal[b] |= bit(a);
                }
            }
        }
        state.unassigned ^= bit(u);
        state.singletons &= ~bit(u);
        state.classes[color] |= bit(u);
        state.color[u] = static_cast<std::uint8_t>(color);
        return true;
    }

    bool solve(State& state) {
        ++nodes;
        while (state.singletons) {
            const int u = first(state.singletons);
            const int color = __builtin_ctz(state.domain[u]);
            state.used = std::max(state.used, color+1);
            if (!assign(state, u, color)) return false;
        }
        if (!state.unassigned) return true;
        int position = -1, score = -100000;
        for (int u : order) {
            if (!(state.unassigned & bit(u))) continue;
            // Prefer smaller domains, then positions involved in many constraints.
            const int rank = -1000*count(state.domain[u])
                + 5*count(state.unequal[u] & state.unassigned) + degree[u];
            if (rank > score) { score = rank; position = u; }
        }
        const unsigned names = (1u << std::min(5, state.used+1))-1;
        const unsigned options = state.domain[position] & names;
        for (unsigned m = options; m; m &= m-1) {
            const int color = __builtin_ctz(m);
            State next = state;
            next.used = std::max(state.used, color+1);
            if (assign(next, position, color) && solve(next)) return true;
        }
        return false;
    }

    bool run(Mask a, Mask b) {
        State state;
        state.domain.fill(31);
        state.color.fill(7);
        state.unassigned = bit(78)-1;
        for (Mask m = a; m; m &= m-1)
            if (!assign(state, first(m), 6)) return false;
        for (Mask m = b; m; m &= m-1)
            if (!assign(state, first(m), 5)) return false;
        return solve(state);
    }
};

static Mask reflection(Mask m) {
    Mask reflected = 0;
    for (; m; m &= m-1) reflected |= bit(77-first(m));
    return reflected;
}

bool exclude_completions(Search& search, Completion& solver, int largest, int next) {
    search.target = largest;
    search.run();
    const auto anchors = search.solutions;
    search.target = next;
    std::uint64_t cases = 0;
    const auto initial_nodes = solver.nodes;
    for (Mask a : anchors) {
        // Reflection preserves the interval and all its progressions.
        if (a > reflection(a)) continue;
        search.run(a);
        for (Mask b : search.solutions) {
            ++cases;
            if (solver.run(a,b)) return false;
        }
    }
    std::printf("Excluded %d+%d in seven colors: %llu pairs, %llu completion nodes.\n",
                largest, next, static_cast<unsigned long long>(cases),
                static_cast<unsigned long long>(solver.nodes-initial_nodes));
    return true;
}

// The two selected original classes can gain arbitrary new positions. Enumerate
// all compatible final supports containing them, then use the five-color solver.
struct RetainedPair {
    Search& supports;
    Completion& solver;
    std::uint64_t cases = 0;

    bool enlarge_second(Mask a, Mask b, Mask available) {
        ++cases;
        if (solver.run(a,b)) return true;
        for (Mask m = available; m; ) {
            const Mask v = m & -m;
            m ^= v;
            if (supports.valid_pair(a, b|v) && enlarge_second(a, b|v, m))
                return true;
        }
        return false;
    }

    bool enlarge_first(Mask a, Mask b, Mask available) {
        if (enlarge_second(a, b, (bit(78)-1) & ~(a|b))) return true;
        for (Mask m = available; m; ) {
            const Mask v = m & -m;
            m ^= v;
            if (supports.valid_pair(a|v, b) && enlarge_first(a|v, b, m))
                return true;
        }
        return false;
    }

    bool run(Mask a, Mask b) {
        bool can_merge = true;
        for (Mask ap : supports.progressions) {
            if (count(ap & (a|b)) >= 3) can_merge = false;
        }
        if (can_merge) {
            std::fputs("These classes may merge; separate-class reduction inapplicable.\n", stderr);
            std::exit(2);
        }
        if (!supports.valid_pair(a,b)) return false;
        return enlarge_first(a, b, (bit(78)-1) & ~(a|b));
    }
};

bool exclude_two_canli_classes(Search& search, Completion& solver) {
    constexpr char canli[] = "11621104463534521203342250566043463151352021104225456604146315040331262162520";
    static_assert(sizeof(canli) == 78);
    std::array<Mask,7> classes{};
    for (int i = 0; i < 77; ++i) classes[canli[i]-'0'] |= bit(i);

    RetainedPair exclusion{search, solver};
    const auto initial_nodes = solver.nodes;
    for (int a = 0; a < 7; ++a) for (int b = a+1; b < 7; ++b) {
        if (exclusion.run(classes[a], classes[b])) return false;
    }
    std::printf("Canli class pairs: %llu exact support pairs excluded in %llu nodes.\n",
                static_cast<unsigned long long>(exclusion.cases),
                static_cast<unsigned long long>(solver.nodes-initial_nodes));
    return exclusion.cases == 430;
}

// In a seven-coloring, a 17-point color class leaves 61 points in six
// classes of size at most 11 (the 17+12, 17+13 and 17+14 exclusions).
// Consequently one remaining class has exactly 11 points.
bool exclude_one_17_support(Search& search, Completion& solver) {
    Mask anchor = 0;
    for (int v : {1,2,5,6,15,17,26,27,31,34,58,62,65,67,73,75,78})
        anchor |= bit(v-1);
    search.target = 11;
    search.run(anchor);
    if (search.solutions.size() != 107583) return false;
    const auto start = solver.nodes;
    for (Mask second : search.solutions)
        if (solver.run(anchor, second)) return false;
    std::printf("Fixed 17-point support: %zu second supports excluded in %llu nodes.\n",
                search.solutions.size(), static_cast<unsigned long long>(solver.nodes-start));
    return true;
}

int main() {
    Search search(78, 18);
    search.run();
    if (!search.solutions.empty()) return 1;

    search.target = 17;
    search.run();
    const auto largest = search.solutions;
    if (largest.size() != 44) return 1;
    search.target = 15;
    for (Mask anchor : largest) {
        search.run(anchor);
        if (!search.solutions.empty()) return 1;
    }

    search.target = 16;
    search.run();
    const auto& sixteen = search.solutions;
    if (sixteen.size() != 25631) return 1;
    for (std::size_t i = 0; i < sixteen.size(); ++i) {
        const Mask anchor = sixteen[i];
        const Graph graph = search.compatibility_graph(anchor);
        for (std::size_t j = 0; j < i; ++j) {
            const Mask other = sixteen[j];
            if (anchor & other) continue;
            bool compatible = true;
            for (Mask m = other; m; m &= m-1) {
                const int u = first(m);
                if (other & ~(graph[u] | bit(u))) {
                    compatible = false;
                    break;
                }
            }
            if (compatible) return 1;
        }
    }

    // Giving every remaining position a separate color realizes these two
    // classes. This directly checks attainment of both claimed maxima.
    Mask a = 0, b = 0;
    for (int x : {1,3,6,8,17,21,37,42,43,48,50,62,65,67,73,75,78}) a |= bit(x-1);
    for (int x : {2,5,9,10,19,30,31,34,35,59,60,66,74,77}) b |= bit(x-1);
    if (count(a) != 17 || count(b) != 14 || !search.valid_pair(a,b)) return 1;

    std::puts("Maximum one-color support: 17 (44 supports).");
    std::puts("Maximum two-color union: 31 (17+14 attained).");
    std::puts("No compatible 17+15 pair or 16+16 pair (25,631 size-16 supports).");
    Completion solver;
    if (!exclude_two_canli_classes(search, solver)
        || !exclude_completions(search, solver, 17, 14)
        || !exclude_completions(search, solver, 17, 13)
        || !exclude_completions(search, solver, 17, 12)
        || !exclude_completions(search, solver, 16, 15)
        || !exclude_one_17_support(search, solver)) return 1;
    return 0;
}
