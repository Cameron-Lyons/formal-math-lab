// Check extensions of the candidate first four marks supplied by verify_short.py --quartets.
#include "compatibility_graph.hpp"
#include <iostream>
#include <string_view>

using namespace erdos272_graph;

namespace {
constexpr int need = 121;
const Progressions short_ap = progressions(6);
std::array<int, limit> index_of_mark;

struct OmissionSearch {
    const Graph& graph;
    std::array<Bits, points> omit;
    explicit OmissionSearch(const Graph& g) : graph(g) {
        for (int x = 0; x < points; ++x) {
            omit[x].resize(g.words);
            for (int v = 0; v < static_cast<int>(g.labels.size()); ++v)
                if (!(g.labels[v] & (1 << x))) omit[x][v / 64] |= Word{1} << (v % 64);
        }
    }

    bool possible(Bits candidates, int count, int required, std::array<int, points> missing,
                  std::vector<int>& witness) const {
        if (!required) return *std::max_element(missing.begin(), missing.end()) <= 0;
        Bits branches = candidates;
        if (!graph.required_pool(branches, count, required)) return false;
        auto count_bits = [](const Bits& bits) {
            int total = 0;
            for (Word w : bits) total += std::popcount(w);
            return total;
        };
        int best = count_bits(branches);
        for (int x = 0; x < points; ++x) {
            if (missing[x] <= 0) continue;
            Bits pool(graph.words);
            for (int w = 0; w < graph.words; ++w) pool[w] = candidates[w] & omit[x][w];
            int size = count_bits(pool);
            if (size < missing[x]) return false;
            if (size < 5 * missing[x]) {
                if (!graph.required_pool(pool, size, missing[x])) return false;
                size = count_bits(pool);
            }
            if (size < best) {
                best = size;
                branches = std::move(pool);
            }
        }
        for (int w = graph.words - 1; w >= 0; --w)
            while (branches[w]) {
                int v = 64 * w + 63 - std::countl_zero(branches[w]);
                erase(branches, v);
                erase(candidates, v);
                Bits next(graph.words);
                for (int j = 0; j < graph.words; ++j)
                    next[j] = candidates[j] & graph.edges[v * graph.words + j];
                int left = count_bits(next);
                if (left < required - 1) continue;
                auto rest = missing;
                for (int x = 0; x < points; ++x) rest[x] -= !(graph.labels[v] & (1 << x));
                if (possible(std::move(next), left, required - 1, rest, witness)) {
                    witness.push_back(graph.labels[v]);
                    return true;
                }
            }
        return false;
    }
};

bool check(const std::array<int, 4>& roots, std::vector<int>& witness, bool defer_sevens) {
    std::vector<int> candidates;
    int last = index_of_mark[roots.back()];
    for (int a = 1; a < limit; ++a)
        if (cardinality(a) >= 2 && index_of_mark[a] > last &&
            std::all_of(roots.begin(), roots.end(), [a](int root) { return short_ap[a & root]; }))
            candidates.push_back(a);
    int count = candidates.size();
    if (count < need) return true;
    bool cost_case = defer_sevens && std::all_of(roots.begin(), roots.end(),
                                                 [](int a) { return cardinality(a) == 7; });
    if (cost_case && count > 5255) throw UseCostCheck{};
    Graph graph = ordered_graph(std::move(candidates), short_ap);
    Bits live(graph.words, ~Word{0});
    if (count % 64) live.back() = (Word{1} << (count % 64)) - 1;
    if (!cost_case) {
        Bits uncolored = live;
        if (!graph.required_pool(uncolored, count, need)) return true;
    }
    count = graph.refine(live, count, need, [](int a) {
        return cardinality(a) <= 3 || index_of_mark[a] < limit;
    });
    if (count < need) return true;
    int budget = 3000;
    try {
        return !graph.has_clique(live, count, need, witness, &budget);
    } catch (const UseCostCheck&) {
        if (cost_case) throw;
    }
    // One set omitting x can be replaced by {x}. For two to ten omissions
    // their common intersection has size at most six, so deleting them frees
    // {x} and at least nine pairs through x. Both give a star of size 125,
    // contradicting the starred bound of 124.
    std::array<int, points> missing;
    missing.fill(11);
    for (int root : roots)
        for (int x = 0; x < points; ++x) missing[x] -= !(root & (1 << x));
    return !OmissionSearch(graph).possible(std::move(live), count, need, missing, witness);
}
}

int main(int argc, char** argv) {
    bool defer_sevens = argc == 2 && std::string_view(argv[1]) == "--defer-seven";
    if (argc != 1 && !defer_sevens) return 1;
    int mark_count;
    if (!(std::cin >> mark_count) || mark_count != 101) return 1;
    index_of_mark.fill(limit);
    for (int j = 0; j < mark_count; ++j) {
        int a;
        if (!(std::cin >> a) || a <= 0 || a >= limit || index_of_mark[a] != limit) return 1;
        index_of_mark[a] = j;
    }
    int cases = 0, size, deferred = 0;
    while (std::cin >> size && size == 4) {
        std::array<int, 4> roots;
        int prev = -1;
        for (int& a : roots) {
            if (!(std::cin >> a) || a <= 0 || a >= limit || index_of_mark[a] >= limit ||
                index_of_mark[a] <= prev) return 1;
            prev = index_of_mark[a];
        }
        std::vector<int> witness(roots.begin(), roots.end());
        try {
            if (!check(roots, witness, defer_sevens)) {
                std::cerr << "125 members at masks";
                for (int a : witness) std::cerr << ' ' << a;
                std::cerr << '\n';
                return 2;
            }
        } catch (const UseCostCheck&) {
            std::cout << "cost";
            for (int a : roots) std::cout << ' ' << a;
            std::cout << '\n';
            ++deferred;
        }
        ++cases;
        if (cases % 100 == 0) std::cerr << "Checked " << cases << " quartets\n";
    }
    int expected;
    if (!std::cin || size != 0 || !(std::cin >> expected) || cases != expected) return 1;
    if (defer_sevens) std::cout << "checked " << cases - deferred << " deferred " << deferred << '\n';
    else std::cout << "Excluded 125 members in " << cases << " quartets\n";
}
