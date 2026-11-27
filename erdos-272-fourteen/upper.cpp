// Decide whether the progression-intersection graph on [N] has a clique of TARGET sets.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>

using Word = std::uint64_t;
using Bits = std::vector<Word>;

#ifndef POINTS
#define POINTS 14
#endif
#ifndef TARGET
#define TARGET 96
#endif
constexpr int n = POINTS, target = TARGET, limit = 1 << n;
static_assert(1 <= n && n <= 14 && target >= 2);
std::array<bool, limit> progression{};

int reflect(int mask) {
    int result = 0;
    for (int i = 0; i < n; ++i)
        result = 2 * result + ((mask >> i) & 1);
    return result;
}

// Choose a minimum-degree vertex of the remaining graph, remove it, and repeat.
// The order affects the speed of the search only.
std::vector<int> removal_order(const std::vector<int>& masks) {
    const int size = masks.size();
    std::vector<int> degree(size), order;
    order.reserve(size);
    for (int i = 0; i < size; ++i)
        for (int b : masks)
            degree[i] += masks[i] != b && progression[masks[i] & b];
    for (int k = 0; k < size; ++k) {
        int best = -1;
        for (int i = 0; i < size; ++i)
            if (degree[i] >= 0 && (best < 0 || degree[i] < degree[best])) best = i;
        const int a = masks[best];
        order.push_back(a);
        degree[best] = -1;
        for (int i = 0; i < size; ++i)
            if (degree[i] >= 0 && progression[a & masks[i]]) --degree[i];
    }
    return order;
}

struct Graph {
    int words;
    std::vector<Bits> neighbors;

    explicit Graph(const std::vector<int>& masks)
        : words((masks.size() + 63) / 64), neighbors(masks.size(), Bits(words)) {
        for (unsigned i = 0; i < masks.size(); ++i)
            for (unsigned j = 0; j < masks.size(); ++j)
                if (i != j && progression[masks[i] & masks[j]])
                    neighbors[i][j / 64] |= Word{1} << (j % 64);
    }

    bool has_clique(Bits candidates, int count, int need) const {
        if (count < need) return false;
        if (need == 1) return true;
        Bits uncovered = candidates, available(words);
        int left = count;
        for (int color = 1; color < need; ++color) {
            available = uncovered;
            for (int i = 0; i < words; ++i) {
                while (available[i]) {
                    const int bit = std::countr_zero(available[i]);
                    const Bits& adjacent = neighbors[64 * i + bit];
                    uncovered[i] &= ~(Word{1} << bit);
                    available[i] &= available[i] - 1;
                    --left;
                    for (int j = i; j < words; ++j) available[j] &= ~adjacent[j];
                }
            }
            if (left < need - color) return false;
        }

        // Every completion includes an uncovered vertex. Try the first such
        // vertex in our branch order, retaining only its remaining neighbors.
        Bits next(words);
        for (int i = words - 1; i >= 0; --i) {
            while (uncovered[i]) {
                const int bit = 63 - std::countl_zero(uncovered[i]);
                const Bits& adjacent = neighbors[64 * i + bit];
                uncovered[i] ^= Word{1} << bit;
                candidates[i] ^= Word{1} << bit;
                int next_count = 0;
                for (int j = 0; j < words; ++j) {
                    next[j] = candidates[j] & adjacent[j];
                    next_count += std::popcount(next[j]);
                }
                if (next_count >= need - 1 && has_clique(next, next_count, need - 1)) return true;
            }
        }
        return false;
    }
};

int main() {
    for (int a = 0; a < n; ++a)
        for (int d = 1; d <= n; ++d) {
            int mask = 0;
            for (int x = a; x < n; x += d) {
                mask |= 1 << x;
                progression[mask] = true;
            }
        }
    std::vector<int> masks(limit - 1);
    std::iota(masks.begin(), masks.end(), 1);
    const auto order = removal_order(masks);
    std::array<int, limit> position{};
    for (int i = 0; i < limit - 1; ++i) position[order[i]] = i;

    int roots = 0, witnesses = 0;
    // Orient the clique so its union with its reflection has its first vertex in the clique.
#ifdef _OPENMP
    #pragma omp parallel for schedule(dynamic) reduction(+:roots,witnesses)
#endif
    for (int i = 0; i < limit - 1; ++i) {
        #ifdef REPORT_PROGRESS
        if (i % 256 == 0) std::cerr << "Root position " << i << " / " << limit - 1 << '\n';
        #endif
        const int root = order[i];
        if (position[reflect(root)] < i) continue;
        ++roots;
        std::vector<int> candidates;
        for (int j = limit - 2; j > i; --j) {
            const int b = order[j];
            if (position[reflect(b)] >= i && progression[root & b]) candidates.push_back(b);
        }
        const int size = candidates.size();
        if (size < target - 1) continue;
        auto local = removal_order(candidates);
        std::reverse(local.begin(), local.end());
        Graph graph(local);
        Bits all(graph.words, ~Word{0});
        if (size % 64) all.back() = (Word{1} << (size % 64)) - 1;
        if (graph.has_clique(all, size, target - 1)) ++witnesses;
    }
    std::cout << roots << " roots checked. A clique of size " << target
              << (witnesses ? " exists.\n" : " does not exist.\n");
    return witnesses ? 1 : 0;
}
