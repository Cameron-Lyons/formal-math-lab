// Exact clique tests for the two sixteen-point compatibility searches.
#pragma once

#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <utility>
#include <vector>

namespace erdos272_graph {
using Word = std::uint64_t;
using Bits = std::vector<Word>;
constexpr int points = 16;
constexpr int limit = 1 << points;
struct UseCostCheck {};
using Progressions = std::array<bool, limit>;

inline int cardinality(int mask) { return std::popcount(static_cast<unsigned>(mask)); }
inline bool has(const Bits& set, int v) { return set[v / 64] & (Word{1} << (v % 64)); }
inline void erase(Bits& set, int v) { set[v / 64] &= ~(Word{1} << (v % 64)); }

inline Progressions progressions(int max_terms) {
    Progressions result{};
    for (int first = 0; first < points; ++first)
        for (int step = 1; step < points; ++step) {
            int mask = 0;
            for (int j = 0, p = first; j < max_terms && p < points; ++j, p += step) {
                mask |= 1 << p;
                result[mask] = true;
            }
        }
    return result;
}

struct Graph {
    std::vector<int> labels;
    int words;
    Bits edges;
    Graph(std::vector<int> vertices, const Progressions& ap)
        : labels(std::move(vertices)), words((labels.size() + 63) / 64), edges(labels.size() * words) {
        for (int i = 0; i < static_cast<int>(labels.size()); ++i)
            for (int j = 0; j < i; ++j)
                if (ap[labels[i] & labels[j]]) {
                    edges[i * words + j / 64] |= Word{1} << (j % 64);
                    edges[j * words + i / 64] |= Word{1} << (i % 64);
                }
    }
    std::vector<int> smallest_last() const {
        int n = labels.size();
        std::vector<int> degrees(n), ordered(n);
        Bits live(words, ~Word{0});
        for (int i = 0; i < n; ++i)
            for (int j = 0; j < words; ++j) degrees[i] += std::popcount(edges[i * words + j]);
        for (int pos = n - 1; pos >= 0; --pos) {
            auto smallest = std::min_element(degrees.begin(), degrees.end());
            int v = smallest - degrees.begin();
            *smallest = n + 1;
            ordered[pos] = labels[v];
            erase(live, v);
            for (int w = 0; w < words; ++w)
                for (Word bits = edges[v * words + w] & live[w]; bits; bits &= bits - 1)
                    --degrees[64 * w + std::countr_zero(bits)];
        }
        return ordered;
    }

    // Remove target-1 independent classes. Every target clique must meet
    // the remainder. Returns false when the classes and the remaining
    // vertices together already give an upper bound below target.
    bool required_pool(Bits& rest, int count, int target) const {
        if (count < target) return false;
        Bits available(words);
        for (int color = 1; color < target; ++color) {
            available = rest;
            for (int w = 0; w < words; ++w)
                while (available[w]) {
                    int b = std::countr_zero(available[w]);
                    int v = w * 64 + b;
                    rest[w] ^= Word{1} << b;
                    available[w] &= available[w] - 1;
                    --count;
                    for (int k = w; k < words; ++k) available[k] &= ~edges[v * words + k];
                }
            if (count < target - color) return false;
        }
        return true;
    }

    // Delete a vertex or an edge only after establishing that its common
    // neighborhood cannot supply the rest of a clique of the requested size.
    template<class Predicate>
    int refine(Bits& live, int count, int need, Predicate inspect_edges) {
        int n = labels.size();
        Bits pool(words);
        std::vector<int> special;
        for (int i = 0; i < n; ++i)
            if (inspect_edges(labels[i])) special.push_back(i);
        for (int round = 0; round < 4; ++round) {
            bool changed = false;
            for (int i = n - 1; i >= 0; --i) {
                if (!has(live, i)) continue;
                int size = 0;
                for (int w = 0; w < words; ++w) {
                    pool[w] = live[w] & edges[i * words + w];
                    size += std::popcount(pool[w]);
                }
                if (!required_pool(pool, size, need - 1)) {
                    erase(live, i);
                    changed = true;
                    if (--count < need) return count;
                }
            }
            for (int i : special) if (has(live, i))
                for (int j : special) if (j > i && has(live, j) &&
                                            (edges[i * words + j / 64] & (Word{1} << (j % 64)))) {
                    int size = 0;
                    for (int w = 0; w < words; ++w) {
                        pool[w] = live[w] & edges[i * words + w] & edges[j * words + w];
                        size += std::popcount(pool[w]);
                    }
                    if (!required_pool(pool, size, need - 2)) {
                        edges[i * words + j / 64] &= ~(Word{1} << (j % 64));
                        edges[j * words + i / 64] &= ~(Word{1} << (i % 64));
                        changed = true;
                    }
                }
            if (!changed) break;
        }
        return count;
    }

    bool has_clique(Bits candidates, int count, int target, std::vector<int>& witness,
                    int* remaining_nodes) const {
        if (remaining_nodes && --*remaining_nodes < 0) throw UseCostCheck{};
        if (target == 0) return true;
        Bits pool = candidates;
        if (!required_pool(pool, count, target)) return false;
        for (int w = words - 1; w >= 0; --w)
            while (pool[w]) {
                int b = 63 - std::countl_zero(pool[w]);
                int v = 64 * w + b;
                erase(pool, v);
                erase(candidates, v);
                Bits next(words);
                int left = 0;
                for (int j = 0; j < words; ++j) {
                    next[j] = candidates[j] & edges[v * words + j];
                    left += std::popcount(next[j]);
                }
                if (left >= target - 1 && has_clique(std::move(next), left, target - 1,
                                                     witness, remaining_nodes)) {
                    witness.push_back(labels[v]);
                    return true;
                }
            }
        return false;
    }
};

inline Graph ordered_graph(std::vector<int> vertices, const Progressions& ap) {
    return Graph(Graph(std::move(vertices), ap).smallest_last(), ap);
}
} // namespace erdos272_graph
