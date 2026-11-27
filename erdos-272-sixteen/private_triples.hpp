// Shared integer bounds from the private nonprogression triples on [16].
#pragma once

#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <limits>
#include <numeric>
#include <tuple>
#include <vector>

namespace erdos272_private {
constexpr int n = 16;
constexpr int limit = 1 << n;
constexpr int max_price = 5;
constexpr int at_least_five_bound = 93; // See five_or_more.cpp.

struct Triple {
    int mask;
    int hull;
};

using TripleBits = std::array<std::uint64_t, 8>;
std::array<bool, limit> progression{}, compatible_trace{};
std::array<TripleBits, limit> meet{}, contained{}, private_triples{};
std::vector<Triple> triples;
std::array<bool, limit> marked{};
std::vector<int> seven;

int size(int mask) { return std::popcount(static_cast<unsigned>(mask)); }

int reflected(int mask) {
    int result = 0;
    for (int i = 0; i < n; ++i) result = (result << 1) | ((mask >> i) & 1);
    return result;
}

void initialize() {
    for (int start = 0; start < n; ++start)
        for (int step = 1; step < n; ++step) {
            int mask = 0;
            for (int i = start; i < n; i += step) {
                mask |= 1 << i;
                progression[mask] = true;
            }
        }
    compatible_trace = progression;
    for (int i = 0; i < n; ++i)
        for (int j = i + 1; j < n; ++j)
            for (int k = j + 1; k < n; ++k) {
                const int t = (1 << i) | (1 << j) | (1 << k);
                if (progression[t]) continue;
                const int step = std::gcd(j - i, k - j);
                int h = 0;
                for (int x = i; x <= k; x += step) h |= 1 << x;
                triples.push_back({t, h});
            }
    std::sort(triples.begin(), triples.end(), [](Triple a, Triple b) {
        if (size(a.hull) != size(b.hull)) return size(a.hull) > size(b.hull);
        return a.mask < b.mask;
    });

    for (int a = 1; a < limit; ++a) {
        if (size(a) < 2) continue;
        if (progression[a] && size(a) == 7) seven.push_back(a);
        for (std::size_t i = 0; i < triples.size(); ++i) {
            const auto [t, h] = triples[i];
            const std::uint64_t bit = std::uint64_t{1} << (i % 64);
            if (a & t) meet[a][i / 64] |= bit;
            if ((a & t) != t) continue;
            contained[a][i / 64] |= bit;
            if ((a & h) != h) private_triples[a][i / 64] |= bit;
        }
    }
}

// Every root is a fixed member. A nonzero s fixes one more small member.
// The external triple constrains compatibility without adding to the count.
int private_triple_bound(const std::vector<int>& roots, int s, const std::vector<int>& domain,
                      const std::array<bool, limit>& allowed_small, int price_limit = max_price,
                      int external_triple = 0) {
    TripleBits priced = meet[s];
    if (!s) priced.fill(~std::uint64_t{0});
    for (int root : roots)
        if (size(root) <= 4)
            for (std::size_t i = 0; i < priced.size(); ++i) priced[i] &= meet[root][i];
    if (external_triple)
        for (std::size_t i = 0; i < priced.size(); ++i) priced[i] &= meet[external_triple][i];
    TripleBits available = priced;
    for (std::size_t i = 0; i < priced.size(); ++i) {
        available[i] &= ~(contained[s][i] | contained[external_triple][i]);
        for (int root : roots) available[i] &= ~contained[root][i];
    }

    struct Candidate { int mask, cost; };
    std::vector<Candidate> cheap;
    std::vector<std::size_t> pure;
    for (int a : domain) {
        if (s && (a == s || !compatible_trace[a & s])) continue;
        if (size(a) <= 4 && !allowed_small[a]) continue;
        int cost = 0;
        for (std::size_t i = 0; i < priced.size(); ++i)
            cost += std::popcount(private_triples[a][i] & priced[i]);
        if (cost >= price_limit) continue;
        if (progression[a]) pure.push_back(cheap.size());
        cheap.push_back({a, cost});
    }

    int budget = 0;
    for (std::size_t i = 0; i < triples.size(); ++i) {
        if (((available[i / 64] >> (i % 64)) & 1) == 0) continue;
        ++budget;
        const int h = triples[i].hull;
        std::size_t owner = cheap.size();
        for (auto j : pure) {
            const auto& a = cheap[j];
            if ((a.mask & h) != h) continue;
            if (owner == cheap.size() ||
                std::tie(a.cost, a.mask) < std::tie(cheap[owner].cost, cheap[owner].mask))
                owner = j;
        }
        if (owner != cheap.size()) ++cheap[owner].cost;
    }

    std::sort(cheap.begin(), cheap.end(), [](Candidate a, Candidate b) {
        return std::tie(a.cost, a.mask) < std::tie(b.cost, b.mask);
    });
    std::vector<std::vector<int>> classes;
    std::vector<int> first_cost;
    for (auto [a, cost] : cheap) {
        if (cost >= price_limit) break;
        auto group = std::find_if(classes.begin(), classes.end(), [&](const auto& cls) {
            return std::none_of(cls.begin(), cls.end(), [a](int b) { return compatible_trace[a & b]; });
        });
        if (group == classes.end()) {
            classes.push_back({a});
            first_cost.push_back(cost);
        } else {
            group->push_back(a);
        }
    }

    int best = std::numeric_limits<int>::max();
    for (int price = 1; price <= price_limit; ++price) {
        int total = budget;
        for (int c : first_cost) total += std::max(0, price - c);
        best = std::min(best, total / price);
    }
    return best + static_cast<int>(roots.size()) + (s != 0);
}

} // namespace erdos272_private
