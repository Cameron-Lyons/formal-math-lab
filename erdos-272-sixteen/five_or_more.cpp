// Every admissible family of subsets of [16] with all sizes >= 5 has size <= 93.
// Build: c++ -O2 -std=c++20 five_or_more.cpp -o five_or_more
#include <algorithm>
#include <array>
#include <bit>
#include <iostream>
#include <numeric>
#include <tuple>
#include <vector>

namespace {
constexpr int n = 16;
constexpr int limit = 1 << n;
constexpr int price = 8;

struct Triple {
    int mask;
    int hull;
};

std::array<bool, limit> progression{};
std::array<int, limit> cost{};
std::vector<Triple> triples;
std::vector<int> cheap;
std::vector<int> longest_choices{0}; // zero denotes absence of any AP member

int size(int mask) { return std::popcount(static_cast<unsigned>(mask)); }

int reflected(int mask) {
    int image = 0;
    for (int i = 0; i < n; ++i)
        image = (image << 1) | ((mask >> i) & 1);
    return image;
}

void initialize() {
    for (int i = 0; i < n; ++i) {
        for (int d = 1; d < n; ++d) {
            int mask = 0;
            for (int j = i; j < n; j += d) {
                mask |= 1 << j;
                progression[mask] = true;
            }
        }
    }
    for (int x = 0; x < n; ++x)
        for (int y = x + 1; y < n; ++y)
            for (int z = y + 1; z < n; ++z) {
                const int triple = (1 << x) | (1 << y) | (1 << z);
                if (progression[triple]) continue;
                int hull = 0;
                const int step = std::gcd(y - x, z - y);
                for (int j = x; j <= z; j += step) hull |= 1 << j;
                triples.push_back({triple, hull});
            }
    for (int a = 1; a < limit; ++a) {
        if (size(a) < 5) continue;
        if (progression[a] && a <= reflected(a)) longest_choices.push_back(a);
        for (const auto& [t, h] : triples)
            cost[a] += (a & t) == t && (a & h) != h;
        if (cost[a] < price) cheap.push_back(a);
    }
    // A longer hull fits inside fewer progressions and gets assigned first.
    std::sort(triples.begin(), triples.end(), [](Triple a, Triple b) {
        if (size(a.hull) != size(b.hull)) return size(a.hull) > size(b.hull);
        return a.mask < b.mask;
    });
}

// A private triple can be charged to only one member. Triples already covered
// by the fixed progression P are unavailable for every charge.
int family_bound(int p) {
    std::vector<int> candidates, pure;
    for (int a : cheap) {
        if (p && !progression[p & a]) continue;
        if (progression[a]) {
            if (!p || size(a) > size(p)) continue;
            pure.push_back(a);
            cost[a] = 0;
        }
        candidates.push_back(a);
    }
    int budget = 0;
    for (const auto& [t, h] : triples) {
        if ((p & t) == t) continue;
        ++budget;
        // In addition to its private owners, t may be charged to one
        // candidate containing its hull. Here we choose a progression.
        int owner = 0;
        for (int a : pure)
            if ((a & h) == h && (!owner || std::tie(cost[a], a) < std::tie(cost[owner], owner)))
                owner = a;
        if (owner) ++cost[owner];
    }
    std::sort(candidates.begin(), candidates.end(), [](int a, int b) {
        return std::tie(cost[a], a) < std::tie(cost[b], b);
    });
    std::vector<std::vector<int>> classes;
    for (int a : candidates) {
        if (cost[a] >= price) break;
        auto incompatible = [&](int b) { return !progression[a & b]; };
        auto group = std::find_if(classes.begin(), classes.end(), [&](const auto& cls) {
            return std::all_of(cls.begin(), cls.end(), incompatible);
        });
        if (group == classes.end()) {
            classes.push_back({a});
            budget += price - cost[a]; // largest discount within this class
        } else {
            group->push_back(a);
        }
    }
    return budget / price;
}
} // namespace

int main() {
    initialize();
    int largest = 0;
    for (int p : longest_choices) largest = std::max(largest, family_bound(p));
    std::cout << triples.size() << " nonprogression triples, " << longest_choices.size()
              << " cases, maximum certified upper bound " << largest << '\n';
    return triples.size() == 504 && longest_choices.size() == 56 && largest == 93 ? 0 : 1;
}
