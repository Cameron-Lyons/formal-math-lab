// Build with c++ -O2 -std=c++20 four_or_more.cpp -o four_or_more.
#include "private_triples.hpp"
#include <fstream>
#include <iostream>
#include <string_view>

using namespace erdos272_private;

namespace {
int target = 124;
bool allow_short_progressions = false;

bool exclude_case(const std::vector<int>& roots, int max_mark_size, int last_mark = 0,
                  int external_triple = 0) {
    std::vector<int> domain, small;
    std::array<bool, limit> allowed_small{};
    for (int a = 1; a < limit; ++a) {
        if (size(a) < 4 && !(allow_short_progressions && size(a) >= 2 && progression[a])) continue;
        if (external_triple && !progression[a & external_triple]) continue;
        if (marked[a] && (size(a) > max_mark_size || a <= last_mark)) continue;
        if (std::any_of(roots.begin(), roots.end(), [a](int m) {
            return a == m || !progression[a & m];
        })) continue;
        domain.push_back(a);
        if (size(a) <= 4) {
            small.push_back(a);
            allowed_small[a] = true;
        }
    }
    if (private_triple_bound(roots, 0, domain, allowed_small, max_price, external_triple) < target) return true;
    for (;;) {
        int remaining = 0, removed = 0;
        for (int s : small) {
            if (!allowed_small[s]) continue;
            if (private_triple_bound(roots, s, domain, allowed_small, max_price, external_triple) < target) {
                allowed_small[s] = false;
                ++removed;
            } else {
                ++remaining;
            }
        }
        if (remaining < target - at_least_five_bound) return true;
        if (!removed) return false;
    }
}
// With a maximum-size marked member already fixed, every completion must
// choose target - 121 marked members. Choose further marks in increasing
// numeric order, so smaller unused marks disappear from each child domain.
bool exclude_large_root(const std::vector<int>& roots, int max_size, int last_mark = 0) {
    if (exclude_case(roots, max_size, last_mark)) return true;
    if (static_cast<int>(roots.size()) >= target - 121) return false;
    for (int a = last_mark + 1; a < limit; ++a) {
        if (!marked[a] || size(a) > max_size) continue;
        if (std::any_of(roots.begin(), roots.end(), [a](int r) {
            return a == r || !progression[a & r];
        })) continue;
        auto next = roots;
        next.push_back(a);
        if (!exclude_large_root(next, max_size, a)) return false;
    }
    return true;
}
} // namespace

int main(int argc, char** argv) {
    if (argc == 2 && std::string_view(argv[1]) == "fixed-triple") {
        initialize();
        target = 116;
        int cases = 0;
        for (int t = 1; t < limit; ++t) {
            if (size(t) != 3 || progression[t] || t > reflected(t)) continue;
            if (!exclude_case({}, n, 0, t)) {
                std::cerr << "Unresolved nonprogression triple " << t << '\n';
                return 1;
            }
            ++cases;
        }
        std::cout << cases << " nonprogression triple cases excluded at " << target
                  << " members of size at least four.\n";
        return cases == 252 ? 0 : 1;
    }
    const bool seven_mark_support = argc == 3 && std::string_view(argv[2]) == "seven-mark-support";
    if (seven_mark_support) {
        allow_short_progressions = true;
        target = 121;
    } else if (argc == 3 && std::string_view(argv[2]) == "short-progressions") {
        allow_short_progressions = true;
        target = 125;
    } else if (argc != 2) {
        std::cerr << "Expected the rank weights file and optional short-progressions mode.\n";
        return 1;
    }
    std::ifstream input(argv[1]);
    int mask, weight;
    while (input >> mask) {
        if (!(input >> weight) || mask < 1 || mask >= limit || weight < 0) return 1;
        if (weight == 0) marked[mask] = true;
    }
    if (!input.eof() || std::count(marked.begin(), marked.end(), true) != 363) return 1;

    initialize();
    if (triples.size() != 504 || seven.size() != 14) return 1;
    for (int a = 1; a < limit; ++a)
        if (marked[a] != marked[reflected(a)] ||
            (marked[a] && size(a) <= 7 && !(size(a) == 7 && progression[a]))) return 1;

    int large_cases = 0;
    for (int a = 1; a < limit; ++a) {
        if (seven_mark_support || !marked[a] || size(a) < 8 || a > reflected(a)) continue;
        if (!exclude_large_root({a}, size(a))) {
            std::cerr << "Unresolved marked member " << a << '\n';
            return 1;
        }
        ++large_cases;
    }
    int seven_cases = 0;
    for (unsigned mask_of_roots = 0; mask_of_roots < (1u << seven.size()); ++mask_of_roots) {
        if (std::popcount(mask_of_roots) != (seven_mark_support ? 4 : target - 121)) continue;
        std::vector<int> roots;
        for (std::size_t i = 0; i < seven.size(); ++i)
            if ((mask_of_roots >> i) & 1) roots.push_back(seven[i]);
        auto image = roots;
        for (int& a : image) a = reflected(a);
        std::sort(image.begin(), image.end());
        if (image < roots) continue;
        bool compatible = true;
        for (int a : roots)
            for (int b : roots) compatible &= progression[a & b];
        if (!compatible) continue;
        if (!exclude_case(roots, 7)) {
            std::cerr << "Unresolved seven-term signature " << mask_of_roots << '\n';
            return 1;
        }
        ++seven_cases;
    }
    std::cout << large_cases << " large marked cases and " << seven_cases
              << " seven-term cases excluded at " << target << " members.\n";
    return large_cases == (seven_mark_support ? 0 : 178) &&
           seven_cases == (allow_short_progressions ? 248 : 128) ? 0 : 1;
}
