// Exhaustive independent validation against permutation enumeration.
#include "exact_cover_hall.hpp"
#include <iostream>
#include <numeric>
#include <random>
#include <vector>
using exact_hall::Bits;
using exact_hall::Domains;

void check(const Domains &domains, const std::vector<int> &left,
           const std::vector<int> &right) {
    Bits lm = 0, rm = 0;
    for (int i : left) lm |= Bits(1) << i;
    for (int p : right) rm |= Bits(1) << p;
    auto permutation = right;
    std::sort(permutation.begin(), permutation.end());
    Domains expected{};
    bool feasible = false;
    do {
        bool okay = true;
        for (std::size_t i = 0; i < left.size(); ++i)
            if (!(domains[left[i]] & (Bits(1) << permutation[i]))) okay = false;
        if (okay) {
            feasible = true;
            for (std::size_t i = 0; i < left.size(); ++i)
                expected[left[i]] |= Bits(1) << permutation[i];
        }
    } while (std::next_permutation(permutation.begin(), permutation.end()));
    Domains actual{};
    auto result = exact_hall::filter(domains, lm, rm, actual);
    if (result.feasible != feasible || (feasible && actual != expected))
        throw std::runtime_error("Hall supports disagree with permutation enumeration");
    if (feasible) {
        unsigned removed = 0;
        for (int i : left) removed += exact_hall::population(domains[i] & rm & ~expected[i]);
        if (removed != result.removed) throw std::runtime_error("incorrect removal count");
    }
    auto unpruned = exact_hall::filter(domains, lm, rm, actual, false);
    if (unpruned.feasible != feasible) throw std::runtime_error("feasibility-only mode differs");
}

int main() {
    std::uint64_t checked = 0;
    for (int n = 0; n <= 4; ++n) {
        std::vector<int> ids(n);
        std::iota(ids.begin(), ids.end(), 0);
        for (unsigned edges = 0; edges < (1u << (n*n)); ++edges) {
            Domains domains{};
            for (int i = 0; i < n; ++i) for (int p = 0; p < n; ++p)
                if ((edges >> (i*n+p)) & 1) domains[i] |= Bits(1) << p;
            check(domains, ids, ids);
            ++checked;
        }
    }
    // Exercise nonconsecutive indices and both halves of the 128-bit masks.
    std::vector<int> left{0, 5, 79}, right{2, 6, 80};
    for (unsigned edges = 0; edges < 512; ++edges) {
        Domains domains{};
        for (int i = 0; i < 3; ++i) for (int p = 0; p < 3; ++p)
            if ((edges >> (3*i+p)) & 1) domains[left[i]] |= Bits(1) << right[p];
        check(domains, left, right);
        ++checked;
    }
    std::mt19937_64 rng(20261122);
    std::vector<int> ids(6);
    std::iota(ids.begin(), ids.end(), 0);
    for (unsigned trial = 0; trial < 1000; ++trial) {
        Domains domains{};
        for (int i = 0; i < 6; ++i) domains[i] = rng() & 63;
        check(domains, ids, ids);
        ++checked;
    }
    // Large known graphs test capacity81 without enumerating81! permutations.
    constexpr Bits all = (Bits(1) << 81) - 1;
    Domains large{}, supported{};
    large.fill(all);
    auto full = exact_hall::filter(large, all, all, supported);
    if (!full.feasible || full.removed || supported != large)
        throw std::runtime_error("complete size81 graph failed");
    for (int i = 0; i < 81; ++i) large[i] = Bits(1) << i;
    auto diagonal = exact_hall::filter(large, all, all, supported);
    if (!diagonal.feasible || diagonal.removed || supported != large)
        throw std::runtime_error("unique size81 matching failed");
    constexpr Bits first40 = (Bits(1) << 40) - 1;
    for (int i = 0; i < 81; ++i) large[i] = i < 41 ? first40 : all & ~first40;
    if (exact_hall::filter(large, all, all, supported).feasible)
        throw std::runtime_error("nontrivial size81 Hall failure was missed");
    std::cout << "PASS: perfect-matching feasibility and every supported edge agree on "
              << checked << " graphs, including all square graphs up to size4.\n";
    std::cout << "PASS: full, unique, and impossible size81 matching instances.\n";
}
