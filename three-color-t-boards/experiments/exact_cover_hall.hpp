#pragma once
// Exact all-different filtering for a square position/pattern support graph.
// A completion of the colored exact-cover problem induces a perfect matching.
// Once one matching is known, an edge belongs to some perfect matching iff
// it is matched or belongs to an alternating cycle. Strong connectivity in
// the contracted matching graph detects precisely those alternating cycles.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <stdexcept>

namespace exact_hall {
using Bits = __uint128_t;
constexpr int capacity = 81;
using Domains = std::array<Bits, capacity>;

inline int population(Bits value) {
    return std::popcount(static_cast<std::uint64_t>(value)) +
           std::popcount(static_cast<std::uint64_t>(value >> 64));
}

inline int first(Bits value) {
    auto lower = static_cast<std::uint64_t>(value);
    return lower ? std::countr_zero(lower) :
           64 + std::countr_zero(static_cast<std::uint64_t>(value >> 64));
}

struct Result {
    bool feasible = false;
    unsigned removed = 0;
};

class Matching {
    const Domains &domains_;
    Bits right_;
public:
    std::array<int, capacity> owner;

    Matching(const Domains &domains, Bits right) : domains_(domains), right_(right) {
        owner.fill(-1);
    }

    bool augment(int left, Bits &visited) {
        Bits options = domains_[left] & right_ & ~visited;
        while (options) {
            int right = first(options);
            Bits bit = Bits(1) << right;
            options &= ~bit;
            visited |= bit;
            if (owner[right] < 0 || augment(owner[right], visited)) {
                owner[right] = left;
                return true;
            }
            // Recursive calls may have marked additional right vertices.
            options &= ~visited;
        }
        return false;
    }
};

// Indices can have holes: used positions and patterns are absent from masks.
// On success, supported contains exactly edges occurring in any perfect
// matching of this graph, not necessarily in a full T-board completion.
// With prune=false only matching feasibility is tested, and supports are
// copied unchanged. Inputs must have equal-sized left and right masks.
inline Result filter(const Domains &domains, Bits left_mask, Bits right_mask,
                     Domains &supported, bool prune = true) {
    constexpr Bits valid = (Bits(1) << capacity) - 1;
    if ((left_mask & ~valid) || (right_mask & ~valid) ||
        population(left_mask) != population(right_mask)) {
        throw std::invalid_argument("Hall filter requires a square support graph of size <=81");
    }
    supported.fill(0);
    std::array<int, capacity> order{};
    int size = 0;
    for (Bits left = left_mask; left; left &= left - 1) {
        int i = first(left);
        order[size++] = i;
        supported[i] = domains[i] & right_mask;
        if (!supported[i]) return {};
    }
    std::sort(order.begin(), order.begin() + size, [&](int a, int b) {
        return population(supported[a]) < population(supported[b]);
    });
    Matching matching(supported, right_mask);
    for (int index = 0; index < size; ++index) {
        Bits visited = 0;
        if (!matching.augment(order[index], visited)) return {};
    }
    Result result{true, 0};
    if (!prune) return result;

    // Contract matched edges. An unmatched edge i--p becomes i -> owner[p].
    Domains reach{};
    for (int index = 0; index < size; ++index) {
        int i = order[index];
        reach[i] = Bits(1) << i;
        for (Bits options = supported[i]; options; options &= options - 1) {
            int owner = matching.owner[first(options)];
            if (owner < 0) throw std::logic_error("perfect matching omitted a right vertex");
            reach[i] |= Bits(1) << owner;
        }
    }
    for (int kindex = 0; kindex < size; ++kindex) {
        int k = order[kindex];
        for (int iindex = 0; iindex < size; ++iindex) {
            int i = order[iindex];
            if (reach[i] & (Bits(1) << k)) reach[i] |= reach[k];
        }
    }
    for (int index = 0; index < size; ++index) {
        int i = order[index];
        for (Bits options = supported[i]; options; options &= options - 1) {
            int p = first(options);
            if (!(reach[matching.owner[p]] & (Bits(1) << i))) {
                supported[i] &= ~(Bits(1) << p);
                ++result.removed;
            }
        }
    }
    return result;
}
} // namespace exact_hall
