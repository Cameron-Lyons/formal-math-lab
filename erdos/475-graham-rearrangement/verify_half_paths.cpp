// The finite path lemma for Graham's rearrangement conjecture modulo 47.
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <stdexcept>

using Mask = std::uint64_t;
constexpr int p = 47;
constexpr Mask bit(int x) { return Mask{1} << x; }

// Bit x-2 chooses x or 1-x from the pair {x, 48-x}, for 2 <= x <= 23.
constexpr std::array<unsigned, 15> choices = {
    0x33c3c6, 0x18cb9f, 0x167a2b, 0x39a617, 0x366eb7,
    0x3d2a6c, 0x1df6c4, 0x23ada0, 0x1dc4a0, 0x2e867b,
    0x0bfb9c, 0x205e05, 0x35f049, 0x1a675c, 0x2cfd44
};

using Regions = std::array<Mask, choices.size()>;
Regions make_regions() {
    Regions regions{};
    for (unsigned i = 0; i < regions.size(); ++i) {
        for (int x = 2; x <= 23; ++x) {
            regions[i] |= bit((choices[i] & bit(x - 2)) ? x : 48 - x);
        }
    }
    return regions;
}

// Exactly the simple paths from vertex to 1 using these steps and free interiors.
bool has_path(Mask steps, int vertex, Mask free_vertices) {
    if (std::has_single_bit(steps))
        return (vertex + std::countr_zero(steps)) % p == 1;
    for (Mask left = steps; left; left &= left - 1) {
        const int x = std::countr_zero(left);
        const int next = (vertex + x) % p;
        if ((free_vertices & bit(next)) &&
            has_path(steps ^ bit(x), next, free_vertices ^ bit(next))) return true;
    }
    return false;
}

unsigned certify(Mask alphabet, bool extend_at_one, const Regions& regions) {
    unsigned count = 0;
    // Descending submasks enumerate every nonempty subset of this alphabet.
    for (Mask steps = alphabet; steps; steps = (steps - 1) & alphabet) {
        int sum = 0;
        for (Mask left = steps; left; left &= left - 1) sum += std::countr_zero(left);
        if (sum % p != 1) continue;

        const Mask extra = (extend_at_one && (steps & bit(1))) ? bit(24) : 0;
        unsigned hits = 0;
        for (Mask region : regions) {
            if (has_path(steps, 0, region | extra) && ++hits == 8) break;
        }
        if (hits < 8) throw std::runtime_error("fewer than eight paths");
        ++count;
    }
    return count;
}

int main() {
    Mask squares = 0, nonsquares = 0;
    for (int x = 1; x < p; ++x) {
        const int square = x * x % p;
        squares |= bit(square);
        nonsquares |= bit(p - square);
    }
    const Regions regions = make_regions();
    const auto first = certify(squares, false, regions);
    const auto second = certify(nonsquares | bit(1), true, regions);
    if (first != 178481 || second != 356963) throw std::logic_error("unexpected counts");
    std::cout << "Sum-one subsets of the squares: " << first
              << "\nSum-one subsets of the nonsquares with 1 adjoined: " << second
              << "\nEvery subset passed in at least 8 of the 15 regions.\n";
}
