// Prove Graham's conjecture modulo 47 by joining two paths with disjoint interiors.
// See modulo-47.md for the reduction to the three products checked by main().
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <random>
#include <vector>

using Mask = std::uint64_t;
constexpr int prime = 47;
constexpr int regions = 32;
constexpr Mask bit(int x) { return Mask{1} << x; }
constexpr Mask field = bit(prime) - 1;

[[noreturn]] void fail(const char* message, Mask steps = 0) {
    std::cerr << message << " (residue mask " << steps << ")\n";
    std::exit(EXIT_FAILURE);
}

Mask negative(Mask set) {
    Mask result = 0;
    for (; set; set &= set - 1) result |= bit(prime - std::countr_zero(set));
    return result;
}

// Choose one vertex from each two-element orbit of v -> target-v,
// excluding the endpoints and the midpoint. Always verify disjointness.
std::array<Mask, regions> make_regions(int target) {
    std::mt19937 generator(prime + target);
    std::array<Mask, regions> result{};
    for (Mask& region : result) {
        auto choices = generator();
        Mask reflected = 0;
        for (int v = 1; v < prime; ++v) {
            const int other = (prime + target - v) % prime;
            if (other <= v) continue;
            region |= bit((choices & 1) ? v : other);
            reflected |= bit((choices & 1) ? other : v);
            choices >>= 1;
        }
        if ((region & reflected) || ((region | reflected) & (bit(0) | bit(target))) ||
            std::popcount(region) != 22) fail("invalid region");
    }
    return result;
}

// Only a returned and replayed witness counts. A search budget can reduce
// the number of regions certified for a set, without certifying a false one.
bool search(Mask remaining, int pos, Mask free, int target, int* order, int& budget) {
    if (budget == 0) return false;
    --budget;
    if (std::has_single_bit(remaining)) {
        *order = std::countr_zero(remaining);
        return (pos + *order) % prime == target;
    }
    // The allowed next steps are the unused residues in free-pos modulo 47.
    Mask options = remaining & ((free >> pos) | (free << (prime - pos)));
    for (; options && budget; options &= options - 1) {
        const int step = std::countr_zero(options);
        const int next = (pos + step) % prime;
        *order = step;
        if (search(remaining ^ bit(step), next, free ^ bit(next), target,
                   order + 1, budget)) return true;
    }
    return false;
}

bool has_path(Mask steps, int target, Mask interior, int budget) {
    const int size = std::popcount(steps);
    if (size == 0 || size > std::popcount(interior) + 1) return false;
    std::array<int, prime - 1> order{};
    if (!search(steps, 0, interior, target, order.data(), budget)) return false;
    Mask unused = steps, visited = bit(0);
    int pos = 0;
    for (int i = 0; i < size; ++i) {
        const int step = order[i];
        if (step < 1 || step >= prime || !(unused & bit(step))) fail("bad step", steps);
        unused ^= bit(step);
        pos = (pos + step) % prime;
        if (i + 1 < size && ((visited & bit(pos)) || !(interior & bit(pos))))
            fail("bad internal vertex", steps);
        visited |= bit(pos);
    }
    if (unused || pos != target) fail("bad endpoint", steps);
    return true;
}

struct Half {
    Mask steps;
    std::uint32_t regions_used;
};
using Groups = std::array<std::vector<Half>, regions + 1>;

// Bit j of word selects the residue 2^j mod 47. Hence the subset sum is
// word mod 47, and a single arithmetic progression enumerates the whole layer.
Groups classify_subsets(const std::array<Mask, 23>& digits, int sum, Mask extra,
                        int target, const std::array<Mask, regions>& allowed) {
    Groups groups;
    for (unsigned word = sum; word < (1u << digits.size()); word += prime) {
        Mask steps = extra;
        for (unsigned ones = word; ones; ones &= ones - 1)
            steps |= digits[std::countr_zero(ones)];
        std::uint32_t found = 0;
        for (int i = 0; i < regions; ++i) {
            if (has_path(steps, target, allowed[i], 256))
                found |= std::uint32_t{1} << i;
        }
        groups[std::popcount(found)].push_back({steps, found});
    }
    return groups;
}

void verify_pairs(const Groups& left, const Groups& right, const char* label,
                  std::uint64_t expected) {
    std::uint64_t pairs = 0, direct = 0;
    for (int i = 0; i <= regions; ++i) {
        for (int j = 0; j <= regions; ++j) {
            pairs += std::uint64_t(left[i].size()) * right[j].size();
            if (i + j > regions) continue; // necessarily share a region
            for (const Half& x : left[i]) {
                for (const Half& y : right[j]) {
                    if (x.regions_used & y.regions_used) continue;
                    const Mask neg_y = negative(y.steps);
                    if (x.steps & neg_y) fail("overlapping step sets");
                    const Mask steps = x.steps | neg_y;
                    if (!has_path(steps, 0, field ^ bit(0), 1000000))
                        fail("no direct cycle certified", steps);
                    ++direct;
                }
            }
        }
    }
    if (pairs != expected) fail("unexpected pair count");
    std::cout << label << ": " << pairs << " ordered pairs, " << direct
              << " direct cycles\n";
}

int main() {
    std::array<Mask, 23> digits;
    Mask squares = 0;
    int power = 1;
    for (Mask& digit : digits) {
        digit = bit(power);
        squares |= digit;
        power = 2 * power % prime;
    }
    if (power != 1 || (squares & negative(squares)) ||
        (squares | negative(squares)) != (field ^ bit(0))) fail("invalid powers of two");
    for (const int target : {1, prime - 1}) {
        const auto allowed = make_regions(target);
        const Groups normal = classify_subsets(digits, target, 0, target, allowed);
        verify_pairs(normal, normal, target == 1 ? "sum 1" : "sum -1", 178481ULL * 178481);
        if (target == prime - 1) {
            const Groups shifted = classify_subsets(digits, 0, bit(prime - 1), target, allowed);
            Groups without_one;
            for (int i = 0; i <= regions; ++i)
                for (const Half& half : normal[i])
                    if (!(half.steps & bit(1))) without_one[i].push_back(half);
            verify_pairs(without_one, shifted, "sum 0 after transfer", 89241ULL * 178482);
        }
    }
    std::cout << "All zero-sum subsets modulo 47 covered, including the empty set.\n";
}
