// Check simple cycles for zero-sum subsets, covering all dilations at 41 or 43.
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <string_view>
#include <vector>

using Mask = std::uint64_t;
#ifndef GRAHAM_PRIME
#define GRAHAM_PRIME 41
#endif
constexpr int prime = GRAHAM_PRIME, length = prime - 1, half = length / 2;
static_assert(prime == 41 || prime == 43);
constexpr int generator = prime == 41 ? 6 : 3;
constexpr Mask bit(int i) { return Mask{1} << i; }
constexpr Mask universe = bit(prime) - 2;
using Order = std::array<int, length>;
std::array<int, length> powers;

[[noreturn]] void fail(const char* reason, Mask set) {
    std::cerr << reason << " (residue mask " << set << ")\n";
    std::exit(EXIT_FAILURE);
}

bool find_cycle(Mask remaining, int current, Mask visited, Order& order, int index) {
    if (std::has_single_bit(remaining)) {
        order[index] = std::countr_zero(remaining);
        return (current + order[index]) % prime == 0;
    }
    for (Mask options = remaining; options; options &= options - 1) {
        const int step = std::countr_zero(options);
        const int next = (current + step) % prime;
        if (visited & bit(next)) continue;
        order[index] = step;
        if (find_cycle(remaining ^ bit(step), next, visited | bit(next), order, index + 1))
            return true;
    }
    return false;
}

void verify_cycle(Mask set, int size) {
    if (std::popcount(set) != size) fail("wrong cardinality", set);
    Order order;
    if (!find_cycle(set, 0, bit(0), order, 0)) fail("no cycle found", set);

    int sum = 0;
    Mask steps = 0, sums = 0;
    for (int j = 0; j < size; ++j) {
        const int step = order[j];
        if (step < 1 || step >= prime) fail("invalid residue", set);
        steps |= bit(step);
        sum = (sum + step) % prime;
        sums |= bit(sum);
    }
    if (sum != 0 || steps != set || std::popcount(sums) != size) fail("invalid cycle", set);
}

struct Enumeration {
    int size;
    int omitted;
    std::array<std::array<std::vector<Mask>, prime>, length + 1> left_halves{};
    std::uint64_t verified = 0;

    // Walk forward from the left endpoint and backward from the right endpoint.
    // The omission counts fix the meeting height; the sums fix the residue.
    void half_words(bool from_right, int depth, int height, int count, int sum, Mask missing) {
        if (height < 0 || count > omitted || depth - count > size) return;
        if (depth == half) {
            const int residue = sum % prime;
            if (from_right) {
                for (Mask left : left_halves[omitted - count][(prime - residue) % prime]) {
                    verify_cycle(universe ^ (left | missing), size);
                    ++verified;
                }
            } else {
                left_halves[count][residue].push_back(missing);
            }
            return;
        }
        const int d = powers[from_right ? length - 1 - depth : depth];
        const int direction = from_right ? -1 : 1;
        half_words(from_right, depth + 1, height - direction * omitted, count, sum, missing);
        half_words(from_right, depth + 1, height + direction * size, count + 1, sum + d,
                   missing | bit(d));
    }

    std::uint64_t run() {
        half_words(false, 0, 0, 0, 0, 0);
        half_words(true, 0, 0, 0, 0, 0);
        return verified;
    }
};

int main(int argc, char** argv) {
    const bool all_sizes = argc == 2 && std::string_view(argv[1]) == "--all";
    if (argc > 1 && !all_sizes) {
        std::cerr << "usage: verify_zero_sum [--all]\n";
        return EXIT_FAILURE;
    }
    int d = 1;
    Mask generated = 0;
    for (int& power : powers) {
        power = d;
        generated |= bit(d);
        d = generator * d % prime;
    }
    if (generated != universe || d != 1) fail("bad generator", generated);

    const int first = all_sizes ? 2 : 27;
    const int last = all_sizes ? length - 2 : 27;
#ifdef _OPENMP
    #pragma omp parallel for schedule(dynamic, 1)
#endif
    for (int size = first; size <= last; ++size) {
        Enumeration enumeration{size, length - size};
        const auto verified = enumeration.run();
        if (prime == 41 && size == 27 && verified != 7337331) fail("wrong size-27 count", 0);
#ifdef _OPENMP
        #pragma omp critical
#endif
        {
            if (all_sizes)
                std::cout << size << ' ' << verified << std::endl;
            else
                std::cout << verified << (prime == 41
                    ? " zero-sum dilation classes verified, one cycle per class\n"
                    : " zero-sum representatives verified, one cycle per subset\n");
        }
    }
}
