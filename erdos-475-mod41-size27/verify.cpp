// Check every 27-element subset of the nonzero residues with total 0 or 1.
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>

using Mask = std::uint64_t;
using Order = std::array<int, 27>;
constexpr Mask bit(int x) { return Mask{1} << x; }
constexpr Mask all_residues = bit(41) - 2; // Bits 1 through 40.

bool find_order(Mask remaining, int sum, Mask seen, Order& order, int index) {
    for (Mask choices = remaining; choices; choices &= choices - 1) {
        const int step = std::countr_zero(choices);
        const int next = (sum + step) % 41;
        const Mask rest = remaining ^ bit(step);
        order[index] = step;
        if (rest == 0) return true; // The last step reaches the reserved endpoint.
        if (!(seen & bit(next)) && find_order(rest, next, seen | bit(next), order, index + 1))
            return true;
    }
    return false;
}

void check(Mask set, int endpoint) {
    Order order{};
    if (!find_order(set, 0, bit(0) | bit(endpoint), order, 0)) std::abort();

    Mask steps = 0, sums = 0;
    int sum = 0;
    for (int step : order) {
        steps |= bit(step);
        sum = (sum + step) % 41;
        sums |= bit(sum);
        if (sum == 0 && steps != set) std::abort();
    }
    if (steps != set || std::popcount(sums) != 27 || sum != endpoint) std::abort();
}

std::uint64_t enumerate(int first, int omissions, int sum, Mask set) {
    if (omissions == 1) {
        std::uint64_t count = 0;
        for (int endpoint : {0, 1}) {
            const int last = (sum - endpoint + 41) % 41;
            if (last >= first) {
                check(set ^ bit(last), endpoint);
                ++count;
            }
        }
        return count;
    }
    std::uint64_t count = 0;
    for (int x = first; x <= 41 - omissions; ++x)
        count += enumerate(x + 1, omissions - 1, (sum + 41 - x) % 41, set ^ bit(x));
    return count;
}

int main() {
    // The full set has sum 0. Choose the 13 omissions in increasing order.
    std::uint64_t count = 0;
#ifdef _OPENMP
    #pragma omp parallel for schedule(dynamic, 1) reduction(+:count)
#endif
    for (int x = 1; x <= 28; ++x)
        count += enumerate(x + 1, 12, 41 - x, all_residues ^ bit(x));
    std::cout << count << " sets verified\n";
    return count == 586986481 ? EXIT_SUCCESS : EXIT_FAILURE;
}
