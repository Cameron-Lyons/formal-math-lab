// Independent, single-threaded proof of the zero-sum case used in the reduction.
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

using Mask = std::uint64_t;
constexpr int prime = 41, length = 40, half = 20, omitted = 13, size = 27;
constexpr Mask bit(int i) { return Mask{1} << i; }
constexpr Mask universe = bit(prime) - 2;
using Order = std::array<int, size>;

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

void verify_cycle(Mask set) {
    if (std::popcount(set) != size) fail("wrong cardinality", set);
    Order order{};
    if (!find_cycle(set, 0, bit(0), order, 0)) fail("no cycle found", set);

    int sum = 0;
    Mask steps = 0, sums = 0;
    for (int step : order) {
        if (step < 1 || step >= prime) fail("invalid residue", set);
        steps |= bit(step);
        sum = (sum + step) % prime;
        sums |= bit(sum);
    }
    if (sum != 0 || steps != set || std::popcount(sums) != size) fail("invalid cycle", set);
}

std::array<int, length> powers;
std::array<std::array<std::vector<Mask>, prime>, omitted + 1> left_halves;
std::uint64_t verified = 0;

// Read the left half from the start and the right half backwards from the end.
// Both walks start at height 0 and stay nonnegative. The omission count
// determines the meeting height, and the residue sum determines the endpoint.
void half_words(bool from_right, int depth, int height, int count, int sum, Mask missing) {
    if (height < 0 || count > omitted) return;
    if (depth == half) {
        const int residue = sum % prime;
        if (from_right) {
            for (Mask left : left_halves[omitted - count][(prime - residue) % prime]) {
                verify_cycle(universe ^ (left | missing));
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

int main() {
    int d = 1;
    Mask generated = 0;
    for (int& power : powers) {
        power = d;
        generated |= bit(d);
        d = 6 * d % prime;
    }
    if (generated != universe || d != 1) fail("bad generator", generated);
    half_words(false, 0, 0, 0, 0, 0);
    half_words(true, 0, 0, 0, 0, 0);
    if (verified != 7337331) fail("wrong zero-sum orbit count", 0);
    std::cout << verified << " zero-sum dilation classes verified, one cycle per class\n";
}
