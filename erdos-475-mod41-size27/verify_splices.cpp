// Verify Graham's rearrangement conjecture modulo 47 by inserting opposite pairs
// into cycles. A successful insertion on each of r different edges proves all
// 2^r choices at once: omitting an insertion just deletes two cycle vertices.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

namespace {
using Mask = std::uint64_t;
using Magnitudes = std::uint32_t;
constexpr int prime = 47;
constexpr int half = (prime - 1) / 2;
constexpr Mask bit(int x) { return Mask{1} << x; }
constexpr Magnitudes magnitudeBit(int x) { return Magnitudes{1} << x; }
constexpr Mask field = bit(prime) - 1;
using Order = std::array<int, prime - 1>;

[[noreturn]] void fail(const char* message, Mask steps = 0) {
    std::cerr << message << " (residue mask " << steps << ")\n";
    std::exit(EXIT_FAILURE);
}

int mod(int x) {
    const int r = x % prime;
    return r < 0 ? r + prime : r;
}

Mask translate(Mask values, int offset) {
    return ((values << offset) | (values >> (prime - offset))) & field;
}

// Each magnitude x contributes no singleton, +x, or -x to the core.
// Group each half by its ordinary and reciprocal sums for the join.
struct HalfCore {
    Mask singletons;
    Magnitudes freePairs;
    int cubeSum;
};
using Table = std::array<std::array<std::vector<HalfCore>, prime>, prime>;

void listHalf(Table& table, const std::array<int, prime>& inverse, int x, int last,
              Mask singletons, Magnitudes freePairs, int sum, int reciprocals, int cubes) {
    if (x > last) {
        table[mod(sum)][mod(reciprocals)].push_back({singletons, freePairs, mod(cubes)});
        return;
    }
    listHalf(table, inverse, x + 1, last, singletons, freePairs | magnitudeBit(x),
             sum, reciprocals, cubes);
    const int cube = x * x * x % prime;
    listHalf(table, inverse, x + 1, last, singletons | bit(x), freePairs,
             sum + x, reciprocals + inverse[x], cubes + cube);
    listHalf(table, inverse, x + 1, last, singletons | bit(prime - x), freePairs,
             sum - x, reciprocals - inverse[x], cubes - cube);
}

// A zero-sum set needs a simple cycle returning to zero on the last step.
bool findCycle(Mask left, int vertex, Mask visited, Order& order, int index) {
    if (std::has_single_bit(left)) {
        const int step = std::countr_zero(left);
        order[index] = step;
        return (vertex + step) % prime == 0;
    }
    for (Mask choices = left; choices; choices &= choices - 1) {
        const int step = std::countr_zero(choices);
        const int next = (vertex + step) % prime;
        if (visited & bit(next)) continue;
        order[index] = step;
        if (findCycle(left ^ bit(step), next, visited | bit(next), order, index + 1))
            return true;
    }
    return false;
}

// Replay both the base cycle and the cycle with every optional pair inserted.
class CycleCheck {
public:
    void append(int step) {
        if (step <= 0 || step >= prime || (steps & bit(step)) || (vertices & bit(current)))
            fail("invalid cycle", steps);
        steps |= bit(step);
        vertices |= bit(current);
        current = (current + step) % prime;
    }

    void finish(Mask expected) const {
        if (steps != expected || current != 0) fail("wrong steps or endpoint", steps);
    }

    Mask visited() const { return vertices; }
    int position() const { return current; }

private:
    Mask steps = 0, vertices = 0;
    int current = 0;
};

struct Splice {
    // Resources are the base-edge start and the two new off-cycle vertices.
    Mask resources;
    int edge;
    int offset;
};
struct Options {
    int magnitude;
    int count = 0;
    std::array<Splice, 2 * (prime - 1)> choices;
};

bool assignSplices(Options* const* remaining, int count, Mask reserved,
                   Splice* selected, int& budget) {
    if (count == 0) return true;
    if (--budget < 0) return false;
    const Options& options = *remaining[0];
    for (int i = 0; i < options.count; ++i) {
        const Splice candidate = options.choices[i];
        if (candidate.resources & reserved) continue;
        *selected = candidate;
        if (assignSplices(remaining + 1, count - 1, reserved | candidate.resources,
                          selected + 1, budget))
            return true;
        if (budget <= 0) break;
    }
    return false;
}

// Try one cycle for "base". If one pair has few insertion choices, return it
// in splitAt so the caller can branch on its absence and presence.
bool certifyFamily(Mask base, Magnitudes freePairs, int& splitAt) {
    const int n = std::popcount(base);
    const int r = std::popcount(freePairs);
    if (r > n) return false;  // Each insertion needs its own base edge.
    if (n == 0) return true;  // Here r is also zero.

    Order order;
    if (!findCycle(base, 0, bit(0), order, 0)) fail("no cycle for base", base);
    CycleCheck original;
    std::array<Mask, prime - 1> edges, starts;
    for (int i = 0; i < n; ++i) {
        starts[i] = bit(original.position());
        original.append(order[i]);
        edges[i] = starts[i] | bit(original.position());
    }
    original.finish(base);
    if (!freePairs) return true;

    std::array<Options, half> options;
    std::array<Options*, half> byCount;
    int used = 0;
    int smallest = 2 * n + 1;
    for (Magnitudes pairs = freePairs; pairs; pairs &= pairs - 1) {
        const int x = std::countr_zero(pairs);
        Options& list = options[used];
        list.magnitude = x;
        byCount[used++] = &list;
        for (int offset : {x, prime - x}) {
            const Mask eligible = translate(field ^ original.visited(), prime - offset);
            for (int i = 0; i < n; ++i) {
                // Both endpoints of this edge must shift to unused vertices.
                if ((edges[i] & eligible) != edges[i]) continue;
                list.choices[list.count++] = {
                    starts[i] | translate(edges[i], offset), i, offset};
            }
        }
        if (list.count < smallest) {
            smallest = list.count;
            splitAt = x;
        }
        if (list.count == 0) return false;
    }
    std::sort(byCount.begin(), byCount.begin() + r, [](const Options* a, const Options* b) {
        if (a->count != b->count) return a->count < b->count;
        return a->magnitude < b->magnitude;
    });
    std::array<Splice, half> selected;
    // A cutoff only selects when to split. Both halves of a split are verified.
    int budget = 75;
    if (!assignSplices(byCount.data(), r, 0, selected.data(), budget)) return false;

    // Check the actual steps with integer addition, independently of the
    // rotated bit masks used to choose insertions. Replacing d by x,d,-x has
    // the same net effect, so every subcollection preserves a simple cycle.
    std::array<int, prime - 1> offsets{};
    Mask allSteps = base;
    Magnitudes replayedPairs = 0;
    for (int j = 0; j < r; ++j) {
        const int edge = selected[j].edge;
        const int offset = selected[j].offset;
        const int x = byCount[j]->magnitude;
        if (edge < 0 || edge >= n || (offset != x && offset != prime - x) || offsets[edge] != 0)
            fail("invalid insertion assignment", base);
        offsets[edge] = offset;
        allSteps |= bit(x) | bit(prime - x);
        replayedPairs |= magnitudeBit(x);
    }
    if (replayedPairs != freePairs) fail("wrong set of optional pairs", base);
    CycleCheck expanded;
    for (int i = 0; i < n; ++i) {
        const int offset = offsets[i];
        if (offset) expanded.append(offset);
        expanded.append(order[i]);
        if (offset) expanded.append(prime - offset);
    }
    expanded.finish(allSteps);
    return true;
}

struct Counts {
    std::uint64_t cores = 0, certificates = 0, splits = 0;
    std::uint64_t normalizedSets = 0, allSets = 0;
};

std::uint64_t coverFamily(Mask base, Magnitudes freePairs, Counts& counts) {
    int splitAt = freePairs ? std::countr_zero(freePairs) : 0;
    if (certifyFamily(base, freePairs, splitAt)) {
        ++counts.certificates;
        return bit(std::popcount(freePairs));
    }
    if (!(freePairs & magnitudeBit(splitAt))) fail("cannot split family", base);
    ++counts.splits;
    const Magnitudes rest = freePairs ^ magnitudeBit(splitAt);
    const auto without = coverFamily(base, rest, counts);
    const auto with = coverFamily(base | bit(splitAt) | bit(prime - splitAt), rest, counts);
    return without + with;
}

void checkCore(const HalfCore& left, const HalfCore& right, int reciprocalSum,
               std::array<Counts, half + 1>& rows) {
    const int cubeSum = (left.cubeSum + right.cubeSum) % prime;
    // When the reciprocal sum vanishes, normalize a nonzero cube sum to 1.
    // Cubing is a bijection on the 46 nonzero residues.
    if (reciprocalSum == 0 && cubeSum > 1) return;
    const Mask base = left.singletons | right.singletons;
    const Magnitudes pairs = left.freePairs | right.freePairs;
    Counts& counts = rows[std::popcount(base)];
    ++counts.cores;
    const auto represented = coverFamily(base, pairs, counts);
    if (represented != bit(std::popcount(pairs))) fail("family count mismatch", base);
    counts.normalizedSets += represented;
    // A nonzero reciprocal or cube sum selects exactly one scalar per orbit.
    // If both sums vanish, the enumeration visits every core without scaling.
    counts.allSets += represented * (reciprocalSum || cubeSum ? prime - 1 : 1);
}
}  // namespace

int main() {
    std::array<int, prime> inverse{};
    for (int x = 1; x < prime; ++x)
        for (int y = 1; y < prime; ++y)
            if (x * y % prime == 1) inverse[x] = y;

    Table left, right;
    listHalf(left, inverse, 1, half / 2, 0, 0, 0, 0, 0);
    listHalf(right, inverse, half / 2 + 1, half, 0, 0, 0, 0, 0);
    std::array<Counts, half + 1> rows{};
    for (int sum = 0; sum < prime; ++sum) {
        for (int reciprocals = 0; reciprocals < prime; ++reciprocals) {
            for (int target : {0, 1}) {
                const auto& matches = right[mod(-sum)][mod(target - reciprocals)];
                for (const HalfCore& a : left[sum][reciprocals])
                    for (const HalfCore& b : matches) checkCore(a, b, target, rows);
            }
        }
    }
    std::cout << "singletons cores certificates splits normalized_sets zero_sum_sets\n";
    std::uint64_t total = 0;
    for (int k = 0; k <= half; ++k) {
        const Counts& c = rows[k];
        std::cout << k << ' ' << c.cores << ' ' << c.certificates << ' ' << c.splits
                  << ' ' << c.normalizedSets << ' ' << c.allSets << '\n';
        total += c.allSets;
    }
    // Nontrivial additive characters each contribute 1 to the zero-sum count.
    const auto expected = (bit(prime - 1) + prime - 1) / prime;
    if (total != expected) fail("total zero-sum count mismatch");
    std::cout << "All " << total << " zero-sum subsets covered.\n";
}
