// Check the zero-sum subsets modulo 41 whose reciprocal sum is 0 or 1.
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

constexpr int p = 41;
using Mask = std::uint64_t;
using Table = std::array<std::array<std::vector<Mask>, p>, p>;
constexpr Mask bit(int x) { return Mask{1} << x; }

// Group the subsets of [first,last] by their sum and their reciprocal sum.
Table subsets(int first, int last) {
    Table groups;
    std::array<int, p> inverse{};
    for (int x = first; x <= last; ++x) {
        int y = 1;
        while (x * y % p != 1) ++y;
        inverse[x] = y;
    }
    auto visit = [&](auto& self, int x, Mask set, int sum, int reciprocals) -> void {
        if (x > last) {
            groups[sum][reciprocals].push_back(set);
            return;
        }
        self(self, x + 1, set, sum, reciprocals);
        self(self, x + 1, set | bit(x), (sum + x) % p, (reciprocals + inverse[x]) % p);
    };
    visit(visit, first, 0, 0, 0);
    return groups;
}

// Try each unused step whose nonempty partial sum has not occurred before.
bool find_order(Mask unused, int position, Mask sums, int* order) {
    if (unused == 0) return position == 0;
    for (Mask choices = unused; choices; choices &= choices - 1) {
        const int step = std::countr_zero(choices);
        const int next = (position + step) % p;
        if (sums & bit(next)) continue;
        if (next == 0 && unused != bit(step)) continue;
        *order = step;
        if (find_order(unused ^ bit(step), next, sums | bit(next), order + 1))
            return true;
    }
    return false;
}

// Replay the returned steps independently of the search's visited mask.
bool verified(Mask set) {
    std::array<int, p - 1> order;
    if (!find_order(set, 0, 0, order.data())) return false;
    const int size = std::popcount(set);
    Mask steps = 0, sums = 0;
    int position = 0;
    for (int i = 0; i < size; ++i) {
        const int step = order[i];
        if (step < 1 || step >= p) return false;
        steps |= bit(step);
        position = (position + step) % p;
        sums |= bit(position);
    }
    return position == 0 && steps == set && std::popcount(sums) == size;
}

int main() {
    const Table left = subsets(1, 20), right = subsets(21, 40);
    std::uint64_t checked = 0;
#ifdef _OPENMP
    #pragma omp parallel for collapse(2) reduction(+:checked)
#endif
    for (int s = 0; s < p; ++s) {
        for (int t = 0; t < p; ++t) {
            for (int target : {0, 1}) {
                const auto& matches = right[(p - s) % p][(p + target - t) % p];
                for (Mask a : left[s][t]) {
                    for (Mask b : matches) {
                        if (!verified(a | b)) {
                            std::cerr << "Failed on residue mask " << (a | b) << '\n';
                            std::exit(EXIT_FAILURE);
                        }
                        ++checked;
                    }
                }
            }
        }
    }
    std::cout << checked << " sets verified\n";
    // Independent subset counts for reciprocal sums 0 and 1, respectively.
    return checked == 654'162'296 + 654'079'862 ? EXIT_SUCCESS : EXIT_FAILURE;
}
