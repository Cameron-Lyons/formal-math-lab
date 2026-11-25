#include <array>
#include <bit>
#include <cstdint>
#include <cstdio>

// Does any sequence of at most two backward edges per vertex give an
// eleven-vertex C4,C8-free graph with at least 16 edges?
constexpr int order = 11, budget = 6;
using Mask = unsigned;
std::array<Mask, order> neighbors{};
std::array<std::uint64_t, order+1> counts{};

void endpoints(int v, Mask used, int length, Mask &blocked) {
    if (length == 2 || length == 6) blocked |= 1U << v;
    if (length == 6) return;
    for (auto next = neighbors[v] & ~used; next; next &= next - 1) {
        int w = std::countr_zero(next);
        endpoints(w, used | (1U << w), length + 1, blocked);
    }
}
void enumerate(int n, int deficit) {
    ++counts[n];
    if (n == order) return;
    auto visit = [&](Mask mask, int cost) {
        if (deficit + cost > budget) return;
        neighbors[n] = mask;
        for (Mask s = mask; s; s &= s-1) neighbors[std::countr_zero(s)] |= 1U << n;
        enumerate(n+1, deficit+cost);
        for (Mask s = mask; s; s &= s-1) neighbors[std::countr_zero(s)] ^= 1U << n;
        neighbors[n] = 0;
    };
    visit(0, 2);
    for (int i = 0; i < n; ++i) {
        visit(1U << i, 1);
        Mask blocked = 0;
        endpoints(i, 1U << i, 0, blocked);
        for (int j = i+1; j < n; ++j)
            if (!(blocked & (1U << j))) visit((1U << i) | (1U << j), 0);
    }
}
int main() {
    enumerate(0, 0);
    for (int n = 0; n <= order; ++n) std::printf("%d %llu\n", n, static_cast<unsigned long long>(counts[n]));
    return counts[order] != 0;
}
