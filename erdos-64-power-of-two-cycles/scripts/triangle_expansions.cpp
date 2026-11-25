// Search every choice of vertices to expand into triangles in each graph6 input.
// Each original edge uses its own port. A degree-two vertex leaves one free port.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using Mask = std::uint32_t;
static Mask bit(int v) { return Mask{1} << v; }

struct CycleRule {
    Mask vertices;
    Mask allowed_counts;
};

class TriangleSearch {
    int order;
    std::array<Mask, 30> neighbors{};
    std::vector<CycleRule> rules;

    void visit(int first, int second, int last, Mask path) {
        const int length = std::popcount(path);
        if (length >= 3 && second < last && (neighbors[last] & bit(first))) {
            // Each of the c expanded vertices can add either one or two edges.
            Mask allowed = 0;
            for (int c = 0; c <= length; ++c) {
                const auto low = static_cast<unsigned>(std::max(4, length + c));
                if (std::bit_ceil(low) > static_cast<unsigned>(length + 2*c))
                    allowed |= bit(c);
            }
            rules.push_back({path, allowed});
        }
        Mask choices = neighbors[last] & ~path & ~(bit(first + 1) - 1);
        while (choices) {
            const int next = std::countr_zero(choices);
            choices &= choices - 1;
            visit(first, length == 1 ? next : second, next, path | bit(next));
        }
    }

    std::uint64_t solve(Mask expanded, Mask unchanged, const std::string& base) const {
        for (;;) {
            Mask force_in = 0, force_out = 0;
            for (auto [cycle, allowed] : rules) {
                const Mask undecided = cycle & ~(expanded | unchanged);
                const int count = std::popcount(undecided);
                const int chosen = std::popcount(cycle & expanded);
                const Mask possible = (allowed >> chosen) & (bit(count + 1) - 1);
                if (!possible) return 0;
                if (possible == 1) force_out |= undecided;
                if (possible == bit(count)) force_in |= undecided;
            }
            if (force_in & force_out) return 0;
            if (!(force_in | force_out)) break;
            expanded |= force_in;
            unchanged |= force_out;
        }
        const Mask remaining = (bit(order) - 1) & ~(expanded | unchanged);
        if (!remaining) {
            std::cout << base << ' ' << expanded << '\n';
            return 1;
        }
        const Mask vertex = bit(std::countr_zero(remaining));
        return solve(expanded | vertex, unchanged, base) + solve(expanded, unchanged | vertex, base);
    }

public:
    explicit TriangleSearch(const std::string& base) {
        if (base.empty() || !std::all_of(base.begin(), base.end(),
            [](unsigned char c) { return c >= 63 && c <= 126; }))
            throw std::invalid_argument("invalid graph6 input");
        order = base.front() - 63;
        const auto size = static_cast<std::size_t>(1 + (order * (order - 1)/2 + 5)/6);
        if (order < 3 || order > 30 || base.size() != size)
            throw std::invalid_argument("expected headerless graph6 of order 3 through 30");
        int index = 0;
        for (int v = 1; v < order; ++v) {
            for (int u = 0; u < v; ++u, ++index) {
                if ((base[1 + index/6] - 63) & (32 >> (index%6))) {
                    neighbors[u] |= bit(v);
                    neighbors[v] |= bit(u);
                }
            }
        }
        for (int v = 0; v < order; ++v)
            if (std::popcount(neighbors[v]) > 3)
                throw std::invalid_argument("triangle replacement needs at most three ports");
    }

    std::uint64_t run(const std::string& base) {
        for (int v = 0; v < order; ++v) visit(v, v, v, bit(v));
        // Different cycles with the same vertex set yield identical count constraints.
        std::sort(rules.begin(), rules.end(), [](auto a, auto b) { return a.vertices < b.vertices; });
        rules.erase(std::unique(rules.begin(), rules.end(),
            [](auto a, auto b) { return a.vertices == b.vertices; }), rules.end());
        return solve(0, 0, base);
    }
};

int main() {
    std::uint64_t bases = 0, models = 0;
    std::string base;
    while (std::cin >> base) {
        models += TriangleSearch(base).run(base);
        ++bases;
    }
    std::cerr << "bases=" << bases << " models=" << models << '\n';
}
