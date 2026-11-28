#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <fstream>
#include <string>
#include <stdexcept>
#include <vector>

using Edge = std::array<int, 4>;
using Domains = std::array<std::uint8_t, 78>;
constexpr int all_colors = 127;

struct Extension {
    std::vector<Edge> edges;
    std::array<std::vector<int>, 78> incident;
    std::uint64_t nodes = 0;

    Extension() {
        for (int d = 1; d <= 25; ++d) {
            for (int a = 0; a + 3 * d < 78; ++a) {
                Edge e{a, a + d, a + 2 * d, a + 3 * d};
                for (int i : e) incident[i].push_back(static_cast<int>(edges.size()));
                edges.push_back(e);
            }
        }
    }

    bool propagate(Domains& dom, std::vector<int>& queue) const {
        std::array<bool, 78> queued{};
        for (int i : queue) queued[i] = true;
        while (!queue.empty()) {
            int x = queue.back();
            queue.pop_back();
            queued[x] = false;
            for (int index : incident[x]) {
                const auto& e = edges[index];
                std::array<unsigned, 4> opts;
                unsigned single = 0, twice = 0, total = 0;
                for (int j = 0; j < 4; ++j) {
                    unsigned m = dom[e[j]];
                    opts[j] = m;
                    total |= m;
                    if (std::has_single_bit(m)) {
                        if (twice & m) return false; // Three fixed to one color.
                        twice |= single & m;
                        single |= m;
                    }
                }
                if (std::popcount(single) >= 3) continue; // The edge already has its colors.
                if (std::popcount(total) < 3) return false;
                for (int j = 0; j < 4; ++j) {
                    if (std::has_single_bit(opts[j])) continue;
                    unsigned rest = opts[(j+1)%4] | opts[(j+2)%4] | opts[(j+3)%4];
                    unsigned permitted = opts[j] & ~twice;
                    // If other vertices can supply only two colors, this
                    // vertex must be a third distinct color.
                    if (std::popcount(rest) <= 2) permitted &= ~rest;
                    if (!permitted) return false;
                    if (permitted != opts[j]) {
                        dom[e[j]] = static_cast<std::uint8_t>(permitted);
                        if (!queued[e[j]]) { queue.push_back(e[j]); queued[e[j]] = true; }
                    }
                }
            }
        }
        return true;
    }

    bool search(Domains dom, std::vector<int> queue) {
        ++nodes;
        if (!propagate(dom, queue)) return false;
        int position = -1, min_size = 8;
        for (int i = 0; i < 78; ++i) {
            int size = std::popcount(dom[i]);
            if (size > 1 && size < min_size) { min_size = size; position = i; }
        }
        if (position == -1) {
            for (const Edge& e : edges) {
                unsigned colors = 0;
                for (int i : e) colors |= dom[i];
                if (std::popcount(colors) < 3) throw std::logic_error("invalid witness");
            }
            for (auto m : dom) std::cout << std::countr_zero(m) << ' ';
            std::cout << '\n';
            return true;
        }
        // Any color still absent from all singleton domains and never selected
        // on this branch is interchangeable with the other unused colors.
        // Labels 0, 1, and 2 name the three retained classes.
        unsigned used = 7;
        for (unsigned mask : dom) if (std::has_single_bit(mask)) used |= mask;
        unsigned options = dom[position];
        unsigned unused = options & ~used;
        if (unused) options = (options & used) | (unused & -unused);
        for (unsigned m = options; m; m &= m-1) {
            dom[position] = static_cast<std::uint8_t>(m & -m);
            if (search(dom, {position})) return true;
        }
        return false;
    }
};

// Find every position whose deletion certifies this word. Leave all of them
// unrestricted when testing whether classes can be retained.
std::array<bool, 78> deletion_positions(const std::string& word, const std::vector<Edge>& edges) {
    std::array<bool, 78> positions;
    positions.fill(true);
    for (const auto& edge : edges) {
        unsigned colors = 0;
        for (int i : edge) colors |= 1u << (word[i] - '0');
        if (std::popcount(colors) >= 3) continue;
        for (int i = 0; i < 78; ++i)
            if (std::find(edge.begin(), edge.end(), i) == edge.end()) positions[i] = false;
    }
    return positions;
}

int main(int argc, char** argv) {
    if (argc > 2) return 2;
    std::ifstream input(argc == 2 ? argv[1] : "colorings.txt");
    if (!input) throw std::runtime_error("cannot read coloring data");
    Extension solver;
    std::string word;
    int words = 0, cases = 0;
    while (input >> word) {
        if (word.size() != 78 || word.find_first_not_of("0123456") != std::string::npos)
            throw std::runtime_error("expected 78 digits from 0 through 6");
        auto omitted = deletion_positions(word, solver.edges);
        if (std::none_of(omitted.begin(), omitted.end(), [](bool x) { return x; })) continue;
        ++words;
        for (unsigned mask = 1; mask < 128; ++mask) {
            int size = std::popcount(mask);
            if (size != 2 && size != 3) continue;
            if (size == 2) {
                // The two classes cannot take the same target color: some
                // progression would have at least three points of that color.
                bool forced_distinct = std::any_of(solver.edges.begin(), solver.edges.end(),
                    [&](const Edge& edge) {
                        int count = 0;
                        for (int i : edge)
                            if (!omitted[i] && (mask & (1u << (word[i] - '0')))) ++count;
                        return count >= 3;
                    });
                if (!forced_distinct) throw std::runtime_error("classes may merge");
                continue;
            }
            Domains dom;
            dom.fill(all_colors);
            std::vector<int> queue;
            for (int i = 0; i < 78; ++i) {
                unsigned bit = 1u << (word[i] - '0');
                if (omitted[i] || !(mask & bit)) continue;
                dom[i] = 1u << std::popcount(mask & (bit - 1));
                queue.push_back(i);
            }
            ++cases;
            if (solver.search(dom, queue)) {
                std::cout << "valid extension found for mask " << mask << '\n';
                return 1;
            }
        }
    }
    if (!words) throw std::runtime_error("no deletion witnesses");
    std::cout << "deletion words=" << words << " class triples=" << cases
              << " nodes=" << solver.nodes << " valid extensions=0\n";
}
