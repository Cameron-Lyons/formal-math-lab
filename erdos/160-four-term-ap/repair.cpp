// Search all seven-color words within a given number of edits of Canli's
// length-77 witness followed by color 4. See README.md for the pruning proof.
#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

constexpr int length = 78;
constexpr int colors = 7;
using Positions = std::bitset<length>;
using Word = std::array<int, length>;

constexpr Word initial{
    1,1,6,2,1,1,0,4,4,6,3,5,3,4,5,2,1,2,0,3,3,4,2,2,5,0,
    5,6,6,0,4,3,4,6,3,1,5,1,3,5,2,0,2,1,1,0,4,2,2,5,4,5,
    6,6,0,4,1,4,6,3,1,5,0,4,0,3,3,1,2,6,2,1,6,2,5,2,0,4
};

// Each four-color pattern uses four 3-bit fields. Return zero if it already
// uses three colors, or a set of entries at least one of which must change.
unsigned conflict(int pattern) {
    std::array<unsigned, 8> groups{};
    for (int j = 0; j < 4; ++j) groups[(pattern >> (3 * j)) & 7] |= 1u << j;
    int distinct = 0;
    for (unsigned group : groups) {
        if (std::popcount(group) >= 3) return group == 15 ? 7 : group;
        if (group) ++distinct;
    }
    return distinct < 3 ? 15 : 0;
}

struct Progression {
    std::array<int, 4> points{};
    std::array<Positions, 16> subsets{};
    int pattern = 0;
    int bad_index = -1;
};

struct Occurrence {
    int progression;
    int shift;
};

class RepairSearch {
    const Word start;
    Word word;
    std::vector<Progression> aps;
    std::array<std::vector<Occurrence>, length> through;
    std::array<unsigned, 4096> conflicts{};
    std::vector<int> bad;

    void recolor(int position, int color) {
        int old = word[position];
        int changed_bits = old ^ color;
        word[position] = color;
        for (auto [id, shift] : through[position]) {
            auto& ap = aps[id];
            ap.pattern ^= changed_bits << shift;
            if (conflicts[ap.pattern] && ap.bad_index < 0) {
                ap.bad_index = static_cast<int>(bad.size());
                bad.push_back(id);
            } else if (!conflicts[ap.pattern] && ap.bad_index >= 0) {
                int last = bad.back();
                bad[ap.bad_index] = last;
                aps[last].bad_index = ap.bad_index;
                bad.pop_back();
                ap.bad_index = -1;
            }
        }
    }

    bool search(int edits, Positions available) {
        ++nodes;
        if (bad.empty()) return true;
        if (edits == 0) return false;
        Positions branch;
        // Disjoint conflicts need distinct edits. At equality all remaining
        // edits must lie inside their union. Repeat if that shrank the domain.
        while (true) {
            Positions packed;
            int needed = 0;
            unsigned smallest = 5;
            for (int id : bad) {
                const auto& ap = aps[id];
                Positions candidates = ap.subsets[conflicts[ap.pattern]] & available;
                unsigned size = candidates.count();
                if (!size) return false;
                if (size < smallest) {
                    branch = candidates;
                    smallest = size;
                }
                if ((candidates & packed).none()) {
                    if (++needed > edits) return false;
                    packed |= candidates;
                }
            }
            if (needed < edits || packed == available) break;
            available = packed;
        }
        for (int position = 0; position < length; ++position) {
            if (!branch[position]) continue;
            // Partition by the first entry of this conflict changed by a repair.
            available.reset(position);
            int original = word[position];
            for (int color = 0; color < colors; ++color) {
                if (color == original) continue;
                recolor(position, color);
                if (search(edits - 1, available)) return true;
            }
            recolor(position, original);
        }
        return false;
    }

public:
    std::uint64_t nodes = 0;
    explicit RepairSearch(const Word& seed) : start(seed), word(seed) {
        for (int pattern = 0; pattern < 4096; ++pattern) conflicts[pattern] = conflict(pattern);
        for (int d = 1; 3*d < length; ++d) {
            for (int a = 0; a + 3*d < length; ++a) {
                int id = static_cast<int>(aps.size());
                Progression ap;
                for (int j = 0; j < 4; ++j) {
                    int position = a + j*d;
                    ap.points[j] = position;
                    ap.pattern |= word[position] << (3*j);
                    through[position].push_back({id, 3*j});
                    for (unsigned mask = 0; mask < 16; ++mask) {
                        if (mask & (1u << j)) ap.subsets[mask].set(position);
                    }
                }
                if (conflicts[ap.pattern]) {
                    ap.bad_index = static_cast<int>(bad.size());
                    bad.push_back(id);
                }
                aps.push_back(ap);
            }
        }
        if (aps.size() != 975) throw std::runtime_error("unexpected progression count");
        if (start == initial && (bad.size() != 1 ||
            aps[bad.front()].points != std::array<int,4>{2,27,52,77}))
            throw std::runtime_error("unexpected witness or progression list");
    }
    bool run(int edits) {
        Positions available;
        if (!search(edits, available.set())) return false;
        // Verify a positive result independently of the incremental state.
        int distance = 0;
        for (int i = 0; i < length; ++i) distance += word[i] != start[i];
        if (distance > edits) throw std::runtime_error("edit budget exceeded");
        for (const auto& ap : aps) {
            unsigned mask = 0;
            for (int x : ap.points) mask |= 1u << word[x];
            if (std::popcount(mask) < 3) throw std::runtime_error("invalid coloring");
        }
        for (int c : word) std::cout << c << ' ';
        std::cout << '\n';
        return true;
    }
};

int main(int argc, char** argv) {
    if (argc > 3) return 2;
    int edits = argc >= 2 ? std::stoi(argv[1]) : 18;
    if (edits < 0 || edits > length) throw std::invalid_argument("expected 0 to 78 edits");
    Word seed = initial;
    if (argc == 3) {
        std::string digits = argv[2];
        if (digits.size() != length || digits.find_first_not_of("0123456") != std::string::npos)
            throw std::invalid_argument("expected 78 digits from 0 through 6");
        for (int i = 0; i < length; ++i) seed[i] = digits[i] - '0';
    }
    RepairSearch search(seed);
    bool found = search.run(edits);
    std::cout << "radius=" << edits << " nodes=" << search.nodes
              << " valid_repair=" << (found ? "yes" : "no") << '\n';
}
