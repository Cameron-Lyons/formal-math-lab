// Exhaustive nonexistence check for a 24-block (14,6,3) covering.
// Compile with c++ -O3 -std=c++20 verify_covering.cpp -o verify_covering
// and run ./verify_covering. No external libraries or input files are needed.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <map>
#include <set>
#include <stdexcept>
#include <vector>

using Mask = unsigned;
using Rows = std::vector<Mask>;
using Map = std::array<unsigned, 14>;
constexpr Mask link_points = (1u << 13) - 1;
constexpr Mask bit(unsigned i) { return 1u << i; }

std::vector<unsigned> members(Mask mask) {
    std::vector<unsigned> result;
    while (mask) {
        result.push_back(std::countr_zero(mask));
        mask &= mask - 1;
    }
    return result;
}

Mask image(Mask mask, const Map& map) {
    Mask result = 0;
    while (mask) {
        result |= bit(map[std::countr_zero(mask)]);
        mask &= mask - 1;
    }
    return result;
}

// Enumerate every bijection between the named points carrying each marked
// source row onto the corresponding target row (on those points).
template<class Visitor>
void bijections(const Rows& source, Mask from, const Rows& target, Mask to,
                Visitor visit) {
    auto cells = [](const Rows& marked, Mask points) {
        std::vector<std::vector<unsigned>> result(1u << marked.size());
        for (unsigned p : members(points)) {
            unsigned signature = 0;
            for (unsigned i = 0; i < marked.size(); ++i)
                if (marked[i] & bit(p)) signature |= bit(i);
            result[signature].push_back(p);
        }
        return result;
    };
    auto left = cells(source, from);
    auto right = cells(target, to);
    std::vector<unsigned> permutable;
    Map map{};
    for (unsigned i = 0; i < left.size(); ++i) {
        if (left[i].size() != right[i].size()) return;
        if (left[i].size() == 1) map[left[i][0]] = right[i][0];
        if (left[i].size() > 1) permutable.push_back(i);
    }
    auto assign = [&](auto& self, unsigned n) -> void {
        if (n == permutable.size()) { visit(map); return; }
        unsigned i = permutable[n];
        do {
            for (unsigned j = 0; j < left[i].size(); ++j)
                map[left[i][j]] = right[i][j];
            self(self, n + 1);
        } while (std::next_permutation(right[i].begin(), right[i].end()));
    };
    assign(assign, 0);
}

// Two points of multiplicity three can be normalized to labels 12 and 0.
// The first three rows contain 12. The next two are the other rows through 0.
// Up to exchanging the last two rows, s is 0, 1, or 2.
Rows marked_rows(unsigned s) {
    Mask b = ((1u << s) - 1) << 4;
    Mask c = ((1u << (4 - s)) - 1) << 8;
    return {bit(12) | 0x00f, bit(12) | 0x0f0, bit(12) | 0xf00,
            bit(0) | b | c, bit(0) | (0xff0 ^ (b | c))};
}

// Enumerate all normalized links of the given size. Only the pairs between distinct
// parts of {0..3}, {4..7}, {8..11} may still need covering.
class NormalizedLinks {
    using Edges = std::uint64_t;
    std::array<Edges, 12> incident{};
    std::array<std::array<Edges, 12>, 12> edge{};
    Edges all = 0;
    struct Choice { Mask row; Edges edges; };
    std::vector<Choice> choices;
    Rows selected;

    Edges covered(Mask row) const {
        Edges result = 0;
        for (unsigned i = 0; i < 12; ++i) if (row & bit(i))
            for (unsigned j = 0; j < i; ++j) if (row & bit(j))
                result |= edge[i][j];
        return result;
    }

    void search(unsigned start, unsigned left, Edges missing) {
        // A five-set has at most eight cross-part pairs (split 2+2+1).
        if (std::popcount(missing) > int(8 * left)) return;
        if (left == 1) {
            Mask endpoints = 0;
            for (unsigned i = 0; i < 12; ++i)
                if (missing & incident[i]) endpoints |= bit(i);
            if (std::popcount(endpoints) > 5) return;
            for (unsigned j = start; j < choices.size(); ++j) {
                if ((choices[j].row & endpoints) != endpoints) continue;
                Rows copy = selected;
                copy.push_back(choices[j].row);
                std::sort(copy.begin(), copy.end());
                by_case[shape].push_back(copy);
            }
            return;
        }
        unsigned necessary = 0;
        for (Edges e : incident)
            necessary += (std::popcount(missing & e) + 3) / 4;
        // A new row covers at most four missing edges at any one of its points.
        if (necessary > 5 * left) return;
        for (unsigned j = start; j + left <= choices.size(); ++j) {
            Edges next = missing & ~choices[j].edges;
            if (std::popcount(next) > int(8 * (left - 1))) continue;
            selected.push_back(choices[j].row);
            search(j + 1, left - 1, next);
            selected.pop_back();
        }
    }

    unsigned shape = 0;
public:
    std::array<std::vector<Rows>, 3> by_case;
    explicit NormalizedLinks(unsigned row_count) {
        unsigned n = 0;
        for (unsigned i = 0; i < 12; ++i)
            for (unsigned j = 0; j < i; ++j)
                if (i / 4 != j / 4) {
                    Edges e = Edges(1) << n++;
                    edge[i][j] = e; all |= e;
                    incident[i] |= e; incident[j] |= e;
                }
        for (Mask m = 0; m < bit(12); ++m)
            if (!(m & bit(0)) && std::popcount(m) == 5)
                choices.push_back({m, covered(m)});
        for (shape = 0; shape < 3; ++shape) {
            selected = marked_rows(shape);
            search(0, row_count - 5, all & ~covered(selected[3]) & ~covered(selected[4]));
        }
    }
};

// For a link representative, generate its complete orbit of normalized
// images. Choose both ordered multiplicity-three points and order their rows.
void add_normalized_images(const Rows& link, std::set<Rows>& seen) {
    std::vector<unsigned> tight;
    for (unsigned i = 0; i < 13; ++i) {
        unsigned n = 0;
        for (Mask b : link) if (b & bit(i)) ++n;
        if (n == 3) tight.push_back(i);
    }
    for (unsigned y : tight) for (unsigned z : tight) if (y != z) {
        Mask common = 0;
        Rows yy, zz;
        for (Mask b : link) {
            if ((b & bit(y)) && (b & bit(z))) common = b;
            else if (b & bit(y)) yy.push_back(b);
            else if (b & bit(z)) zz.push_back(b);
        }
        if (!common || yy.size() != 2 || zz.size() != 2)
            throw std::logic_error("invalid multiplicity-three pair");
        for (unsigned i = 0; i < 2; ++i) for (unsigned j = 0; j < 2; ++j) {
            Rows anchor{common, yy[i], yy[1-i], zz[j], zz[1-j]};
            for (unsigned s = 0; s <= 2; ++s) {
                bijections(anchor, link_points, marked_rows(s), link_points,
                    [&](const Map& map) {
                        Rows copy;
                        for (Mask b : link) copy.push_back(image(b, map));
                        std::sort(copy.begin(), copy.end());
                        seen.insert(copy);
                    });
            }
        }
    }
}

// Option for the low-degree center y, given the root link. Its rows through
// the root are already fixed, so store only its other (six-person) rows.
using Options = std::vector<Rows>;
Options extend_at(unsigned y, const Rows& common, const std::vector<Rows>& types) {
    std::set<Rows> options;
    for (const Rows& link : types) for (unsigned v = 0; v < 13; ++v) {
        Rows anchor, other;
        for (Mask b : link) ((b & bit(v)) ? anchor : other).push_back(b);
        if (anchor.size() != common.size()) continue;
        // v is to become the root, and y the center of this link.
        do {
            bijections(anchor, link_points ^ bit(v), common, link_points ^ bit(y),
                [&](const Map& map) {
                    Rows copy;
                    for (Mask b : other) copy.push_back(bit(y) | image(b, map));
                    std::sort(copy.begin(), copy.end());
                    options.insert(copy);
                });
        } while (std::next_permutation(anchor.begin(), anchor.end()));
    }
    return {options.begin(), options.end()};
}

// For fixed root, keep an option at y only if all but at most four other
// candidate centers can agree on their rows through y and that center.
bool compatible_root(const Rows& root_link, const std::vector<Rows>& types) {
    std::vector<unsigned> centers;
    std::array<Options, 13> options;
    for (unsigned y = 0; y < 13; ++y) {
        Rows common;
        for (Mask b : root_link) if (b & bit(y)) common.push_back(b);
        if (common.size() < 4) continue; // Ignoring these points weakens the test.
        centers.push_back(y);
        options[y] = extend_at(y, common, types);
    }

    using Signatures = std::array<unsigned, 13>;
    std::array<std::vector<Signatures>, 13> ids;
    std::array<std::array<unsigned,13>,13> distinct{};
    for (unsigned y : centers) ids[y].resize(options[y].size());
    for (unsigned a : centers) for (unsigned b : centers) if (a < b) {
        std::map<Rows,unsigned> intern;
        for (unsigned y : {a, b}) {
            unsigned z = (y == a) ? b : a;
            for (unsigned i = 0; i < options[y].size(); ++i) {
                Rows shared;
                for (Mask row : options[y][i]) if (row & bit(z)) shared.push_back(row);
                auto it = intern.emplace(shared, intern.size()).first;
                ids[y][i][z] = it->second;
            }
        }
        distinct[a][b] = distinct[b][a] = intern.size();
    }
    std::array<std::vector<char>, 13> live;
    for (unsigned y : centers) live[y].assign(options[y].size(), true);
    while (true) {
        std::array<std::array<std::vector<char>,13>,13> supported;
        for (unsigned y : centers) for (unsigned z : centers) if (y != z) {
            supported[y][z].resize(distinct[y][z], false);
            for (unsigned i = 0; i < live[y].size(); ++i)
                if (live[y][i]) supported[y][z][ids[y][i][z]] = true;
        }
        unsigned empty = 0;
        bool changed = false;
        for (unsigned y : centers) {
            unsigned count = 0;
            for (unsigned i = 0; i < live[y].size(); ++i) if (live[y][i]) {
                unsigned incompatible = 0;
                for (unsigned z : centers) if (y != z)
                    if (!supported[z][y][ids[y][i][z]]) ++incompatible;
                if (incompatible > 4) { live[y][i] = false; changed = true; }
                else ++count;
            }
            if (count == 0) ++empty;
        }
        if (empty > 4) return false;
        if (!changed) return true;
    }
}

int main() {
    // A 13-point pair covering with nine 5-sets has at least two points
    // of degree three: every degree is at least three and 9*5 < 13*4-1.
    // Any cover with fewer rows could be padded to nine distinct rows.
    NormalizedLinks nine(9);
    for (const auto& list : nine.by_case)
        if (!list.empty()) throw std::logic_error("nine-row link found");
    std::cout << "No nine-row link covers all pairs.\n";
    NormalizedLinks normalized(10);
    std::set<Rows> seen, enumerated;
    std::vector<Rows> types;
    std::cout << "Normalized links per case:";
    for (const auto& list : normalized.by_case) {
        std::cout << ' ' << list.size();
        for (const Rows& link : list) {
            enumerated.insert(link);
            if (seen.contains(link)) continue;
            types.push_back(link);
            add_normalized_images(link, seen);
        }
    }
    if (seen != enumerated)
        throw std::logic_error("normalization orbit and enumeration disagree");
    std::cout << "\nLink types: " << types.size() << '\n';
    for (unsigned round = 1; !types.empty(); ++round) {
        std::vector<Rows> survivors;
        for (const Rows& t : types) if (compatible_root(t, types)) survivors.push_back(t);
        std::cout << "Round " << round << ": " << survivors.size()
                  << " of " << types.size() << " types survive\n";
        if (survivors.size() == types.size()) {
            std::cout << "Inconclusive\n"; return 1;
        }
        types = std::move(survivors);
    }
    std::cout << "No 24-block covering exists.\n";
}
