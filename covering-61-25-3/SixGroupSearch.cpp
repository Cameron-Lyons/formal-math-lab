// Check the six-to-five replacement question for the 27 groups in Covering.lean.
// Build with c++ -std=c++23 -O3 -Wall -Wextra -Wpedantic -Werror SixGroupSearch.cpp -o six-group-search
// Run ./six-group-search [Covering.lean]
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>

namespace {
constexpr int people = 61, groupSize = 25, publishedCount = 27, replacements = 5;
using Mask = std::uint64_t;
using Cut = std::uint32_t;
using Degrees = std::array<int, people>;
using PairCounts = std::array<Degrees, people>;
using Links = std::array<std::array<Mask, people>, people>;
using Published = std::array<Mask, publishedCount>;

constexpr Mask bit(int i) {
    return Mask{1} << i;
}
constexpr Mask everyone = bit(people) - 1;
int first(Mask s) {
    return std::countr_zero(s);
}
int size(Mask s) {
    return std::popcount(s);
}
int ceiling(int a, int b) {
    return (a + b - 1) / b;
}

void expect(std::istream &in, char token) {
    char actual;
    if (!(in >> actual) || actual != token)
        throw std::runtime_error("Unexpected syntax in the published group list");
}

Published readPublished(const char *path) {
    std::ifstream in(path);
    std::string line;
    while (std::getline(in, line) && line != "def published : List Nat := [") {
    }
    if (!in)
        throw std::runtime_error("Cannot find the published group list in " + std::string(path));
    Published rows{};
    for (int g = 0; g < publishedCount; ++g) {
        if (g)
            expect(in, ',');
        for (char c : std::string("pack["))
            expect(in, c);
        for (int j = 0; j < groupSize; ++j) {
            if (j)
                expect(in, ',');
            int label;
            if (!(in >> label) || label < 1 || label > people)
                throw std::runtime_error("Invalid person label");
            rows[g] |= bit(label - 1);
        }
        expect(in, ']');
        if (size(rows[g]) != groupSize)
            throw std::runtime_error("Repeated person in a published group");
    }
    expect(in, ']');
    return rows;
}

// link[a][b] contains exactly the third people c for which {a,b,c} still needs a group.
struct Source {
    std::array<Cut, people> incidence{};
    std::vector<Mask> lowUnion, highUnion;

    static std::vector<Mask> unions(const Published &rows, int offset, int length) {
        std::vector<Mask> result(1U << length);
        for (unsigned m = 1; m < result.size(); ++m)
            result[m] = result[m & (m - 1)] | rows[offset + std::countr_zero(m)];
        return result;
    }

    explicit Source(const Published &rows)
        : lowUnion(unions(rows, 0, 14)), highUnion(unions(rows, 14, 13)) {
        for (int j = 0; j < publishedCount; ++j)
            for (Mask s = rows[j]; s; s &= s - 1)
                incidence[first(s)] |= Cut{1} << j;
        Links allKept{};
        makeLinks(0, allKept);
        for (const auto &row : allKept)
            if (std::any_of(row.begin(), row.end(), [](Mask m) { return m != 0; }))
                throw std::runtime_error("Published groups do not cover every triple");
    }

    void makeLinks(Cut removed, Links &link) const {
        for (int a = 0; a < people; ++a)
            for (int b = a + 1; b < people; ++b) {
                Cut keep = incidence[a] & incidence[b] & ~removed;
                Mask covered = lowUnion[keep & 16383U] | highUnion[keep >> 14];
                link[a][b] = link[b][a] = everyone & ~(covered | bit(a) | bit(b));
            }
    }
};

// For fixed R, its compatible left vertices have no forbidden edge into R.
// Two sets L,R contain disjoint subsets of size w iff |L|,|R|>=w and |L union R|>=2w.
bool twoGroupsPossible(int w, Mask eligible, const std::array<Mask, people> &edges) {
    if (size(eligible) < 2 * w)
        return false;
    std::unordered_set<Mask> visited;
    auto search = [&](auto &&self, Mask right) -> bool {
        if (!visited.insert(right).second)
            return false;
        Mask left = 0, candidates = 0;
        for (Mask s = eligible; s; s &= s - 1) {
            int p = first(s);
            Mask compatible = right & ~edges[p];
            if (compatible == right)
                left |= bit(p);
            else if (size(compatible) >= w)
                candidates |= bit(p);
        }
        if (size(left) >= w && size(left | right) >= 2 * w)
            return true;
        if (size(left | candidates) < w || size(left | candidates | right) < 2 * w)
            return false;
        for (Mask s = candidates; s; s &= s - 1)
            if (self(self, right & ~edges[first(s)]))
                return true;
        return false;
    };
    return search(search, eligible);
}

struct Bounds {
    Degrees degree{};
    PairCounts pair{};
    std::array<Mask, people> neighbors{};
    int total = 0;

    // One group contributes at most 23 third people to a pair, and at most
    // 24 pair incidences to a person. Both ceilings are necessary lower bounds.
    explicit Bounds(const Links &link) {
        for (int a = 0; a < people; ++a) {
            int pairs = 0;
            for (int b = 0; b < people; ++b) {
                neighbors[a] |= link[a][b];
                pair[a][b] = ceiling(size(link[a][b]), groupSize - 2);
                pairs += pair[a][b];
            }
            degree[a] = ceiling(pairs, groupSize - 1);
            total += degree[a];
        }
    }

    bool allowsDegreeTwo(int p, int k, const Links &link) const {
        Mask mustAppear = neighbors[p], mustAppearTwice = 0;
        for (int q = 0; q < people; ++q)
            if (q != p) {
                if (degree[q] + 2 > k)
                    mustAppear |= bit(q);
                if (degree[q] >= k || pair[p][q] >= 2)
                    mustAppearTwice |= bit(q);
            }
        // Each of the two groups has just 24 places besides p. At least
        // 'need' mandatory neighbors must be absent from each respective
        // group. These two sets of absent neighbors must be disjoint and
        // have no link edge between them.
        int need = size(mustAppear) - (groupSize - 1);
        return need <= 0 || twoGroupsPossible(need, mustAppear & ~mustAppearTwice, link[p]);
    }

    bool strengthen(int k, const Links &link) {
        if (total > groupSize * k)
            return false;
        bool changed;
        do {
            changed = false;
            for (int p = 0; p < people; ++p) {
                int old = degree[p];
                while (degree[p] <= k) {
                    // If p occurs s times, p and q share at least
                    // s + degree[q] - k groups among the k group indices.
                    int s = degree[p], used = 0;
                    for (int q = 0; q < people; ++q)
                        if (q != p)
                            used += std::max(pair[p][q], s + degree[q] - k);
                    if (used <= (groupSize - 1) * s && (s != 2 || allowsDegreeTwo(p, k, link)))
                        break;
                    ++degree[p];
                }
                total += degree[p] - old;
                if (degree[p] > k || total > groupSize * k)
                    return false;
                if (degree[p] != old)
                    changed = true;
            }
        } while (changed);
        return true;
    }
};

// Each load is a set that must be contained in one particular replacement
// group. Distinct loads refer to distinct groups.
bool loadsFit(const Links &links, const Bounds &bounds, const Degrees &degree, Mask singletons,
              const std::vector<Mask> &loads) {
    PairCounts shared{};
    PairCounts minimum = bounds.pair;
    for (Mask load : loads) {
        for (Mask xs = load; xs; xs &= xs - 1) {
            int x = first(xs);
            for (Mask ys = xs & (xs - 1); ys; ys &= ys - 1) {
                int y = first(ys);
                int known = ++shared[x][y];
                // If x and y meet only once, all their missing third people
                // must fit in this very group.
                int needed = size(load | links[x][y]) > groupSize ? 2 : 1;
                minimum[x][y] = minimum[y][x] = std::max({minimum[x][y], known, needed});
            }
        }
    }
    int total = 0;
    for (int p = 0; p < people; ++p) {
        int pairs = std::accumulate(minimum[p].begin(), minimum[p].end(), 0);
        int needed = std::max(degree[p], ceiling(pairs, groupSize - 1));
        if ((singletons & bit(p)) && needed > 1)
            return false;
        total += needed;
    }
    if (total > replacements * groupSize)
        return false;
    for (Mask load : loads) {
        if (size(load) != groupSize)
            continue;
        // All 25 places are determined. Insert the group and retest the other four.
        Links rest = links;
        for (Mask xs = load; xs; xs &= xs - 1)
            for (Mask ys = load; ys; ys &= ys - 1)
                rest[first(xs)][first(ys)] &= ~load;
        if (!Bounds(rest).strengthen(replacements - 1, rest))
            return false;
    }
    return true;
}

bool placeComponents(const Links &links, const Bounds &bounds, const Degrees &degree, Mask singletons) {
    // Adjacent singletons in a missing triple have the same unique group.
    std::vector<Mask> components;
    Mask remaining = singletons;
    while (remaining) {
        Mask pending = remaining & -remaining;
        Mask load = pending;
        while (pending) {
            int p = first(pending);
            remaining &= ~bit(p);
            load |= bounds.neighbors[p];
            pending = remaining & load;
        }
        if (size(load) > groupSize)
            return false;
        components.push_back(load);
    }
    std::vector<Mask> loads;
    auto place = [&](auto &&self, std::size_t i) -> bool {
        if (i == components.size())
            return loadsFit(links, bounds, degree, singletons, loads);
        for (std::size_t j = 0; j < loads.size(); ++j) {
            Mask old = loads[j], combined = old | components[i];
            if (size(combined) > groupSize)
                continue;
            loads[j] = combined;
            bool fits = self(self, i + 1);
            loads[j] = old;
            if (fits)
                return true;
        }
        if (loads.size() == replacements)
            return false;
        loads.push_back(components[i]);
        bool fits = self(self, i + 1);
        loads.pop_back();
        return fits;
    };
    return place(place, 0);
}

bool singletonTest(const Links &links, const Bounds &bounds) {
    Mask candidates = 0;
    Degrees degree = bounds.degree;
    for (int p = 0; p < people; ++p)
        if (degree[p] == 1)
            candidates |= bit(p);
    // Each candidate who actually appears twice or more uses a spare seat.
    auto choose = [&](auto &&self, Mask undecided, Mask once, int spare) -> bool {
        if (!undecided || spare == 0)
            return placeComponents(links, bounds, degree, once | undecided);
        int p = first(undecided);
        undecided &= ~bit(p);
        if (self(self, undecided, once | bit(p), spare))
            return true;
        ++degree[p];
        bool fits = self(self, undecided, once, spare - 1);
        --degree[p];
        return fits;
    };
    return choose(choose, candidates, 0, replacements * groupSize - bounds.total);
}

int run(const char *input) {
    Source src(readPublished(input));
    Links links{};
    int checked = 0, afterBounds = 0, unresolved = 0;
    for (Cut cut = 0; cut < (Cut{1} << publishedCount); ++cut) {
        if (std::popcount(cut) != 6)
            continue;
        ++checked;
        src.makeLinks(cut, links);
        Bounds bounds(links);
        if (!bounds.strengthen(replacements, links))
            continue;
        ++afterBounds;
        if (singletonTest(links, bounds)) {
            ++unresolved;
            std::cout << "Unresolved removal mask " << cut << '\n';
        }
    }
    std::cout << "Six-group deletions checked: " << checked << "\nAfter attendance bounds: " << afterBounds
              << "\nAfter forced groups: " << unresolved << '\n';
    return unresolved == 0 ? 0 : 2;
}

} // namespace

int main(int argc, char **argv) {
    try {
        if (argc > 2)
            throw std::runtime_error("Usage: six-group-search [Covering.lean]");
        return run(argc == 2 ? argv[1] : "Covering.lean");
    } catch (const std::exception &e) {
        std::cerr << e.what() << '\n';
        return 1;
    }
}
