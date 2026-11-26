// Compile: c++ -std=c++20 -O3 verify_independent.cpp -o /tmp/verify_independent
// Run: /tmp/verify_independent
// This checker has no external inputs. It classifies the local pair covers by
// individualization and refinement, then branches on compatible labeled links
// for every choice of the (at most four) points of degree greater than ten.
//
// Removing a point of degree ten from its groups yields ten five-sets that
// cover all pairs of the other thirteen points. Each of those points has local
// degree at least three, since its twelve partners are covered four at a time.
// Their degrees total 50, so at least two points have local degree three.
// Name them 12 and 0. The three blocks through 12 partition the remaining
// points into parts of four, with point 0 in the first. The other two blocks
// through 0 must partition the other eight points into two four-sets. Up to
// relabeling, one meets the second part in k=0, 1 or 2 points. This fixes the
// first five blocks. The remaining five avoid both 12 and 0.
//
// The program also verifies that no block is redundant in any local cover.
// Hence no nine-block local cover exists: it could be padded to ten blocks.
// In a 24-group covering all fourteen points would therefore have degree at
// least ten. Their total degree of 144 permits at most four larger degrees.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <stdexcept>
#include <vector>

using namespace std;
using Link = array<int, 10>;
using Tail = array<int, 5>;
using Colors = array<int, 13>;

int shared[13][13];
Link relabel(const Link &link, const Colors &labeling) {
    Link answer{};
    for (int j = 0; j < 10; j++)
        for (int i = 0; i < 13; i++)
            if (link[j] & (1 << i))
                answer[j] |= 1 << labeling[i];
    sort(answer.begin(), answer.end());
    return answer;
}
// The current colors form an ordered partition respected by relabeling.
// Refine with colored multisets of pair multiplicities. When refinement
// stabilizes, individualize each possible point in a deterministically
// chosen cell. Equal minimum leaf codes are equivalent to isomorphism.
Link canonical_rec(const Link &link, Colors colors) {
    while (true) {
        array<vector<int>, 13> profiles{};
        for (int i = 0; i < 13; i++) {
            for (int j = 0; j < 13; j++)
                if (i != j)
                    profiles[i].push_back(16 * colors[j] + shared[i][j]);
            sort(profiles[i].begin(), profiles[i].end());
            profiles[i].insert(profiles[i].begin(), colors[i]);
        }
        vector<vector<int>> ordered(profiles.begin(), profiles.end());
        sort(ordered.begin(), ordered.end());
        ordered.erase(unique(ordered.begin(), ordered.end()), ordered.end());
        Colors next{};
        for (int i = 0; i < 13; i++)
            next[i] =
                lower_bound(ordered.begin(), ordered.end(), profiles[i]) - ordered.begin();
        if (ordered.size() == 13)
            return relabel(link, next);
        if (next != colors) {
            colors = next;
            continue;
        }
        vector<int> sizes(ordered.size(), 0);
        for (int col : colors)
            sizes[col]++;
        int c = -1;
        for (int i = 0; i < (int)sizes.size(); i++)
            if (sizes[i] > 1 && (c == -1 || sizes[i] < sizes[c]))
                c = i;
        Link best{};
        best.fill(1 << 13);
        for (int i = 0; i < 13; i++)
            if (colors[i] == c) {
                auto split = colors;
                split[i] = ordered.size();
                best = min(best, canonical_rec(link, split));
            }
        return best;
    }
}
Link canonical(const Link &link) {
    for (auto &row : shared)
        fill(begin(row), end(row), 0);
    for (int a : link)
        for (int i = 0; i < 13; i++)
            if (a >> i & 1)
                for (int j = 0; j < 13; j++)
                    if (a >> j & 1)
                        shared[i][j]++;
    return canonical_rec(link, {});
}

struct Candidate {
    unsigned mask;
    uint64_t pairs;
};
struct Search {
    vector<Candidate> blocks;
    array<vector<int>, 48> supports;
    uint64_t mandatory;
    set<Tail> solutions;
    int chosen[5]{};
    array<pair<int, int>, 48> cross;
    Search(unsigned a, unsigned b) {
        int n = 0;
        for (int i = 0; i < 12; i++)
            for (int j = 0; j < i; j++)
                if (i / 4 != j / 4)
                    cross[n++] = {j, i};
        auto edges = [&](unsigned mask) {
            uint64_t bits = 0;
            for (int e = 0; e < 48; e++) {
                auto [x, y] = cross[e];
                if ((mask >> x & 1) && (mask >> y & 1))
                    bits |= uint64_t{1} << e;
            }
            return bits;
        };
        mandatory = ((uint64_t{1} << 48) - 1) & ~(edges(a) | edges(b));
        for (unsigned mask = 0; mask < 4096; mask += 2)
            if (popcount(mask) == 5) {
                uint64_t es = edges(mask) & mandatory;
                int idx = blocks.size();
                blocks.push_back({mask, es});
                for (int e = 0; e < 48; e++)
                    if (es >> e & 1)
                        supports[e].push_back(idx);
            }
    }
    void visit(uint64_t missing, int remaining) {
        if (!missing) {
            if (remaining != 0) {
                cerr << "short completion" << endl;
                abort();
            }
            Tail answer;
            copy(chosen, chosen + 5, answer.begin());
            sort(answer.begin(), answer.end());
            solutions.insert(answer);
            return;
        }
        if (remaining == 0 || popcount(missing) > 8 * remaining)
            return;
        // Every completion must hit this particular uncovered edge in some block.
        int target = countr_zero(missing);
        for (int idx : supports[target]) {
            uint64_t next = missing & ~blocks[idx].pairs;
            chosen[5 - remaining] = blocks[idx].mask;
            if (popcount(next) <= 8 * (remaining - 1))
                visit(next, remaining - 1);
        }
    }
};
set<Link> enumerate_links() {
    set<Link> canonical_classes;
    for (int k = 0; k < 3; k++) {
        int a = 1 | (((1 << k) - 1) << 4) | (((1 << (4 - k)) - 1) << 8);
        int b = a ^ (15 << 4) ^ (15 << 8);
        Search s(a, b);
        s.visit(s.mandatory, 5);
        cout << "k=" << k << " normalized links=" << s.solutions.size() << endl;
        for (auto tail : s.solutions) {
            Link link{(1 << 12) | 15, (1 << 12) | (15 << 4), (1 << 12) | (15 << 8), a, b};
            copy(tail.begin(), tail.end(), link.begin() + 5);
            for (int i = 0; i < 13; i++)
                for (int j = 0; j < i; j++) {
                    int mask = (1 << i) | (1 << j);
                    if (none_of(link.begin(), link.end(),
                                [&](int r) { return (r & mask) == mask; }))
                        abort();
                }
            canonical_classes.insert(canonical(link));
        }
    }
    cout << "Independent class count " << canonical_classes.size() << endl;
    int least_private_pairs = 78;
    for (auto link : canonical_classes) {
        array<int, 10> private_pairs{};
        for (int i = 0; i < 13; i++)
            for (int j = 0; j < i; j++) {
                int pair_mask = (1 << i) | (1 << j), covers = 0, last = -1;
                for (int r = 0; r < 10; r++)
                    if ((link[r] & pair_mask) == pair_mask) {
                        covers++;
                        last = r;
                    }
                if (covers == 1)
                    private_pairs[last]++;
            }
        least_private_pairs =
            min(least_private_pairs, *min_element(private_pairs.begin(), private_pairs.end()));
    }
    cout << "Least number of private pairs in a block " << least_private_pairs << endl;
    if (least_private_pairs == 0)
        throw logic_error("A nine-block local cover has not been excluded");
    return canonical_classes;
}

using Rows = vector<int>;

// Root point 13 has the given link. Enumerate every possible ten-block link
// at a second point p that agrees on the blocks through both 13 and p.
// Store just the rows of six people that contain p and avoid 13.
set<Rows> star_options(const Link &root_link, int p, const set<Link> &types) {
    Rows target;
    for (int row : root_link)
        if (row & (1 << p))
            target.push_back(row);
    const int d = target.size();
    set<Rows> options;
    for (const auto &link : types)
        for (int v = 0; v < 13; ++v) {
            Rows marked, extra;
            for (int row : link)
                (row & (1 << v) ? marked : extra).push_back(row);
            if ((int)marked.size() != d)
                continue;
            // For this prospective link, v takes the role of the root point.
            vector<int> order(d);
            iota(order.begin(), order.end(), 0);
            do {
                vector<vector<int>> source(1 << d), dest(1 << d);
                for (int a = 0; a < 13; ++a) {
                    int src = 0, dst = 0;
                    for (int i = 0; i < d; ++i) {
                        if (marked[i] & (1 << a))
                            src |= 1 << i;
                        if (target[order[i]] & (1 << a))
                            dst |= 1 << i;
                    }
                    if (a != v)
                        source[src].push_back(a);
                    if (a != p)
                        dest[dst].push_back(a);
                }
                vector<int> cells;
                bool matches = true;
                for (int cell = 0; cell < (1 << d); ++cell) {
                    if (source[cell].size() != dest[cell].size()) {
                        matches = false;
                        break;
                    }
                    if (!source[cell].empty())
                        cells.push_back(cell);
                }
                if (!matches)
                    continue;
                array<int, 13> name{};
                auto assign = [&](auto &self, int pos) -> void {
                    if (pos == (int)cells.size()) {
                        Rows choice;
                        for (int row : extra) {
                            int mask = 1 << p;
                            for (int points = row; points; points &= points - 1)
                                mask |= 1 << name[countr_zero((unsigned)points)];
                            choice.push_back(mask);
                        }
                        sort(choice.begin(), choice.end());
                        options.insert(choice);
                        return;
                    }
                    int cell = cells[pos];
                    // Every bijection compatible with the marked rows permutes
                    // labels only within a cell of equal incidence signatures.
                    do {
                        for (size_t i = 0; i < dest[cell].size(); ++i)
                            name[source[cell][i]] = dest[cell][i];
                        self(self, pos + 1);
                    } while (next_permutation(dest[cell].begin(), dest[cell].end()));
                };
                assign(assign, 0);
            } while (next_permutation(order.begin(), order.end()));
        }
    return options;
}

struct Choice {
    int point;
    array<int, 13> shared{};
    Rows extra;
};

class Compatibility {
    vector<Choice> choices;
    int considered = 0;
    int next_id = 0;
    Link fixed;
    mutable int exact_assignments = 0, within_budget = 0;
    mutable map<pair<int, int>, int> summary;
    using Candidates = vector<int>;

    // Prune an option if too many of the considered points lack any
    // remaining option giving the identical rows for their shared pair.
    Candidates filter(Candidates live, int points, int permitted_missing) const {
        erase_if(live, [&](int i) { return !(points & (1 << choices[i].point)); });
        vector<int> support(next_id, 0);
        size_t old;
        do {
            old = live.size();
            fill(support.begin(), support.end(), 0);
            for (int i : live) {
                const Choice &c = choices[i];
                for (int t = points ^ (1 << c.point); t; t &= t - 1) {
                    int q = countr_zero((unsigned)t);
                    support[c.shared[q]] |= 1 << c.point;
                }
            }
            erase_if(live, [&](int i) {
                const Choice &c = choices[i];
                int count = 0;
                for (int t = points ^ (1 << c.point); t; t &= t - 1) {
                    int q = countr_zero((unsigned)t);
                    if (!(support[c.shared[q]] & (1 << q)))
                        ++count;
                }
                return count > permitted_missing;
            });
        } while (live.size() != old);
        return live;
    }

    // Test the actual union at a leaf. An over-budget union cannot occur in
    // a covering. At exactly 24 groups, the whole design is already fixed.
    // The exhaustive run checks that no compatible leaf uses fewer than 24.
    bool exact(const Candidates &live, int points, const Rows &already) const {
        if (!points) {
            ++exact_assignments;
            if (already.size() > 14) {
                ++summary[{already.size(), -1}];
                return false;
            }
            if (already.size() < 14)
                throw logic_error("Inconclusive: an assignment leaves unused group slots");
            ++within_budget;
            Rows all_groups = already;
            for (int row : fixed)
                all_groups.push_back(row | (1 << 13));
            int holes = 0;
            for (int t = 0; t < (1 << 14); t++)
                if (popcount((unsigned)t) == 3) {
                    auto covered = [t](int group) { return (t & group) == t; };
                    if (none_of(all_groups.begin(), all_groups.end(), covered))
                        ++holes;
                }
            ++summary[{already.size(), holes}];
            return holes == 0;
        }
        array<int, 13> counts{};
        for (int i : live)
            ++counts[choices[i].point];
        int p = countr_zero((unsigned)points);
        for (int t = points; t; t &= t - 1) {
            int q = countr_zero((unsigned)t);
            if (counts[q] < counts[p])
                p = q;
        }
        // Every compatible assignment chooses exactly one option at p.
        for (int i : live)
            if (choices[i].point == p) {
                Candidates next;
                for (int j : live) {
                    int q = choices[j].point;
                    if (q != p && choices[i].shared[q] == choices[j].shared[p])
                        next.push_back(j);
                }
                Rows combined;
                set_union(already.begin(), already.end(), choices[i].extra.begin(),
                          choices[i].extra.end(), back_inserter(combined));
                if (exact(next, points ^ (1 << p), combined))
                    return true;
            }
        return false;
    }

  public:
    Compatibility(const Link &root_link, const set<Link> &types) : fixed(root_link) {
        array<map<Rows, int>, 13 * 13> intern;
        for (int p = 0; p < 13; ++p) {
            int d = count_if(root_link.begin(), root_link.end(),
                             [&](int row) { return row & (1 << p); });
            if (d >= 4)
                considered |= 1 << p;
        }
        for (int p = 0; p < 13; ++p)
            if (considered & (1 << p)) {
                for (const Rows &rows : star_options(root_link, p, types)) {
                    Choice choice{p, {}, rows};
                    for (int t = considered ^ (1 << p); t; t &= t - 1) {
                        int q = countr_zero((unsigned)t);
                        Rows slice;
                        for (int row : rows)
                            if (row & (1 << q))
                                slice.push_back(row);
                        auto &index = intern[13 * min(p, q) + max(p, q)];
                        auto [where, inserted] = index.emplace(slice, next_id);
                        if (inserted)
                            ++next_id;
                        choice.shared[q] = where->second;
                    }
                    choices.push_back(choice);
                }
            }
    }

    struct Result {
        int masks = 0, locally_consistent = 0, feasible = 0;
    };
    Result check() const {
        Candidates initial(choices.size());
        iota(initial.begin(), initial.end(), 0);
        const auto pool = filter(initial, considered, 4);
        Result result;
        // Mark exactly four ignored points. This only relaxes the conditions
        // when fewer than four of the considered points are genuinely high.
        int omissions = min(4, popcount((unsigned)considered));
        for (int omitted = considered;; omitted = (omitted - 1) & considered) {
            if (popcount((unsigned)omitted) == omissions) {
                ++result.masks;
                int required = considered ^ omitted;
                auto candidates = filter(pool, required, 0);
                int mask = 0;
                for (int i : candidates)
                    mask |= 1 << choices[i].point;
                if (mask == required) {
                    ++result.locally_consistent;
                    if (exact(candidates, required, {}))
                        ++result.feasible;
                }
            }
            if (!omitted)
                break;
        }
        if (exact_assignments) {
            cout << "  " << exact_assignments << " compatible assignments, " << within_budget
                 << " within the 24-group budget\n";
            for (auto [size_and_holes, count] : summary) {
                auto [additional, holes] = size_and_holes;
                cout << "  " << count << " assignments force " << additional + 10
                     << " total groups";
                if (holes >= 0)
                    cout << " and miss " << holes << " triples";
                cout << "\n";
            }
        }
        return result;
    }
};

int main() {
    auto types = enumerate_links();
    int masks = 0, locally_consistent = 0, feasible = 0, class_number = 0;
    for (const auto &root_link : types) {
        auto r = Compatibility(root_link, types).check();
        cout << "Root class " << ++class_number << ": " << r.masks
             << " choices of ignored points, " << r.locally_consistent
             << " pass pairwise filtering, " << r.feasible << " extend to a covering\n";
        masks += r.masks;
        locally_consistent += r.locally_consistent;
        feasible += r.feasible;
    }
    cout << "Total: " << masks << " choices, " << locally_consistent
         << " pass pairwise filtering, " << feasible << " extend to a covering\n";
    if (feasible) {
        cout << "The necessary conditions do not exclude a covering.\n";
        return 1;
    }
    cout << "No covering of all 364 triples by 24 six-person groups exists.\n";
}
