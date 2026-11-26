// Independent exhaustive nonexistence verifier for a 24-block (14,6,3) covering.
// Compile: c++ -std=c++23 -O3 verify_independent.cpp -o /tmp/verify_independent
// Run:     /tmp/verify_independent
//
// Algorithm (independent of verify_covering.cpp):
// 1. Classify all 10-block (13,5,2) local pair covers via individualization and
//    color refinement, and confirm every block has at least one private pair
//    (hence no 9-block local cover exists, so every point in a 24-block (14,6,3)
//    covering has degree ≥ 10, leaving at most 144 - 140 = 4 points of degree ≥ 11).
// 2. For each of the 30 root link types and every choice of 4 ignored points among
//    its degree-≥-4 neighbors, filter pairwise-compatible 10-block links and run
//    exact backtracking; every surviving assignment forces 24 blocks and misses trios.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <iterator>
#include <map>
#include <numeric>
#include <set>
#include <stdexcept>
#include <utility>
#include <vector>

namespace {

using Link = std::array<int, 10>;
using Tail = std::array<int, 5>;
using Colors = std::array<int, 13>;
using Rows = std::vector<int>;
using PairCounts = std::array<std::array<int, 13>, 13>;

Link relabel(const Link &link, const Colors &labeling) {
    Link out{};
    for (int j = 0; j < 10; ++j)
        for (int i = 0; i < 13; ++i)
            if (link[j] >> i & 1) out[j] |= 1 << labeling[i];
    std::sort(out.begin(), out.end());
    return out;
}

// Individualization-refinement canonicalizer using colored pair multiplicities.
Link canonical_rec(const Link &link, const PairCounts &shared, Colors colors) {
    while (true) {
        std::array<std::vector<int>, 13> profiles{};
        for (int i = 0; i < 13; ++i) {
            profiles[i].reserve(13);
            for (int j = 0; j < 13; ++j)
                if (i != j) profiles[i].push_back(16 * colors[j] + shared[i][j]);
            std::sort(profiles[i].begin(), profiles[i].end());
            profiles[i].insert(profiles[i].begin(), colors[i]);
        }
        std::vector<std::vector<int>> ordered(profiles.begin(), profiles.end());
        std::sort(ordered.begin(), ordered.end());
        ordered.erase(std::unique(ordered.begin(), ordered.end()), ordered.end());

        Colors next{};
        for (int i = 0; i < 13; ++i)
            next[i] = int(std::lower_bound(ordered.begin(), ordered.end(), profiles[i]) -
                          ordered.begin());
        if (ordered.size() == 13) return relabel(link, next);
        if (next != colors) {
            colors = next;
            continue;
        }
        std::vector<int> sizes(ordered.size(), 0);
        for (int col : colors) ++sizes[col];
        int split_col = -1;
        for (int c = 0; c < (int)sizes.size(); ++c)
            if (sizes[c] > 1 && (split_col < 0 || sizes[c] < sizes[split_col])) split_col = c;

        Link best{};
        best.fill(1 << 13);
        for (int i = 0; i < 13; ++i)
            if (colors[i] == split_col) {
                Colors branch = colors;
                branch[i] = int(ordered.size());
                best = std::min(best, canonical_rec(link, shared, branch));
            }
        return best;
    }
}

Link canonical(const Link &link) {
    PairCounts shared{};
    for (int row : link)
        for (int i = 0; i < 13; ++i)
            if (row >> i & 1)
                for (int j = 0; j < 13; ++j)
                    if (row >> j & 1) ++shared[i][j];
    return canonical_rec(link, shared, {});
}

// Enumerate all 5-block completions of the normalized 5-block anchor for a (13,5,2) cover.
struct LinkTailSearch {
    struct Candidate {
        unsigned mask;
        std::uint64_t pairs;
    };
    std::vector<Candidate> blocks;
    std::array<std::vector<int>, 48> supports;
    std::uint64_t mandatory = 0;
    std::set<Tail> solutions;
    Tail chosen{};

    LinkTailSearch(unsigned a, unsigned b) {
        std::array<std::pair<int, int>, 48> cross{};
        int n = 0;
        for (int i = 0; i < 12; ++i)
            for (int j = 0; j < i; ++j)
                if (i / 4 != j / 4) cross[n++] = {j, i};
        auto edges = [&](unsigned mask) {
            std::uint64_t bits = 0;
            for (int e = 0; e < 48; ++e) {
                auto [x, y] = cross[e];
                if ((mask >> x & 1) && (mask >> y & 1)) bits |= std::uint64_t{1} << e;
            }
            return bits;
        };
        mandatory = ((std::uint64_t{1} << 48) - 1) & ~(edges(a) | edges(b));
        for (unsigned mask = 0; mask < 4096; mask += 2) {
            if (std::popcount(mask) != 5) continue;
            std::uint64_t es = edges(mask) & mandatory;
            int idx = int(blocks.size());
            blocks.push_back({mask, es});
            for (int e = 0; e < 48; ++e)
                if (es >> e & 1) supports[e].push_back(idx);
        }
    }

    void visit(std::uint64_t missing, int remaining) {
        if (!missing) {
            if (remaining != 0) throw std::logic_error("short completion found");
            Tail answer = chosen;
            std::sort(answer.begin(), answer.end());
            solutions.insert(answer);
            return;
        }
        if (remaining == 0 || std::popcount(missing) > 8 * remaining) return;
        int target = std::countr_zero(missing);
        for (int idx : supports[target]) {
            std::uint64_t next = missing & ~blocks[idx].pairs;
            chosen[5 - remaining] = int(blocks[idx].mask);
            if (std::popcount(next) <= 8 * (remaining - 1)) visit(next, remaining - 1);
        }
    }
};

std::set<Link> enumerate_links() {
    std::set<Link> classes;
    for (int k = 0; k < 3; ++k) {
        int a = 1 | (((1 << k) - 1) << 4) | (((1 << (4 - k)) - 1) << 8);
        int b = a ^ (15 << 4) ^ (15 << 8);
        LinkTailSearch search{unsigned(a), unsigned(b)};
        search.visit(search.mandatory, 5);
        std::cout << "k=" << k << " normalized links=" << search.solutions.size() << '\n';
        for (const Tail &tail : search.solutions) {
            Link link{(1 << 12) | 15, (1 << 12) | (15 << 4), (1 << 12) | (15 << 8), a, b};
            std::copy(tail.begin(), tail.end(), link.begin() + 5);
            for (int i = 0; i < 13; ++i)
                for (int j = 0; j < i; ++j) {
                    int pair = (1 << i) | (1 << j);
                    if (std::none_of(link.begin(), link.end(),
                                     [&](int row) { return (row & pair) == pair; }))
                        throw std::logic_error("uncovered pair in link");
                }
            classes.insert(canonical(link));
        }
    }
    std::cout << "Independent class count: " << classes.size() << '\n';

    // Confirm every block of every 10-block link covers at least one private pair,
    // which rules out any 9-block (13,5,2) cover (it could be padded to 10 blocks).
    int least_private = 78;
    for (const Link &link : classes) {
        std::array<int, 10> private_pairs{};
        for (int i = 0; i < 13; ++i)
            for (int j = 0; j < i; ++j) {
                int pair = (1 << i) | (1 << j), covers = 0, owner = -1;
                for (int r = 0; r < 10; ++r)
                    if ((link[r] & pair) == pair) {
                        ++covers;
                        owner = r;
                    }
                if (covers == 1) ++private_pairs[owner];
            }
        least_private =
            std::min(least_private, *std::min_element(private_pairs.begin(), private_pairs.end()));
    }
    std::cout << "Least private pairs in any block: " << least_private << '\n';
    if (least_private == 0) throw std::logic_error("nine-block local cover not excluded");
    return classes;
}

// Visit every bijection (13 \ {skip_src}) -> (13 \ {skip_dst}) sending marked[i] to target[i].
template <class Visitor>
void for_each_matching_bijection(const Rows &marked, int skip_src, const Rows &target, int skip_dst,
                                 Visitor visit) {
    const int d = int(marked.size());
    std::vector<std::vector<int>> src_cells(1 << d), dst_cells(1 << d);
    for (int a = 0; a < 13; ++a) {
        int s = 0, t = 0;
        for (int i = 0; i < d; ++i) {
            if (marked[i] >> a & 1) s |= 1 << i;
            if (target[i] >> a & 1) t |= 1 << i;
        }
        if (a != skip_src) src_cells[s].push_back(a);
        if (a != skip_dst) dst_cells[t].push_back(a);
    }
    std::vector<int> nonempty;
    for (int c = 0; c < (1 << d); ++c) {
        if (src_cells[c].size() != dst_cells[c].size()) return;
        if (!src_cells[c].empty()) nonempty.push_back(c);
    }
    std::array<int, 13> map{};
    auto assign = [&](auto &self, int pos) -> void {
        if (pos == int(nonempty.size())) {
            visit(map);
            return;
        }
        int c = nonempty[pos];
        do {
            for (std::size_t i = 0; i < dst_cells[c].size(); ++i)
                map[src_cells[c][i]] = dst_cells[c][i];
            self(self, pos + 1);
        } while (std::next_permutation(dst_cells[c].begin(), dst_cells[c].end()));
    };
    assign(assign, 0);
}

// Given root point 13's link, enumerate every 10-block link at point p agreeing on
// blocks through {13, p}, returning its 6-person blocks containing p and omitting 13.
std::set<Rows> star_options(const Link &root_link, int p, const std::set<Link> &types) {
    Rows target;
    for (int row : root_link)
        if (row >> p & 1) target.push_back(row);
    std::sort(target.begin(), target.end());

    std::set<Rows> options;
    for (const Link &link : types) {
        for (int v = 0; v < 13; ++v) {
            Rows marked, extra;
            for (int row : link) (row >> v & 1 ? marked : extra).push_back(row);
            if (marked.size() != target.size()) continue;
            Rows perm = target;
            do {
                for_each_matching_bijection(marked, v, perm, p, [&](const std::array<int, 13> &map) {
                    Rows choice;
                    choice.reserve(extra.size());
                    for (int row : extra) {
                        int mask = 1 << p;
                        for (unsigned pts = unsigned(row); pts; pts &= pts - 1)
                            mask |= 1 << map[std::countr_zero(pts)];
                        choice.push_back(mask);
                    }
                    std::sort(choice.begin(), choice.end());
                    options.insert(std::move(choice));
                });
            } while (std::next_permutation(perm.begin(), perm.end()));
        }
    }
    return options;
}

class Compatibility {
    struct Choice {
        int point;
        std::array<int, 13> shared{};
        Rows extra;
    };
    using Candidates = std::vector<int>;

    std::vector<Choice> choices;
    int considered = 0, next_id = 0;
    Link fixed;
    mutable int exact_assignments = 0;
    mutable std::map<std::pair<int, int>, int> summary;

    Candidates filter(Candidates live, int points, int permitted_missing) const {
        std::erase_if(live, [&](int i) { return !(points >> choices[i].point & 1); });
        std::vector<int> support(next_id, 0);
        std::size_t old = 0;
        do {
            old = live.size();
            std::fill(support.begin(), support.end(), 0);
            for (int i : live) {
                const Choice &c = choices[i];
                for (unsigned t = unsigned(points ^ (1 << c.point)); t; t &= t - 1) {
                    int q = std::countr_zero(t);
                    support[c.shared[q]] |= 1 << c.point;
                }
            }
            std::erase_if(live, [&](int i) {
                const Choice &c = choices[i];
                int missing = 0;
                for (unsigned t = unsigned(points ^ (1 << c.point)); t; t &= t - 1) {
                    int q = std::countr_zero(t);
                    if (!(support[c.shared[q]] >> q & 1)) ++missing;
                }
                return missing > permitted_missing;
            });
        } while (live.size() != old);
        return live;
    }

    bool exact(const Candidates &live, int points, const Rows &already) const {
        if (!points) {
            ++exact_assignments;
            if (already.size() > 14) {
                ++summary[{int(already.size()), -1}];
                return false;
            }
            if (already.size() < 14)
                throw std::logic_error("inconclusive: assignment leaves unused group slots");
            Rows all_groups = already;
            for (int row : fixed) all_groups.push_back(row | (1 << 13));
            int holes = 0;
            for (unsigned t = 0; t < (1u << 14); ++t) {
                if (std::popcount(t) != 3) continue;
                auto covered = [t](int group) { return (int(t) & group) == int(t); };
                if (std::none_of(all_groups.begin(), all_groups.end(), covered)) ++holes;
            }
            ++summary[{int(already.size()), holes}];
            return holes == 0;
        }
        std::array<int, 13> counts{};
        for (int i : live) ++counts[choices[i].point];
        int p = std::countr_zero(unsigned(points));
        for (unsigned t = unsigned(points); t; t &= t - 1) {
            int q = std::countr_zero(t);
            if (counts[q] < counts[p]) p = q;
        }
        for (int i : live) {
            if (choices[i].point != p) continue;
            Candidates next;
            for (int j : live) {
                int q = choices[j].point;
                if (q != p && choices[i].shared[q] == choices[j].shared[p]) next.push_back(j);
            }
            Rows combined;
            std::set_union(already.begin(), already.end(), choices[i].extra.begin(),
                           choices[i].extra.end(), std::back_inserter(combined));
            if (exact(next, points ^ (1 << p), combined)) return true;
        }
        return false;
    }

  public:
    Compatibility(const Link &root_link, const std::set<Link> &types) : fixed(root_link) {
        std::array<std::map<Rows, int>, 13 * 13> intern;
        for (int p = 0; p < 13; ++p) {
            int d = int(std::count_if(root_link.begin(), root_link.end(),
                                      [&](int row) { return row >> p & 1; }));
            if (d >= 4) considered |= 1 << p;
        }
        for (int p = 0; p < 13; ++p) {
            if (!(considered >> p & 1)) continue;
            for (const Rows &rows : star_options(root_link, p, types)) {
                Choice choice{p, {}, rows};
                for (unsigned t = unsigned(considered ^ (1 << p)); t; t &= t - 1) {
                    int q = std::countr_zero(t);
                    Rows slice;
                    for (int row : rows)
                        if (row >> q & 1) slice.push_back(row);
                    auto &table = intern[13 * std::min(p, q) + std::max(p, q)];
                    auto [it, inserted] = table.emplace(std::move(slice), next_id);
                    if (inserted) ++next_id;
                    choice.shared[q] = it->second;
                }
                choices.push_back(std::move(choice));
            }
        }
    }

    struct Result {
        int masks = 0, locally_consistent = 0, feasible = 0, assignments = 0;
        std::map<std::pair<int, int>, int> summary;
    };

    Result check() const {
        Candidates initial(choices.size());
        std::iota(initial.begin(), initial.end(), 0);
        const auto pool = filter(initial, considered, 4);
        Result result;
        const int omissions = std::min(4, std::popcount(unsigned(considered)));
        for (int omitted = considered;; omitted = (omitted - 1) & considered) {
            if (std::popcount(unsigned(omitted)) == omissions) {
                ++result.masks;
                int required = considered ^ omitted;
                auto candidates = filter(pool, required, 0);
                int covered = 0;
                for (int i : candidates) covered |= 1 << choices[i].point;
                if (covered == required) {
                    ++result.locally_consistent;
                    if (exact(candidates, required, {})) ++result.feasible;
                }
            }
            if (!omitted) break;
        }
        result.assignments = exact_assignments;
        result.summary = summary;
        return result;
    }
};

}  // namespace

int main() {
    auto types = enumerate_links();
    int masks = 0, locally_consistent = 0, feasible = 0, assignments = 0;
    std::map<std::pair<int, int>, int> totals;
    for (const Link &root_link : types) {
        auto r = Compatibility(root_link, types).check();
        masks += r.masks;
        locally_consistent += r.locally_consistent;
        feasible += r.feasible;
        assignments += r.assignments;
        for (auto [k, v] : r.summary) totals[k] += v;
    }
    std::cout << "Omission subsets checked: " << masks
              << ", locally consistent: " << locally_consistent
              << ", exact assignments: " << assignments << '\n';
    for (auto [size_and_holes, count] : totals) {
        auto [additional, holes] = size_and_holes;
        std::cout << "  " << count << " assignments force " << additional + 10 << " groups";
        if (holes >= 0) std::cout << " and miss " << holes << " triples";
        std::cout << '\n';
    }
    if (feasible) {
        std::cout << "The necessary conditions do not exclude a covering.\n";
        return 1;
    }
    std::cout << "No covering of all 364 triples by 24 six-person groups exists.\n";
}
