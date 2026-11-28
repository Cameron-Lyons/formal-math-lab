// Build with c++ -O3 -std=c++20 periodic_coloring.cpp -o periodic_coloring.
// Default: check the period-23 positive example and the stated negative cases.
// With one argument: full cyclic problem at that modulus. With a second argument:
// project only APs of that interval length onto the modulus.
// Each exhaustive search enumerates proper color classes first, then looks for a partition.
// A solution with fewer than seven colors can be refined to exactly seven since p>=7.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <string>
#include <utility>
#include <stdexcept>
#include <vector>

using Mask = std::uint64_t;

struct ColorClass {
    Mask members;
    std::vector<Mask> forbidden_pairs;
};

class PeriodSearch {
    static constexpr int palette = 7;
    int period;
    int length; // Zero means all cyclic progressions with nonzero step.
    Mask universe;
    std::vector<Mask> progressions;
    std::vector<std::vector<Mask>> forbidden_with;
    std::vector<ColorClass> classes;
    std::vector<std::vector<int>> by_size;
    std::vector<int> chosen;
    std::uint64_t nodes = 0;

    static Mask point(int i) { return Mask{1} << i; }

    void build_progressions() {
        // Masking discards repetitions: the question counts distinct colors.
        int max_step = length ? (length - 1) / 3 : period - 1;
        for (int d = 1; d <= max_step; ++d) {
            int starts = length ? length - 3 * d : period;
            for (int a = 0; a < starts; ++a) {
                Mask edge = 0;
                for (int j = 0; j < 4; ++j) edge |= point((a + j * d) % period);
                progressions.push_back(edge);
            }
        }
        std::sort(progressions.begin(), progressions.end());
        progressions.erase(std::unique(progressions.begin(), progressions.end()), progressions.end());
    }

    void build_forbidden_subsets() {
        // A color class must leave at least two distinct vertices of each edge.
        // Store, for each vertex, the other vertices in every minimal violation.
        for (Mask edge : progressions) {
            for (Mask omitted = edge; omitted; omitted &= omitted - 1) {
                Mask forbidden = edge ^ (omitted & -omitted);
                for (Mask m = forbidden; m; m &= m - 1) {
                    int x = std::countr_zero(m);
                    forbidden_with[x].push_back(forbidden ^ point(x));
                }
            }
        }
        for (auto& list : forbidden_with) {
            std::sort(list.begin(), list.end());
            list.erase(std::unique(list.begin(), list.end()), list.end());
        }
    }

    void generate_classes(Mask members, int first) {
        if (members) {
            int size = std::popcount(members);
            if (size >= static_cast<int>(by_size.size())) by_size.resize(size + 1);
            by_size[size].push_back(static_cast<int>(classes.size()));
            std::vector<Mask> pairs;
            for (Mask edge : progressions) {
                Mask rest = edge & ~members;
                if (std::popcount(rest) == 2) pairs.push_back(rest);
            }
            std::sort(pairs.begin(), pairs.end());
            pairs.erase(std::unique(pairs.begin(), pairs.end()), pairs.end());
            classes.push_back({members, std::move(pairs)});
        }
        for (int x = first; x < period; ++x) {
            const auto& forbidden = forbidden_with[x];
            bool invalid = std::any_of(forbidden.begin(), forbidden.end(), [&](Mask rest) {
                return (members & rest) == rest;
            });
            if (!invalid) generate_classes(members | point(x), x + 1);
        }
    }

    Mask orbit_minimum(Mask members) const {
        if (length) {
            // Reversal of the full interval preserves its projected constraints.
            Mask reflected = 0;
            for (Mask m = members; m; m &= m - 1) {
                reflected |= point((length - 1 - std::countr_zero(m)) % period);
            }
            return std::min(members, reflected);
        }
        // Translations and multiplication by units preserve the cyclic APs.
        Mask best = members;
        for (int d = 1; d < period; ++d) {
            if (std::gcd(d, period) != 1) continue;
            Mask image = 0;
            for (Mask b = members; b; b &= b - 1) {
                image |= point((std::countr_zero(b) * d) % period);
            }
            for (int i = 0; i < period; ++i) {
                best = std::min(best, image);
                image = ((image << 1) & universe) | (image >> (period - 1));
            }
        }
        return best;
    }

    bool compatible(int first_id, int second_id) const {
        const ColorClass& first = classes[first_id];
        Mask second = classes[second_id].members;
        if (first.members & second) return false;
        for (Mask pair : first.forbidden_pairs) {
            if ((second & pair) == pair) return false;
        }
        return true;
    }

    // Candidates are disjoint from and compatible with every class already chosen.
    // A solution can select its remaining classes in decreasing size, with equal
    // sizes ordered by increasing ID; only the first (symmetry-fixed) class is exempt.
    bool cover(Mask remaining, int largest, int previous, const std::vector<int>& candidates) {
        ++nodes;
        int seats = palette - static_cast<int>(chosen.size());
        int total = std::popcount(remaining);
        if (seats == 0) return total == 0;
        if (total < seats || total > seats * largest) return false;

        std::array<int, 64> count_by_size{};
        Mask available = 0;
        for (int id : candidates) {
            Mask members = classes[id].members;
            int size = std::popcount(members);
            if (size > largest || (size == largest && id <= previous)) continue;
            ++count_by_size[size];
            available |= members;
        }
        if ((available & remaining) != remaining) return false;
        // Even the largest available classes, ignoring overlap, must cover every point.
        int capacity = 0;
        int unfilled = seats;
        for (int size = largest; size >= 1 && unfilled; --size) {
            int take = std::min(unfilled, count_by_size[size]);
            capacity += take * size;
            unfilled -= take;
        }
        if (capacity < total) return false;

        for (int id : candidates) {
            Mask add = classes[id].members;
            int size = std::popcount(add);
            if (size > largest || (size == largest && id <= previous)) continue;
            if (size * seats < total || total - size < seats - 1) continue;
            if (seats == 1) {
                // The inequalities and add ⊆ remaining force add = remaining.
                chosen.push_back(id);
                return true;
            }

            std::vector<int> next;
            // After this choice, any other single class must leave at most
            // (seats-2)*size points for its remaining companions.
            int minimum = std::max(1, total - (seats - 1) * size);
            for (int other : candidates) {
                int other_size = std::popcount(classes[other].members);
                if (other_size < minimum || other_size > size) continue;
                if (other_size == size && other <= id) continue;
                if (compatible(id, other)) next.push_back(other);
            }
            chosen.push_back(id);
            if (cover(remaining ^ add, size, id, next)) return true;
            chosen.pop_back();
        }
        return false;
    }

public:
    PeriodSearch(int p, int interval_length)
        : period(p), length(interval_length), universe(point(p) - 1),
          forbidden_with(p), by_size(1) {}

    bool run() {
        build_progressions();
        std::cout << "p=" << period;
        if (length) std::cout << " length=" << length;
        else std::cout << " cyclic";
        if (std::any_of(progressions.begin(), progressions.end(), [](Mask m) {
                return std::popcount(m) < 3;
            })) {
            std::cout << " seven_colors=no (a progression has fewer than three points)\n";
            return false;
        }
        build_forbidden_subsets();
        generate_classes(0, 0);
        int maximum = static_cast<int>(by_size.size()) - 1;
        bool found = false;
        for (int size = maximum; size * palette >= period && !found; --size) {
            for (int id : by_size[size]) {
                Mask set = classes[id].members;
                if (orbit_minimum(set) != set) continue;
                chosen = {id};
                std::vector<int> candidates;
                int minimum = std::max(1, period - (palette - 1) * size);
                for (int k = size; k >= minimum; --k) {
                    for (int other : by_size[k]) {
                        if (compatible(id, other)) candidates.push_back(other);
                    }
                }
                if (cover(universe ^ set, size, -1, candidates)) {
                    found = true;
                    break;
                }
            }
        }
        std::cout << " maximum_class=" << maximum
                  << " nodes=" << nodes << " seven_colors=" << (found ? "yes" : "no") << '\n';
        if (found) {
            for (int j = 0; j < period; ++j) {
                for (std::size_t i = 0; i < chosen.size(); ++i) {
                    if (classes[chosen[i]].members & point(j)) std::cout << i << ' ';
                }
            }
            std::cout << '\n';
        }
        return found;
    }
};

// Repeating this block three times gives a legal 69-position coloring. Test directly
// on the interval, independently of the exact-cover verifier; also check the full cycle.
bool check_positive_example() {
    constexpr std::array<int, 23> block{
        0, 0, 1, 2, 3, 0, 0, 4, 1, 1, 3, 5, 3, 2, 6, 1, 4, 2, 6, 4, 5, 6, 5
    };
    auto color_count = [&](int a, int d) {
        unsigned mask = 0;
        for (int j = 0; j < 4; ++j) mask |= 1u << block[(a + j * d) % 23];
        return std::popcount(mask);
    };
    for (int d = 1; d < 23; ++d)
        for (int a = 0; a < 23; ++a)
            if (color_count(a, d) < 3) return false;
    int checked = 0;
    for (int d = 1; 3 * d < 69; ++d)
        for (int a = 0; a + 3 * d < 69; ++a) {
            if (color_count(a, d) < 3) return false;
            ++checked;
        }
    std::cout << "p=23 interval_length=69 valid=yes checked_progressions=" << checked << '\n';
    return true;
}

int main(int argc, char** argv) {
    if (argc == 2 || argc == 3) {
        int period = std::stoi(argv[1]);
        int length = argc == 3 ? std::stoi(argv[2]) : 0;
        if (period < 7 || period > 63)
            throw std::invalid_argument("the 64-bit verifier supports periods from 7 through 63");
        if (argc == 3 && length < period)
            throw std::invalid_argument("the interval length must be at least the period");
        PeriodSearch(period, length).run();
        return 0;
    }
    if (argc != 1) return 2;
    if (!check_positive_example()) return 1;
    for (int p : {25, 27, 29, 31, 33, 35, 37, 39}) {
        if (PeriodSearch(p, 0).run()) return 1;
    }
    for (int p : {37, 39}) {
        if (PeriodSearch(p, 70).run()) return 1;
    }
    for (int p : {41, 43, 45}) {
        if (PeriodSearch(p, 78).run()) return 1;
    }
}
