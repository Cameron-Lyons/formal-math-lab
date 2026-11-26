// Exhaustive necessary-condition test for tiling a cube with slabs of orders 1..7.
// Build and run: c++ -std=c++17 -O2 bound_profiles.cpp -o /tmp/slab_profiles && /tmp/slab_profiles
#include <algorithm>
#include <array>
#include <iostream>
#include <vector>

constexpr int box_count = 7;
using Box = std::array<int, 3>;
using Profile = std::array<int, box_count>;  // Length of each box along one cube axis.

struct Counts {
    int shapes = 0;
    int orientations = 0;
    int pairwise_fit = 0;
};

class Search {
public:
    explicit Search(int side) : side(side) {
        for (int i = 0; i < box_count; ++i) {
            const int k = i + 1;
            for (int a = k; a <= side; a += k)
                for (int b = a; b <= side; b += k)
                    choices[i].push_back({k, a, b});
            const int largest = side / k * k;
            min_volume[i + 1] = min_volume[i] + k * k * k;
            max_volume[i + 1] = max_volume[i] + k * largest * largest;
        }
    }

    Counts run() {
        choose_boxes(box_count - 1, side * side * side);
        return counts;
    }

private:
    int side;
    Counts counts;
    std::array<std::vector<Box>, box_count> choices;
    std::array<int, box_count + 1> min_volume{}, max_volume{};
    std::array<Box, box_count> boxes;
    Profile volumes, lengths, areas;
    std::vector<Profile> admissible;

    // Unassigned boxes 0..i must contribute exactly the remaining volume.
    void choose_boxes(int i, int remaining) {
        if (remaining < min_volume[i + 1] || remaining > max_volume[i + 1]) return;
        if (i < 0) {
            ++counts.shapes;
            admissible.clear();
            choose_lengths(0);
            combine_axes();
            return;
        }
        for (const Box& box : choices[i]) {
            boxes[i] = box;
            volumes[i] = box[0] * box[1] * box[2];
            choose_boxes(i - 1, remaining - volumes[i]);
        }
    }

    void choose_lengths(int i) {
        if (i == box_count) {
            if (has_section_support()) admissible.push_back(lengths);
            return;
        }
        for (int j = 0; j < 3; ++j) {
            if (j > 0 && boxes[i][j] == boxes[i][j - 1]) continue;
            lengths[i] = boxes[i][j];
            areas[i] = volumes[i] / lengths[i];
            choose_lengths(i + 1);
        }
    }

    // Every generic transverse slice has area side^2. Full-length boxes occur
    // in every slice. For each shorter box there must be a slice containing it
    // and a slice omitting it.
    bool has_section_support() const {
        int target = side * side;
        int sums[1 << box_count] = {};
        int subset_count = 1;
        for (int i = 0; i < box_count; ++i) {
            if (lengths[i] == side) {
                target -= areas[i];
            } else {
                for (int mask = 0; mask < subset_count; ++mask)
                    sums[subset_count + mask] = sums[mask] + areas[i];
                subset_count *= 2;
            }
        }
        int union_mask = 0, intersection_mask = subset_count - 1;
        bool found = false;
        for (int mask = 0; mask < subset_count; ++mask) {
            if (sums[mask] != target) continue;
            found = true;
            union_mask |= mask;
            intersection_mask &= mask;
        }
        return found && union_mask == subset_count - 1 && intersection_mask == 0;
    }

    // Given lengths along two axes, the third is forced. Ordering the three
    // profiles lexicographically counts each orientation up to axis permutation.
    void combine_axes() {
        std::sort(admissible.begin(), admissible.end());
        for (const Profile& x : admissible) {
            for (const Profile& y : admissible) {
                if (y > x) break;
                Profile z;
                bool valid = true;
                for (int i = 0; i < box_count; ++i) {
                    const Box& box = boxes[i];
                    z[i] = box[0] + box[1] + box[2] - x[i] - y[i];
                    Box oriented{x[i], y[i], z[i]};
                    std::sort(oriented.begin(), oriented.end());
                    if (oriented != box) {
                        valid = false;
                        break;
                    }
                }
                if (!valid || z > y || !std::binary_search(admissible.begin(), admissible.end(), z))
                    continue;
                ++counts.orientations;
                std::cout << "Section-compatible orientation for side " << side << ':';
                for (int i = 0; i < box_count; ++i)
                    std::cout << " (" << x[i] << ',' << y[i] << ',' << z[i] << ')';
                std::cout << '\n';
                bool fits = true;
                for (int i = 0; i < box_count; ++i) {
                    for (int j = 0; j < i; ++j) {
                        if (x[i] + x[j] > side && y[i] + y[j] > side && z[i] + z[j] > side)
                            fits = false;
                    }
                }
                if (fits) ++counts.pairwise_fit;
            }
        }
    }
};

int main() {
    std::cout << "side  volume-tuples  section-compatible-orientations  pairwise-fit\n";
    Counts total;
    for (int n = 7; n <= 28; ++n) {
        const Counts c = Search(n).run();
        std::cout << n << "  " << c.shapes << "  " << c.orientations << "  " << c.pairwise_fit << '\n';
        total.shapes += c.shapes;
        total.orientations += c.orientations;
        total.pairwise_fit += c.pairwise_fit;
    }
    std::cout << "Total  " << total.shapes << "  " << total.orientations << "  " << total.pairwise_fit << '\n';
}
