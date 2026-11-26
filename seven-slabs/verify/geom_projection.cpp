// Compile: c++ -std=c++17 -O2 geom_projection.cpp -o geom_projection
// Run:     ./geom_projection
#include <algorithm>
#include <array>
#include <iostream>
#include <set>
#include <vector>

using Shape = std::array<int, 3>; // increasing order, with repetitions

template <int K>
struct Sweep {
    using Lengths = std::array<int, K>;
    int side;
    const std::array<Shape, K>& shapes;
    Lengths ends{}, lengths{}, volumes{};
    std::set<Lengths> projections;

    Sweep(int s, const std::array<Shape, K>& boxes) : side(s), shapes(boxes) {
        for (int i = 0; i < K; ++i)
            volumes[i] = boxes[i][0] * boxes[i][1] * boxes[i][2];
        fill(0, 0, side * side);
    }

    // Choose slabs starting at position to supply exactly missing_area.
    // lengths[i] stays nonzero after an interval ends, preventing reuse.
    void fill(int i, int position, int missing_area) {
        if (missing_area == 0) {
            int next = side;
            for (int end : ends)
                if (end > position) next = std::min(next, end);
            if (next == side) {
                // This is automatic from volume equality, but explicitly
                // require every slab to have been scheduled.
                if (std::find(lengths.begin(), lengths.end(), 0) == lengths.end())
                    projections.insert(lengths);
            } else {
                int vacated = 0;
                for (int j = 0; j < K; ++j)
                    if (ends[j] == next) vacated += volumes[j] / lengths[j];
                fill(0, next, vacated);
            }
            return;
        }
        if (i == K) return;
        fill(i + 1, position, missing_area); // slab i does not start here
        if (lengths[i]) return;
        int previous = 0;
        for (int d : shapes[i]) {
            if (d == previous) continue;
            previous = d;
            const int area = volumes[i] / d;
            if (position + d > side || area > missing_area) continue;
            ends[i] = position + d;
            lengths[i] = d;
            fill(i + 1, position, missing_area - area);
            ends[i] = lengths[i] = 0;
        }
    }
};

struct Enumerate {
    static constexpr int K = 7;
    const int side;
    std::array<std::vector<Shape>, K> options;
    std::array<std::vector<bool>, K + 1> reachable;
    std::array<Shape, K> shapes;
    int volume_sets = 0, one_axis = 0, multiple_vectors = 0, all_k1_lengths = 0;

    void check(int k, int remainder) {
        if (k == 0) {
            ++volume_sets;
            Sweep<K> sweep(side, shapes);
            if (sweep.projections.empty()) return;
            ++one_axis;
            multiple_vectors += sweep.projections.size() >= 2;
            // Every edge length of slab 1 must occur as its longitudinal
            // length on at least one of the cube's three axes.
            for (int d : shapes[0]) {
                bool occurs = false;
                for (const auto& p : sweep.projections)
                    if (p[0] == d) occurs = true;
                if (!occurs) return;
            }
            ++all_k1_lengths;
            return;
        }
        for (const auto& s : options[k - 1]) {
            const int v = s[0] * s[1] * s[2];
            if (v > remainder || !reachable[k - 1][remainder - v]) continue;
            shapes[k - 1] = s;
            check(k - 1, remainder - v);
        }
    }

    explicit Enumerate(int n) : side(n) {
        int cube = n * n * n;
        reachable[0].assign(cube + 1, false);
        reachable[0][0] = true;
        for (int k = 1; k <= K; ++k) {
            reachable[k].assign(cube + 1, false);
            for (int a = k; a <= n; a += k)
                for (int b = a; b <= n; b += k) {
                    options[k - 1].push_back({k, a, b});
                    const int v = k * a * b;
                    for (int r = v; r <= cube; ++r)
                        if (reachable[k - 1][r - v]) reachable[k][r] = true;
                }
        }
        check(K, cube);
    }
};

int main() {
    // Known 3-slab tiling of a 6-cube. The first axis sees three consecutive
    // intervals, and the other two axes see three intervals spanning the cube.
    const std::array<Shape, 3> layers = {{{1, 6, 6}, {2, 6, 6}, {3, 6, 6}}};
    const Sweep<3> control(6, layers);
    if (!control.projections.count({1, 2, 3}) ||
        !control.projections.count({6, 6, 6})) {
        std::cerr << "Three-slab positive control failed\n";
        return 1;
    }
    std::cout << "side volume_sets one_axis multiple_vectors all_k1_lengths\n";
    for (int n = 10; n <= 28; ++n) {
        Enumerate e(n);
        std::cout << n << " " << e.volume_sets << " " << e.one_axis << " "
                  << e.multiple_vectors << " " << e.all_k1_lengths << "\n";
    }
}
