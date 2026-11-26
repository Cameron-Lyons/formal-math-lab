// Compile with c++ -std=c++17 -O2 placement_search.cpp -o /tmp/place-slabs
// With no arguments, searches all cube sides for seven slabs.
// With arguments, searches one (number of slabs, cube side) pair, e.g. 3 6.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

using Point = std::array<int, 3>;
struct Box {
    Point low, high;
};
struct Shape {
    Point sides;
    int volume;
    std::vector<Point> orientations;
};

class Search {
    int count, side;
    std::vector<std::vector<Shape>> choices;
    std::vector<const Shape*> chosen;
    std::vector<int> min_volume, max_volume;
    std::vector<Box> placed;

    bool occupied(Point p) const {
        for (const Box& b : placed) {
            bool inside = true;
            for (int a = 0; a < 3; ++a)
                inside &= b.low[a] <= p[a] && p[a] < b.high[a];
            if (inside) return true;
        }
        return false;
    }

    bool fits(const Box& b) const {
        for (int a = 0; a < 3; ++a)
            if (b.low[a] < 0 || b.high[a] > side) return false;
        for (const Box& other : placed) {
            bool separated = false;
            for (int a = 0; a < 3; ++a)
                separated |= b.high[a] <= other.low[a] || other.high[a] <= b.low[a];
            if (!separated) return false;
        }
        return true;
    }

    bool fill(int unused) {
        if (!unused) return true; // All boxes fit and their volumes sum to the cube.

        // An uncovered cube corner determines the position of its covering box.
        // A high-side corner is represented by its adjacent unit cell at side-1.
        Point anchor{};
        int high_axes = 0;
        bool found = false;
        for (int corner = 0; corner < 8 && !found; ++corner) {
            for (int a = 0; a < 3; ++a)
                anchor[a] = (corner & (1 << a)) ? side - 1 : 0;
            if (!occupied(anchor)) {
                high_axes = corner;
                found = true;
            }
        }
        if (!found) {
            // The first uncovered unit cell in lexicographic order is the
            // low corner of the unplaced box that covers it.
            for (int x = 0; x < side && !found; ++x)
                for (int y = 0; y < side && !found; ++y)
                    for (int z = 0; z < side && !found; ++z) {
                        anchor = {x, y, z};
                        found = !occupied(anchor);
                    }
        }
        if (!found) return false;

        for (int k = 0; k < count; ++k) {
            int bit = 1 << k;
            if (!(unused & bit)) continue;
            for (const Point& d : chosen[k]->orientations) {
                Box b;
                for (int a = 0; a < 3; ++a) {
                    b.low[a] = (high_axes & (1 << a)) ? side - d[a] : anchor[a];
                    b.high[a] = b.low[a] + d[a];
                }
                if (!fits(b)) continue;
                placed.push_back(b);
                if (fill(unused ^ bit)) return true;
                placed.pop_back();
            }
        }
        return false;
    }

    bool pack() {
        // With at most seven boxes, one box owns at least two cube corners.
        // It contains an entire cube edge. By cube symmetry put that edge
        // along z at the origin and sort the other two sides.
        int all = (1 << count) - 1;
        for (int k = 0; k < count; ++k) {
            Point d = chosen[k]->sides;
            if (d[2] != side) continue;
            placed.push_back({{0, 0, 0}, d});
            if (fill(all ^ (1 << k))) return true;
            placed.pop_back();
        }
        return false;
    }

    bool choose(int k, int remaining) {
        if (remaining < min_volume[k] || remaining > max_volume[k]) return false;
        if (k == 0) {
            ++volume_tuples;
            return pack();
        }
        for (const Shape& shape : choices[k - 1]) {
            chosen[k - 1] = &shape;
            if (choose(k - 1, remaining - shape.volume)) return true;
        }
        return false;
    }

public:
    std::uint64_t volume_tuples = 0;
    Search(int pieces, int length) : count(pieces), side(length), choices(count),
        chosen(count), min_volume(count + 1), max_volume(count + 1) {
        for (int k = 1; k <= count; ++k) {
            min_volume[k] = min_volume[k - 1] + k * k * k;
            int longest = side / k * k;
            max_volume[k] = max_volume[k - 1] + k * longest * longest;
            for (int a = k; a <= side; a += k)
                for (int b = a; b <= side; b += k) {
                    Point d{k, a, b};
                    Shape shape{d, k * a * b, {}};
                    do { shape.orientations.push_back(d); }
                    while (std::next_permutation(d.begin(), d.end()));
                    choices[k - 1].push_back(shape);
                }
        }
    }
    bool run() { return choose(count, side * side * side); }
};

int main(int argc, char** argv) {
    if (argc != 1 && argc != 3) return 2;
    int pieces = argc == 3 ? std::atoi(argv[1]) : 7;
    int first = argc == 3 ? std::atoi(argv[2]) : 1;
    int last = argc == 3 ? first : 28;
    if (pieces < 1 || pieces > 7 || first < 1 || last > 28) return 2;
    std::cout << "side  shape_tuples_checked  tiling\n";
    for (int n = first; n <= last; ++n) {
        Search search(pieces, n);
        bool tiled = search.run();
        std::cout << n << "  " << search.volume_tuples << "  "
                  << (tiled ? "YES" : "no") << std::endl;
    }
}
