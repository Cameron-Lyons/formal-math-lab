// Check one entire orbit of pivot rows. Input contains compact cap/tail groups
// followed by exact encodings of earlier boards which must occur in the orbit.
#include <algorithm>
#include <array>
#include <bitset>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>

using Board = std::array<unsigned char, 100>;
using Key = std::array<std::uint64_t, 3>;
using Window = std::array<int, 4>;

struct KeyHash {
    std::size_t operator()(const Key& key) const {
        std::size_t hash = 0;
        for (auto part : key)
            hash ^= std::hash<std::uint64_t>{}(part) + 0x9e3779b9 + (hash << 6) + (hash >> 2);
        return hash;
    }
};

int cell(int x, int row) {
    return row * row + row + x;
}

struct Geometry {
    std::array<Window, 81> windows{};
    std::array<int, 100> mirror{};

    Geometry() {
        int n = 0;
        for (int row = 0; row < 10; ++row) {
            for (int x = -row; x <= row; ++x) {
                mirror[cell(x, row)] = cell(-x, row);
                if (row < 9)
                    windows[n++] = {cell(x, row), cell(x-1, row+1), cell(x, row+1), cell(x+1, row+1)};
            }
        }
    }
};

Key checked_key(const Board& image, const Geometry& geometry) {
    std::bitset<81> patterns;
    for (auto [top, left, middle, right] : geometry.windows)
        patterns.set(27*image[top] + 9*image[left] + 3*image[middle] + image[right]);
    if (!patterns.all()) throw std::runtime_error("invalid Cartesian T pattern set");
    // The fixed widths 40, 40, 20 make this ternary encoding injective.
    // Even 3^40 - 1 fits in uint64_t.
    Key key{};
    for (int i = 0; i < 100; ++i) key[i/40] = 3 * key[i/40] + image[i];
    return key;
}

std::string piece(std::size_t width) {
    std::string value;
    if (!(std::cin >> value) || value.size() != width || value.find_first_not_of("012") != value.npos)
        throw std::runtime_error("invalid ternary piece");
    return value;
}

std::string pivot_orbit(const std::string& pivot) {
    std::string colors = "012", least = pivot;
    do {
        std::string row = pivot;
        for (char& digit : row) digit = colors[digit - '0'];
        least = std::min(least, row);
        std::reverse(row.begin(), row.end());
        least = std::min(least, row);
    } while (std::next_permutation(colors.begin(), colors.end()));
    return least;
}

std::size_t check() {
    const Geometry geometry;
    int cut;
    if (!(std::cin >> cut) || cut < 1 || cut >= 9) throw std::runtime_error("invalid pivot row");
    const std::size_t pivot_width = 2*cut + 1;
    const std::size_t cap_width = cut*cut;
    const std::size_t tail_width = 100 - cap_width - pivot_width;
    const std::string partition = piece(pivot_width);
    std::size_t groups, earlier, expected;
    if (!(std::cin >> groups >> earlier >> expected)) throw std::runtime_error("invalid partition header");
    std::unordered_set<Key, KeyHash> boards;
    boards.reserve(expected);
    for (std::size_t g = 0; g < groups; ++g) {
        std::size_t orientations, cap_count, tail_count;
        if (!(std::cin >> orientations >> cap_count >> tail_count) || (orientations != 1 && orientations != 2))
            throw std::runtime_error("invalid group header");
        const std::string pivot = piece(pivot_width);
        if (pivot_orbit(pivot) != partition) throw std::runtime_error("incorrect pivot partition");
        std::vector<std::string> prefixes;
        for (std::size_t i = 0; i < cap_count; ++i) prefixes.push_back(piece(cap_width) + pivot);
        for (std::size_t i = 0; i < tail_count; ++i) {
            const std::string tail = piece(tail_width);
            for (const auto& prefix : prefixes) {
                const std::string base = prefix + tail;
                for (std::size_t flip = 0; flip < orientations; ++flip) {
                    Board source, image;
                    for (int j = 0; j < 100; ++j) source[j] = base[flip ? geometry.mirror[j] : j] - '0';
                    std::array<unsigned char, 3> colors{0, 1, 2};
                    do {
                        for (int j = 0; j < 100; ++j) image[j] = colors[source[j]];
                        if (!boards.insert(checked_key(image, geometry)).second)
                            throw std::runtime_error("duplicate full board");
                    } while (std::next_permutation(colors.begin(), colors.end()));
                }
            }
        }
    }
    for (std::size_t i = 0; i < earlier; ++i) {
        Key key;
        if (!(std::cin >> key[0] >> key[1] >> key[2]) || !boards.contains(key))
            throw std::runtime_error("an earlier board is absent");
    }
    std::string extra;
    if ((std::cin >> extra) || boards.size() != expected) throw std::runtime_error("incorrect partition count");
    return boards.size();
}

int main() {
    std::ios::sync_with_stdio(false);
    std::cin.tie(nullptr);
    try {
        std::cout << check() << '\n';
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
