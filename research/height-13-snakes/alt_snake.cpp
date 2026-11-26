// Independent verifier for the longest induced path length on every 13-by-n grid.
// Uses an edge-crossing mate encoding (independent of frontier.cpp's vertex labels).
// Build: c++ -O3 -std=c++23 alt_snake.cpp -o verify
// Run:   ./verify
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <unordered_map>
#include <vector>

namespace {
constexpr int height = 13;
constexpr int above = height;
using Key = std::uint64_t;
using Values = std::vector<int>;
constexpr Key done = ~Key(0);
constexpr int unreachable = -1;  // Finite values count occupied squares.

// Each 4-bit slot describes an edge crossing from the processed side to the next square:
//   0:   processed endpoint is vacant, so the next square has no edge from it.
//   1:   processed endpoint is occupied and has no edge across this cut.
//   2+j: edge crosses the cut; its other path end exits at slot j (self-mate if
//        the other end of that path already terminated on the processed side).
// Slots 0..12 are horizontal cut edges; slot 13 is the vertical edge from above.
int slot(Key key, int position) { return int((key >> (4 * position)) & 15); }
void put(Key &key, int position, int value) {
    const int shift = 4 * position;
    key = (key & ~(Key(15) << shift)) | (Key(value) << shift);
}
void pair_ends(Key &key, int first, int second) {
    put(key, first, 2 + second);
    put(key, second, 2 + first);
}

struct Moves {
    int vacant = -1;
    std::array<int, 4> occupied{-1, -1, -1, -1};
};
struct Layer {
    std::unordered_map<Key, int> index;
    std::vector<Key> keys;
    std::vector<Moves> moves;

    int intern(Key key) {
        const auto [it, inserted] = index.try_emplace(key, int(keys.size()));
        if (inserted) keys.push_back(key);
        return it->second;
    }
};
std::array<Layer, height> layers;

Moves transitions(Key key, int row) {
    Layer &next = layers[(row + 1) % height];
    Moves moves;
    if (key == done) {
        moves.vacant = next.intern(done);
        return moves;
    }
    const int left = slot(key, row), up = slot(key, above);
    Key cleared = key;
    put(cleared, row, 0);
    put(cleared, above, 0);
    if (left < 2 && up < 2) moves.vacant = next.intern(cleared);
    if (left == 1 || up == 1) return moves;
    if (left == 2 + above && up == 2 + row) return moves;  // Would close a cycle.

    const int incoming = (left >= 2) + (up >= 2);
    for (int mask = 0; mask < 4; ++mask) {
        const bool right = mask & 1, down = mask & 2;
        if ((down && row + 1 == height) || incoming + right + down > 2) continue;
        Key result = cleared;
        put(result, row, 1);
        if (row + 1 < height) put(result, above, 1);

        std::array<int, 2> ends{};
        int count = 0;
        if (left >= 2 && left != 2 + row) ends[count++] = left - 2;
        if (up >= 2 && up != 2 + above) ends[count++] = up - 2;
        if (right) ends[count++] = row;
        if (down) ends[count++] = above;
        if (count == 2) pair_ends(result, ends[0], ends[1]);
        if (count == 1) pair_ends(result, ends[0], ends[0]);

        int active = 0, fixed_ends = 0;
        for (int i = 0; i <= height; ++i) {
            const int code = slot(result, i);
            active += (code >= 2);
            fixed_ends += (code == 2 + i);
        }
        if (count == 0) {
            if (active > 0) continue;  // A sealed component could never rejoin.
            result = done;
        }
        if (fixed_ends <= 2) moves.occupied[mask] = next.intern(result);
    }
    return moves;
}

void build() {
    bool added = true;
    while (added) {
        added = false;
        for (int row = 0; row < height; ++row) {
            Layer &layer = layers[row];
            while (layer.moves.size() < layer.keys.size()) {
                const Key key = layer.keys[layer.moves.size()];
                layer.moves.push_back(transitions(key, row));
                added = true;
            }
        }
    }
}

void advance(Values &current) {
    for (int row = 0; row < height; ++row) {
        Values next(layers[(row + 1) % height].moves.size(), unreachable);
        const auto &choices = layers[row].moves;
        for (std::size_t i = 0; i < current.size(); ++i) {
            const int value = current[i];
            if (value == unreachable) continue;
            const Moves &moves = choices[i];
            if (moves.vacant >= 0) next[moves.vacant] = std::max(next[moves.vacant], value);
            for (int dest : moves.occupied)
                if (dest >= 0) next[dest] = std::max(next[dest], value + 1);
        }
        current.swap(next);
    }
}

int answer(int n) {
    constexpr std::array<int, 6> initial{13, 20, 28, 36, 43, 51};
    constexpr std::array<int, 6> offset{4, 3, 3, 3, 4, 4};
    return n <= 6 ? initial.at(n - 1) : 8 * n + offset[n % 6];
}

void require(bool test, const char *message) {
    if (!test) throw std::runtime_error(message);
}
}  // namespace

int main() {
    const int start = layers[0].intern(0);
    build();
    const int finished = layers[0].index.at(done);
    const auto states = layers[0].moves.size();
    std::cout << "Boundary states: " << states << '\n';
    require(states == 620950, "Unexpected state count");
    for (auto &layer : layers) {
        layer.index.clear();
        layer.index.rehash(0);
        layer.keys.clear();
        layer.keys.shrink_to_fit();
    }

    Values v(states, unreachable), at53;
    v[start] = 0;
    for (int n = 1; n <= 59; ++n) {
        advance(v);
        // Any longest snake can be shifted left to meet column 1; discard the
        // never-started state (`done` is tracked separately).
        v[start] = unreachable;
        require(v[finished] == answer(n), "Finite-width value mismatch");
        if (n == 53) at53 = v;
    }

    std::size_t reachable = 0;
    for (std::size_t i = 0; i < states; ++i) {
        const int expected = at53[i] == unreachable ? unreachable : at53[i] + 48;
        require(v[i] == expected, "Period certificate V(59) = V(53) + 48 failed");
        if (v[i] != unreachable) ++reachable;
    }
    std::cout << "Formula verified for widths 1 through 59.\n"
              << "V(59) = V(53) + 48 in all coordinates (" << reachable << " reachable).\n";
}
