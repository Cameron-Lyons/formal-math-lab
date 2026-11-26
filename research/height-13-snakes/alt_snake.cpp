// Verify the exact longest induced path length for every 13-by-n grid.
// Build with: c++ -O3 -std=c++17 alt_snake.cpp -o verify
// Run with: ./verify
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
constexpr int unreachable = -1; // All finite values count occupied cells.

// A slot describes an edge from a processed vertex to an unprocessed one.
//   0: the processed vertex is vacant, so the next vertex is free.
//   1: the processed vertex is occupied and has no edge across this cut.
//   2+j: the edge crosses the cut. Its mate is in slot j. A self-mate
//        means that the other end of this path is on the processed side.
// Slots 0 through 12 correspond to horizontal edges. Slot 13 is vertical.
int slot(Key key, int position) {
    return int((key >> (4 * position)) & 15);
}
void put(Key& key, int position, int value) {
    const int shift = 4 * position;
    key = (key & ~(Key(15) << shift)) | (Key(value) << shift);
}
void pair_ends(Key& key, int first, int second) {
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
    Layer& next = layers[(row + 1) % height];
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
    if (left == 2 + above && up == 2 + row) return moves; // Would close a cycle.

    const int incoming = (left >= 2) + (up >= 2);
    for (int mask = 0; mask < 4; ++mask) {
        const bool right = mask & 1, down = mask & 2;
        if ((down && row + 1 == height) || incoming + right + down > 2) continue;
        Key result = cleared;
        put(result, row, 1);
        if (row + 1 < height) put(result, above, 1);

        // Each incoming piece contributes its other crossing edge, if any.
        // Each outgoing edge contributes another surviving end of the joined path.
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
            if (active > 0) continue; // A completed component could never rejoin.
            result = done;
        }
        if (fixed_ends <= 2) moves.occupied[mask] = next.intern(result);
    }
    return moves;
}

// Complete each row's reachable state set and store its one-cell transitions.
void build() {
    bool new_moves;
    do {
        new_moves = false;
        for (int row = 0; row < height; ++row) {
            Layer& layer = layers[row];
            while (layer.moves.size() < layer.keys.size()) {
                const Key key = layer.keys[layer.moves.size()];
                layer.moves.push_back(transitions(key, row));
                new_moves = true;
            }
        }
    } while (new_moves);
}

// Apply the max-plus operator for one full column.
void advance(Values& current) {
    for (int row = 0; row < height; ++row) {
        Values next(layers[(row + 1) % height].moves.size(), unreachable);
        const auto& choices = layers[row].moves;
        for (std::size_t i = 0; i < current.size(); ++i) {
            const int value = current[i];
            if (value == unreachable) continue;
            const Moves& moves = choices[i];
            if (moves.vacant >= 0) {
                int& best = next[moves.vacant];
                best = std::max(best, value);
            }
            for (int destination : moves.occupied) {
                if (destination >= 0) {
                    int& best = next[destination];
                    best = std::max(best, value + 1);
                }
            }
        }
        current.swap(next);
    }
}
int answer(int n) {
    constexpr std::array<int, 6> initial{13, 20, 28, 36, 43, 51};
    constexpr std::array<int, 6> offset{4, 3, 3, 3, 4, 4};
    return n <= 6 ? initial.at(n - 1) : 8 * n + offset[n % 6];
}
void require(bool test, const char* message) {
    if (!test) throw std::runtime_error(message);
}
} // namespace

int main() {
    const int start = layers[0].intern(0);
    build();
    const int finished = layers[0].index.at(done);
    const auto states = layers[0].moves.size();
    std::cout << "Boundary states: " << states << '\n';
    require(states == 620950, "Unexpected state count");
    for (auto& layer : layers) {
        layer.index.clear();
        layer.index.rehash(0);
        layer.keys.clear();
        layer.keys.shrink_to_fit();
    }

    Values v(states, unreachable), v49;
    v[start] = 0;
    for (int n = 1; n <= 55; ++n) {
        advance(v);
        require(v[finished] == answer(n), "Finite-width value mismatch");
        if (n == 49) v49 = v;
    }
    // v is now V_55. Deleting the strict coordinates constructs the lower bound W.
    Values w = v49;
    int discarded = 0;
    for (std::size_t i = 0; i < states; ++i) {
        require(v49[i] != unreachable && v[i] != unreachable, "Unexpected inaccessible state");
        require(v[i] <= v49[i] + 48, "V_55 exceeds V_49 + 48");
        if (v[i] < v49[i] + 48) {
            w[i] = unreachable;
            ++discarded;
        }
    }
    std::cout << "Strict coordinates of the upper inequality: " << discarded << '\n';
    require(discarded == 1081, "Unexpected number of strict coordinates");
    Values z = w;
    for (int r = 0; r < 6; ++r) {
        require(z[finished] == answer(49 + r), "Lower-bound base value mismatch");
        std::cout << "Lower-bound value at width " << 49 + r << ": " << z[finished] << '\n';
        advance(z);
    }
    for (std::size_t i = 0; i < states; ++i) {
        if (w[i] != unreachable) require(z[i] >= w[i] + 48, "Lower inequality fails");
    }
    std::cout << "Verified both vector inequalities and all finite base cases.\n";
}
