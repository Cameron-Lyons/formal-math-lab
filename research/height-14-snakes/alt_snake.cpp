// Verify the exact longest induced path length for every 14-by-n grid.
// Build with: c++ -O3 -std=c++17 alt_snake.cpp -o verify
// Run with: ./verify
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>

namespace {
constexpr int height = 14;
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
// The 14 horizontal slots have four bits each. The vertical slot has five:
// if its mate is a horizontal slot, the horizontal mate is implicit.
int vertical(Key key) {
    return int(key >> (4 * above));
}
int slot(Key key, int position) {
    if (position == above) return vertical(key);
    if (vertical(key) == 2 + position) return 2 + above;
    return int((key >> (4 * position)) & 15);
}
void put(Key& key, int position, int value) {
    const int shift = 4 * position;
    const Key mask = position == above ? 31 : 15;
    if (position != above && value == 2 + above) value = 0;
    key = (key & ~(mask << shift)) | (Key(value) << shift);
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
    std::vector<int> index;
    std::vector<Key> keys;
    std::vector<Moves> moves;

    // An open-addressed table of indices avoids storing a second copy of each key.
    std::size_t bucket(Key key) const {
        Key hash = key ^ (key >> 30);
        hash *= 0xbf58476d1ce4e5b9ULL;
        hash ^= hash >> 27;
        hash *= 0x94d049bb133111ebULL;
        hash ^= hash >> 31;
        std::size_t pos = hash & (index.size() - 1);
        while (index[pos] >= 0 && keys[index[pos]] != key)
            pos = (pos + 1) & (index.size() - 1);
        return pos;
    }

    int intern(Key key) {
        if (4 * (keys.size() + 1) > 3 * index.size()) {
            index.assign(std::max<std::size_t>(16, 2 * index.size()), -1);
            for (std::size_t i = 0; i < keys.size(); ++i) index[bucket(keys[i])] = int(i);
        }
        int& id = index[bucket(key)];
        if (id < 0) {
            id = int(keys.size());
            keys.push_back(key);
        }
        return id;
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

int formula(int width) {
    constexpr std::array<int, 17> initial{
        14, 21, 30, 38, 46, 55, 64, 72, 82, 89, 98, 107, 115, 123, 134, 142, 150
    };
    constexpr std::array<int, 6> offset{3, 12, 20, 30, 38, 47};
    if (width <= int(initial.size())) return initial.at(width - 1);
    return 52 * (width / 6) + offset[width % 6];
}

} // namespace

int main() {
    const int start = layers[0].intern(0);
    build();
    const int finished = layers[0].index.at(layers[0].bucket(done));
    const std::size_t states = layers[0].moves.size();
    if (finished < 0 || states != 1776869)
        throw std::runtime_error("Unexpected edge-state graph");
    for (Layer& layer : layers) {
        std::vector<int>().swap(layer.index);
        std::vector<Key>().swap(layer.keys);
    }

    Values current(states, unreachable), at41;
    current[start] = 0;
    for (int width = 1; width <= 47; ++width) {
        advance(current);
        // A longest snake can be translated to meet the first column.
        // Only the never-started configuration is removed at a column cut.
        current[start] = unreachable;
        if (current[finished] != formula(width)) {
            std::cerr << "Formula mismatch at width " << width << ": got "
                      << current[finished] << '\n';
            return 1;
        }
        if (width == 41) at41 = current;
    }
    std::size_t reachable = 0;
    for (std::size_t i = 0; i < states; ++i) {
        const int expected = at41[i] == unreachable ? unreachable : at41[i] + 52;
        if (current[i] != expected) {
            std::cerr << "Period mismatch at edge state " << i << '\n';
            return 1;
        }
        if (current[i] != unreachable) ++reachable;
    }
    std::cout << "All widths 1 through 47 agree with the formula.\n"
              << "D(47) = D(41) + 52 on all " << states << " edge states ("
              << reachable << " reachable).\n";
}
