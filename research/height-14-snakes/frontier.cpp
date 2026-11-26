// Exact row-by-row frontier calculation for longest snakes in 14-by-n grids.
// Build: c++ -std=c++17 -O3 frontier.cpp -o frontier
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>

using Key = std::uint64_t;
using Scores = std::vector<int>;
constexpr int Height = 14;
constexpr int Unreachable = -1;
constexpr Key PivotHasDegreeZero = Key{1} << 63;
constexpr Key Finished = ~Key{0};
constexpr Key Invalid = ~Key{1};

// A row is vacant (0), unsaturated with component label 1..8, or saturated
// with code 9..16. Each pair of rows is a two-digit base-17 number < 289,
// stored in 9 bits. Seven pairs occupy 63 bits, leaving a bit for the pivot.
// The sentinel words each contain a pair outside the valid range.
int slot(Key key, int row) {
    unsigned pair = (key >> (9 * (row / 2))) & 511;
    return row % 2 ? pair / 17 : pair % 17;
}

Key replace(Key key, int row, int previous, int value) {
    Key unit = Key(row % 2 ? 17 : 1) << (9 * (row / 2));
    return key - previous * unit + value * unit;
}

int label(int code) {
    return code > 8 ? code - 8 : code;
}

Key canonical(Key key) {
    int labels[9] = {};
    int count = 0;
    for (int row = 0; row < Height; ++row) {
        int code = slot(key, row);
        if (code == 0) continue;
        int component = label(code);
        if (labels[component] == 0) labels[component] = ++count;
        key = replace(key, row, code, labels[component] + (code > 8 ? 8 : 0));
    }
    return key;
}

Key advance(Key key, int row, bool fill) {
    if (key == Finished) return fill ? Invalid : Finished;
    // Only the previous pivot, immediately above this cell, can still have
    // two unseen neighbors. Its zero-degree flag tells us whether adding
    // the downward edge saturates it.
    int left = slot(key, row), above = row ? slot(key, row - 1) : 0;
    int leftLabel = label(left), aboveLabel = label(above);
    bool isolatedPivot = key & PivotHasDegreeZero;
    key &= ~PivotHasDegreeZero;

    if (!fill) {
        if (!left) return key;
        key = replace(key, row, left, 0);
        for (int i = 0; i < Height; ++i) {
            if (label(slot(key, i)) == leftLabel) return canonical(key);
        }
        // Once sealed, a component can only be the complete, unique snake.
        return key == 0 ? Finished : Invalid;
    }

    // Both edges to occupied old neighbors are forced by inducedness.
    if (left > 8 || above > 8) return Invalid;
    if (leftLabel && leftLabel == aboveLabel) return Invalid; // A cycle.
    if (above && !isolatedPivot) key = replace(key, row - 1, above, above + 8);
    if (left && above) {
        for (int i = 0; i < Height; ++i) {
            int code = slot(key, i);
            if (label(code) == leftLabel)
                key = replace(key, i, code, aboveLabel + (code > 8 ? 8 : 0));
        }
    }
    int newLabel = above ? aboveLabel : leftLabel;
    if (!newLabel) {
        unsigned present = 0;
        for (int i = 0; i < Height; ++i) present |= 1u << label(slot(key, i));
        // The two vertical pieces of the frontier have lengths r and 14-r.
        // They have at most ceil(r/2)+ceil((14-r)/2) <= 8 occupied runs.
        for (newLabel = 1; newLabel <= 8 && (present & (1u << newLabel)); ++newLabel) {}
        if (newLabel > 8) throw std::logic_error("component label overflow");
    }
    key = replace(key, row, slot(key, row), newLabel + (above && left ? 8 : 0));
    if (row + 1 < Height && !above && !left) key |= PivotHasDegreeZero;
    return canonical(key);
}

// Store only key indices in an open-addressed table. Equality always compares
// the full key; hashing affects construction time but never merges states.
struct Stage {
    std::vector<int> table;
    std::vector<Key> keys;
    std::vector<std::array<int, 2>> edges;

    std::size_t bucket(Key key) const {
        key ^= key >> 33;
        key *= UINT64_C(0xff51afd7ed558ccd);
        key ^= key >> 33;
        return key & (table.size() - 1);
    }
    void grow() {
        table.assign(std::max<std::size_t>(16, 2 * table.size()), -1);
        for (std::size_t i = 0; i < keys.size(); ++i) {
            std::size_t b = bucket(keys[i]);
            while (table[b] != -1) b = (b + 1) & (table.size() - 1);
            table[b] = int(i);
        }
    }
    int id(Key key) {
        if (key == Invalid) return -1;
        if (keys.size() * 4 >= table.size() * 3) grow();
        std::size_t b = bucket(key);
        while (table[b] != -1) {
            if (keys[table[b]] == key) return table[b];
            b = (b + 1) & (table.size() - 1);
        }
        table[b] = int(keys.size());
        keys.push_back(key);
        return table[b];
    }
};

bool accepting(Key key) {
    if (key == Finished) return true;
    if (key == 0) return false;
    for (int row = 0; row < Height; ++row)
        if (label(slot(key, row)) > 1) return false;
    return true;
}

int formula(int width) {
    constexpr std::array<int, 17> initial{
        14, 21, 30, 38, 46, 55, 64, 72, 82, 89, 98, 107, 115, 123, 134, 142, 150};
    constexpr std::array<int, 6> offsets{3, 12, 20, 30, 38, 47};
    if (width <= 17) return initial.at(width - 1);
    return 52 * (width / 6) + offsets[width % 6];
}

int main() {
    std::array<Stage, Height> stages;
    stages[0].id(0);
    // Starting at the empty board, close all phases under skip and fill.
    while (stages[0].edges.size() < stages[0].keys.size()) {
        for (int row = 0; row < Height; ++row) {
            Stage &here = stages[row], &next = stages[(row + 1) % Height];
            while (here.edges.size() < here.keys.size()) {
                Key key = here.keys[here.edges.size()];
                int skip = next.id(advance(key, row, false));
                int fill = next.id(advance(key, row, true));
                here.edges.push_back({skip, fill});
            }
        }
    }
    const auto &boundary = stages[0].keys;
    std::vector<bool> accepted;
    for (Key key : boundary) accepted.push_back(accepting(key));
    std::cout << "Column-boundary states = " << boundary.size() << std::endl;
    for (Stage &stage : stages) {
        stage.table.clear();
        stage.table.shrink_to_fit();
        stage.keys.clear();
        stage.keys.shrink_to_fit();
    }

    Scores scores(accepted.size(), Unreachable);
    scores[0] = 0;
    constexpr int EarlierWidth = 41, LaterWidth = 47, Gain = 52;
    Scores earlier;
    for (int width = 1; width <= LaterWidth; ++width) {
        for (int row = 0; row < Height; ++row) {
            const auto &edges = stages[row].edges;
            Scores next(stages[(row + 1) % Height].edges.size(), Unreachable);
            for (std::size_t i = 0; i < edges.size(); ++i) {
                if (scores[i] == Unreachable) continue;
                for (int fill : {0, 1}) {
                    int j = edges[i][fill];
                    if (j >= 0) next[j] = std::max(next[j], scores[i] + fill);
                }
            }
            scores.swap(next);
        }
        // Translate a longest snake to meet the first column. A live or sealed
        // snake cannot return to the never-started state, whose index is zero.
        scores[0] = Unreachable;
        int longest = Unreachable;
        for (std::size_t i = 0; i < scores.size(); ++i)
            if (accepted[i]) longest = std::max(longest, scores[i]);
        if (longest != formula(width)) {
            std::cerr << "Formula mismatch at width " << width << ", got " << longest << '\n';
            return 1;
        }
        if (width == EarlierWidth) earlier = scores;
    }
    std::size_t reachable = 0;
    for (std::size_t i = 0; i < scores.size(); ++i) {
        int expected = earlier[i] == Unreachable ? Unreachable : earlier[i] + Gain;
        if (scores[i] != expected) {
            std::cerr << "Period certificate failed at state " << i << '\n';
            return 1;
        }
        if (scores[i] != Unreachable) ++reachable;
    }
    std::cout << "Formula verified for widths 1 through " << LaterWidth << ".\n"
              << "D(" << LaterWidth << ") = D(" << EarlierWidth << ") + " << Gain
              << " in all coordinates (" << reachable << " reachable).\n";
}
