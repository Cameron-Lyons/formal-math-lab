// Reproduce the height-13 snake formula with a finite max-plus calculation.
// Build: c++ -std=c++17 -O3 frontier.cpp -o frontier
// Run:   ./frontier
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <unordered_map>
#include <vector>

using Key = std::uint64_t;
constexpr int Height = 13;
constexpr int Unreachable = -1;

// Each row uses four bits. Low three bits give its component label (0 if
// empty); the fourth bit says its degree in the processed graph is two.
// The most recently inserted vertex can still have two unseen neighbors.
// For that vertex alone, distinguish degrees zero and one as well.
constexpr Key PivotHasDegreeZero = Key{1} << 60;
constexpr Key Finished = Key{1} << 61;
constexpr Key Invalid = Key{1} << 62;
constexpr int Saturated = 8;
constexpr int LabelMask = 7;

int slot(Key key, int row) {
    return (key >> (4 * row)) & 15;
}

Key replace(Key key, int row, int value) {
    return (key & ~(Key{15} << (4 * row))) | (Key(value) << (4 * row));
}

Key canonical(Key key) {
    int labels[8] = {};
    int count = 0;
    Key result = key & PivotHasDegreeZero;
    for (int row = 0; row < Height; ++row) {
        int value = slot(key, row), label = value & LabelMask;
        if (label == 0) continue;
        if (labels[label] == 0) labels[label] = ++count;
        result |= Key(labels[label] | (value & Saturated)) << (4 * row);
    }
    return result;
}

Key advance(Key key, int row, bool fill) {
    if (key == Finished) return fill ? Invalid : Finished;
    int left = slot(key, row), above = row ? slot(key, row - 1) : 0;
    int leftLabel = left & LabelMask, aboveLabel = above & LabelMask;
    bool pivotWasIsolated = key & PivotHasDegreeZero;
    key &= ~PivotHasDegreeZero;

    if (!fill) {
        if (left == 0) return key;
        // The old left vertex is the only vertex leaving the frontier.
        key = replace(key, row, 0);
        for (int i = 0; i < Height; ++i) {
            if ((slot(key, i) & LabelMask) == leftLabel) return canonical(key);
        }
        // This component is sealed. It must be the entire final snake.
        return key == 0 ? Finished : Invalid;
    }

    // Both incident edges to occupied old neighbors are mandatory.
    if ((left & Saturated) || (above & Saturated)) return Invalid;
    if (leftLabel && leftLabel == aboveLabel) return Invalid;  // A cycle.
    if (above && !pivotWasIsolated) key = replace(key, row - 1, above | Saturated);
    if (left && above) {
        for (int i = 0; i < Height; ++i) {
            int value = slot(key, i);
            if ((value & LabelMask) == leftLabel)
                key = replace(key, i, (value & Saturated) | aboveLabel);
        }
    }
    int label = above ? aboveLabel : leftLabel;
    if (label == 0) {
        unsigned present = 0;
        for (int i = 0; i < Height; ++i)
            present |= 1u << (slot(key, i) & LabelMask);
        // The two vertical frontier segments have lengths r and 13-r. Their
        // occupied runs number at most ceil(r/2)+ceil((13-r)/2) = 7.
        for (label = 1; label <= 7 && (present & (1u << label)); ++label) {}
        if (label > 7) throw std::logic_error("component label overflow");
    }
    key = replace(key, row, label | ((above && left) ? Saturated : 0));
    if (row + 1 < Height && !above && !left) key |= PivotHasDegreeZero;
    return canonical(key);
}

struct Stage {
    std::unordered_map<Key, int> ids;
    std::vector<Key> keys;
    std::vector<std::array<int, 2>> edges;
    int id(Key key) {
        if (key == Invalid) return -1;
        auto [it, inserted] = ids.try_emplace(key, int(keys.size()));
        if (inserted) keys.push_back(key);
        return it->second;
    }
};

bool accepting(Key key) {
    if (key == Finished) return true;
    if (key == 0) return false;
    for (int row = 0; row < Height; ++row)
        if ((slot(key, row) & LabelMask) > 1) return false;
    return true;
}

int formula(int n) {
    constexpr int initial[] = {0, 13, 20, 28, 36, 43, 51};
    if (n <= 6) return initial[n];
    return 8 * n + (n % 6 == 0 || n % 6 >= 4 ? 4 : 3);
}

int main() {
    std::array<Stage, Height> stages;
    stages[0].id(0);
    // Close the set of states under either decision at the next square.
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
    std::cout << "Column-boundary states = " << boundary.size() << '\n';
    for (Stage &stage : stages) {
        stage.ids.clear();
        stage.ids.rehash(0);
    }
    std::vector<bool> accepted;
    for (Key key : boundary) accepted.push_back(accepting(key));
    std::vector<int> scores(boundary.size(), Unreachable), at53;
    scores[0] = 0;
    for (int width = 1; width <= 59; ++width) {
        for (int row = 0; row < Height; ++row) {
            const auto &edges = stages[row].edges;
            std::vector<int> next(stages[(row + 1) % Height].keys.size(), Unreachable);
            for (std::size_t i = 0; i < edges.size(); ++i) {
                if (scores[i] == Unreachable) continue;
                for (int fill : {0, 1}) {
                    int j = edges[i][fill];
                    if (j >= 0) next[j] = std::max(next[j], scores[i] + fill);
                }
            }
            scores.swap(next);
        }
        // A longest snake can be translated to touch the first column.
        // Discard the never-started state; Finished is a different state.
        scores[0] = Unreachable;
        int longest = Unreachable;
        for (std::size_t i = 0; i < scores.size(); ++i)
            if (accepted[i]) longest = std::max(longest, scores[i]);
        if (longest != formula(width)) {
            std::cerr << "Mismatch at width " << width << ": got " << longest << '\n';
            return 1;
        }
        if (width == 53) at53 = scores;
    }
    std::size_t reachable = 0;
    for (std::size_t i = 0; i < scores.size(); ++i) {
        int expected = at53[i] == Unreachable ? Unreachable : at53[i] + 48;
        if (scores[i] != expected) {
            std::cerr << "Period certificate failed at state " << i << '\n';
            return 1;
        }
        if (scores[i] != Unreachable) ++reachable;
    }
    std::cout << "Formula verified for widths 1 through 59.\n"
              << "D(59) = D(53) + 48 in all coordinates ("
              << reachable << " reachable).\n";
}
