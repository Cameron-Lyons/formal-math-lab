// Exact frontier DP for induced paths on a 15-by-n grid.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <vector>

using Key = std::uint64_t;
constexpr int Height = 15;
constexpr Key PivotIsolated = Key{1} << 63, Finished = ~Key{0}, Invalid = ~Key{1};
using Slots = std::array<std::uint8_t, Height>;

// Each row is vacant (0), unsaturated (label 1..8), or saturated (label+8).
// Three groups of five base-17 digits fit in 63 bits (17^5 < 2^21).
Slots unpack(Key key) {
    Slots slots{};
    for (int start = 0; start < Height; start += 5) {
        unsigned group = key & ((1u << 21) - 1);
        for (int j = 0; j < 5; ++j) {
            slots[start + j] = group % 17;
            group /= 17;
        }
        key >>= 21;
    }
    return slots;
}

int label(int code) { return code > 8 ? code - 8 : code; }

Key pack(const Slots& slots, bool isolated) {
    std::array<unsigned, 9> names{};
    unsigned count = 0;
    Key key = isolated ? PivotIsolated : 0;
    for (int start = 0; start < Height; start += 5) {
        unsigned group = 0, place = 1;
        for (int j = 0; j < 5; ++j) {
            int code = slots[start + j];
            if (code) {
                unsigned& name = names[label(code)];
                if (!name) name = ++count;
                group += place * (name + (code > 8 ? 8 : 0));
            }
            place *= 17;
        }
        key |= Key(group) << (21 * (start / 5));
    }
    return key;
}

Key skip(Key key, Slots slots, int row) {
    int lost = label(slots[row]);
    if (!lost) return key & ~PivotIsolated;
    slots[row] = 0;
    bool occupied = false;
    for (int code : slots) {
        if (label(code) == lost) return pack(slots, false);
        occupied |= code != 0;
    }
    // A sealed component can only be the unique, completed snake.
    return occupied ? Invalid : Finished;
}

Key fill(Key key, Slots slots, int row) {
    // Both edges to old occupied neighbors are forced. A shared label closes a cycle.
    int left = slots[row], up = row ? slots[row - 1] : 0;
    if (left > 8 || up > 8 || (left && left == up)) return Invalid;
    // Only the pivot (above the new cell) has two remaining neighbors.
    if (up && !(key & PivotIsolated)) slots[row - 1] += 8;
    if (left && up) {
        for (auto& code : slots)
            if (label(code) == left) code = up + (code > 8 ? 8 : 0);
    }
    int name = up ? up : left;
    if (!name) {
        unsigned used = 0;
        for (int code : slots) used |= 1u << label(code);
        // The new frontier holds at most eight occupied runs, including this singleton.
        name = 1;
        while (name <= 8 && (used & (1u << name))) ++name;
        if (name > 8) throw std::logic_error("too many components");
    }
    slots[row] = name + (left && up ? 8 : 0);
    return pack(slots, !left && !up && row + 1 < Height);
}

using Edges = std::array<std::int32_t, 2>;
struct Stage {
    std::vector<int> table;
    std::vector<Key> keys;
    std::vector<Edges> edges;

    std::size_t bucket(Key key) const {
        Key hash = key ^ (key >> 33);
        hash *= UINT64_C(0xff51afd7ed558ccd);
        hash ^= hash >> 33;
        std::size_t i = hash & (table.size() - 1);
        while (table[i] >= 0 && keys[table[i]] != key) i = (i + 1) & (table.size() - 1);
        return i;
    }
    int intern(Key key) {
        if (key == Invalid) return -1;
        if (keys.size() * 4 >= table.size() * 3) {
            table.assign(std::max<std::size_t>(16, 2 * table.size()), -1);
            for (std::size_t j = 0; j < keys.size(); ++j) table[bucket(keys[j])] = int(j);
        }
        int& id = table[bucket(key)];
        if (id < 0) {
            id = int(keys.size());
            keys.push_back(key);
        }
        return id;
    }
};

bool accepting(Key key) {
    if (key == Finished) return true;
    if (!key) return false;
    for (int code : unpack(key))
        if (label(code) > 1) return false;
    return true;
}

using Stages = std::array<Stage, Height>;

// Enumerate exactly the states reachable from the empty board in every row phase.
// When a sweep adds nothing at phase zero, every known state has its outgoing edges.
void build(Stages& stages) {
    stages[0].intern(0);
    while (stages[0].edges.size() < stages[0].keys.size()) {
        for (int row = 0; row < Height; ++row) {
            Stage& here = stages[row];
            Stage& next = stages[(row + 1) % Height];
            while (here.edges.size() < here.keys.size()) {
                Key key = here.keys[here.edges.size()];
                if (key == Finished) {
                    here.edges.push_back({next.intern(Finished), -1});
                    continue;
                }
                Slots slots = unpack(key);
                int vacant = next.intern(skip(key, slots, row));
                int filled = next.intern(fill(key, slots, row));
                here.edges.push_back({vacant, filled});
            }
        }
    }
}

using Score = std::int16_t;
using Scores = std::vector<Score>;
constexpr Score Unreachable = -1;
constexpr int EarlierWidth = 40, LaterWidth = 46, Gain = 56;
static_assert(Height * LaterWidth <= std::numeric_limits<Score>::max());

void append_column(const Stages& stages, Scores& scores) {
    for (int row = 0; row < Height; ++row) {
        const auto& edges = stages[row].edges;
        Scores next(stages[(row + 1) % Height].edges.size(), Unreachable);
        for (std::size_t i = 0; i < edges.size(); ++i) {
            Score value = scores[i];
            if (value == Unreachable) continue;
            for (int take = 0; take <= 1; ++take) {
                int j = edges[i][take];
                if (j >= 0) next[j] = std::max(next[j], Score(value + take));
            }
        }
        scores.swap(next);
    }
    // Translate left to meet column one. Only a never-started snake can reach id 0.
    scores[0] = Unreachable;
}

int formula(int width) {
    switch (width) {
        case 1: return 15;
        case 2: return 23;
        case 3: return 32;
        case 4: return 41;
        case 5: return 49;
        case 8: return 77;
        case 11: return 105;
        case 13: return 123;
        case 15: return 142;
        case 19: return 179;
        case 25: return 235;
        default: return (28 * width + 10) / 3;
    }
}

int main() {
    Stages stages;
    build(stages);
    std::vector<std::uint8_t> accepted;
    for (Key key : stages[0].keys) accepted.push_back(accepting(key));
    for (Stage& stage : stages) {
        std::vector<Key>().swap(stage.keys);
        std::vector<int>().swap(stage.table);
    }

    Scores scores(accepted.size(), Unreachable), earlier;
    scores[0] = 0;
    for (int width = 1; width <= LaterWidth; ++width) {
        append_column(stages, scores);
        Score longest = Unreachable;
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
            std::cerr << "Shift failed at state " << i << '\n';
            return 1;
        }
        if (scores[i] != Unreachable) ++reachable;
    }
    std::cout << "Formula verified at every width from 1 to " << LaterWidth << ".\n"
              << "D(" << LaterWidth << ") = D(" << EarlierWidth << ") + " << Gain
              << " in all " << scores.size() << " coordinates (" << reachable << " reachable).\n";
}
