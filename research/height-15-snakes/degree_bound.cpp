// Upper bound for induced snakes using degrees, with four finite cycle checks. Build with c++ -O3 -std=c++17.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <utility>
#include <vector>

namespace degree_bound {
constexpr int height = 15;
constexpr int power3(int exponent) { return exponent == 0 ? 1 : 3 * power3(exponent - 1); }
constexpr int high_trit = power3(height), words = 3 * high_trit;
using Moves = std::array<int, 5>;
using Scores = std::vector<std::int16_t>;
constexpr std::int16_t unreachable = -1;

// A state is deficit * words + word. Each cut slot has one trit:
// 0 = vacant old cell, 1 = occupied and forbids a neighbor, 2 = occupied and
// requires a neighbor. The two low trits face the new cell from above and left.
// After the step, the downward trit is first and the rightward trit is last.
// At the bottom there is no downward neighbor, so the next top starts with 0.
template<class Emit>
void transitions(int state, int row, Emit emit) {
    const int deficit = state / words, word = state % words;
    const int above = word % 3, left = word / 3 % 3;
    const int rest = 3 * (word / 9);
    if (above != 2 && left != 2)
        emit(0, deficit * words + rest);
    if (above == 1 || left == 1) return;

    for (int outgoing = 0; outgoing < 4; ++outgoing) {
        const bool right = outgoing & 1, down = outgoing & 2;
        if (row + 1 == height && down) continue;
        const int degree = (above == 2) + (left == 2) + right + down;
        const int next_deficit = deficit + 2 - degree;
        if (degree > 2 || next_deficit > 2) continue;
        const int down_trit = row + 1 == height ? 0 : 1 + down;
        const int next_word = rest + down_trit + high_trit * (1 + right);
        emit(1 + outgoing, next_deficit * words + next_word);
    }
}

// Every nonempty path has sum (2 - degree) = 2, including a single cell.
// Requiring exactly this deficit still allows additional disjoint cycles.
bool accepts(int state) {
    if (state / words != 2) return false;
    for (int word = state % words; word; word /= 3)
        if (word % 3 == 2) return false; // An edge would leave the board.
    return true;
}

struct Graph {
    std::array<std::vector<Moves>, height> moves;
    std::vector<bool> accepting;

    // The initial state has index 0. Enumerate only reachable states in each
    // row phase. A direct array translates ternary state numbers to indices.
    Graph() {
        std::array<std::vector<int>, height> states;
        states[0].push_back(0);
        std::vector<int> index(3 * words, -1);
        while (moves[0].size() < states[0].size()) {
            for (int r = 0; r < height; ++r) {
                if (moves[r].size() == states[r].size()) continue;
                auto &next = states[(r + 1) % height];
                for (std::size_t i = 0; i < next.size(); ++i) index[next[i]] = int(i);
                while (moves[r].size() < states[r].size()) {
                    Moves edges{-1, -1, -1, -1, -1};
                    transitions(states[r][moves[r].size()], r, [&](int choice, int state) {
                        int &id = index[state];
                        if (id < 0) {
                            id = int(next.size());
                            next.push_back(state);
                        }
                        edges[choice] = id;
                    });
                    moves[r].push_back(edges);
                }
                for (int state : next) index[state] = -1;
            }
        }
        for (int state : states[0]) accepting.push_back(accepts(state));
    }
};

int relaxed_maximum(int width) {
    switch (width) {
        case 1: return 15;
        case 2: return 23;
        case 3: return 32;
        case 4: return 41;
        case 5: return 49;
        case 8: return 77;
        case 13: return 123;
        default: return (28 * width + 10) / 3;
    }
}

// At a given number of cells from the end, one bit per move says whether
// that move can attain the optimal remaining score.
using Choices = std::vector<std::vector<std::uint8_t>>;

// Follow only optimal moves. The forest here belongs to a single concrete
// board. Joining two vertices in the same tree closes a cycle, so every
// completion of that particular partial board can be discarded.
class CycleCheck {
    const Graph &graph;
    const Choices &choices;
    std::vector<int> parent; // -1 means vacant, a root is its own parent.

    int root(int cell) const {
        if (cell < 0 || parent[cell] < 0) return -1;
        while (parent[cell] != cell) cell = parent[cell];
        return cell;
    }

    bool search(int cell, int state) {
        const int remaining = int(parent.size()) - cell;
        if (remaining == 0) return graph.accepting[state];
        const int row = cell % height;
        const auto &moves = graph.moves[row][state];
        const unsigned mask = choices[remaining][state];
        if ((mask & 1u) && search(cell + 1, moves[0])) return true;
        if (mask < 2) return false;

        const int left = root(cell - height);
        const int above = row == 0 ? -1 : root(cell - 1);
        if (left >= 0 && left == above) return false;
        parent[cell] = cell;
        if (left >= 0) parent[left] = cell;
        if (above >= 0) parent[above] = cell;
        for (int c = 1; c < 5; ++c)
            if ((mask & (1u << c)) && search(cell + 1, moves[c])) return true;
        if (left >= 0) parent[left] = left;
        if (above >= 0) parent[above] = above;
        parent[cell] = -1;
        return false;
    }

public:
    CycleCheck(const Graph &g, const Choices &c, int width)
        : graph(g), choices(c), parent(height * width, -1) {}
    bool has_acyclic_maximizer() { return search(0, 0); }
};

// Work backwards from the right board edge. suffix[i] is the greatest
// remaining number of cells that can complete state i to an accepting board.
void verify(const Graph &graph) {
    constexpr int earlier_width = 28, later_width = 34, gain = 56;
    constexpr std::array<int, 4> gaps{11, 15, 19, 25};
    Scores earlier;
    Scores suffix(graph.accepting.size(), unreachable);
    for (std::size_t i = 0; i < suffix.size(); ++i)
        if (graph.accepting[i]) suffix[i] = 0;
    Choices choices(1);
    for (int remaining = 1; remaining <= height * later_width; ++remaining) {
        const int row = (height - remaining % height) % height;
        const auto &edges = graph.moves[row];
        Scores best(edges.size(), unreachable);
        std::vector<std::uint8_t> optimal(edges.size(), 0);
        for (std::size_t i = 0; i < edges.size(); ++i) {
            for (int c = 0; c < 5; ++c) {
                const int dest = edges[i][c];
                if (dest < 0 || suffix[dest] == unreachable) continue;
                const int value = suffix[dest] + (c != 0);
                if (value > best[i]) {
                    best[i] = value;
                    optimal[i] = 0;
                }
                if (value == best[i]) optimal[i] |= 1u << c;
            }
        }
        suffix.swap(best);
        if (remaining <= height * gaps.back()) choices.push_back(std::move(optimal));
        if (row != 0) continue;
        const int width = remaining / height;
        if (suffix[0] != relaxed_maximum(width))
            throw std::logic_error("relaxed maximum check failed");
        if (width == earlier_width) earlier = suffix;
        if (std::find(gaps.begin(), gaps.end(), width) != gaps.end()) {
            if (CycleCheck(graph, choices, width).has_acyclic_maximizer())
                throw std::logic_error("a relaxed maximum is attained by a snake");
            std::cout << "Width " << width << ": every relaxed maximizer of size "
                      << suffix[0] << " contains a cycle.\n";
        }
        if (width == gaps.back()) choices.clear();
    }
    for (std::size_t i = 0; i < suffix.size(); ++i) {
        const int bound = earlier[i] == unreachable ? unreachable : earlier[i] + gain;
        if (suffix[i] > bound) throw std::logic_error("six-column bound failed");
    }
    std::cout << "Checked the degree bound through width " << later_width << ".\n"
              << "U(" << later_width << ") <= U(" << earlier_width << ") + " << gain
              << " on all " << suffix.size() << " boundary states.\n";
}
} // namespace degree_bound

int main() {
    degree_bound::verify(degree_bound::Graph{});
}
