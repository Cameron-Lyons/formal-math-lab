// Exhaust all three-terminal profiles of graphs of treewidth at most three
// with internal minimum degree three and no cycle of length 4, 8, or 16.
// c++ -std=c++23 -O2 -Wall -Wextra -Wpedantic -Werror scripts/treewidth_three.cpp -o /tmp/eg64-treewidth-three
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <map>
#include <stdexcept>
#include <vector>

namespace {

using Bits = std::uint64_t;
using Graph = std::vector<Bits>;
using Triple = std::array<int, 3>;
constexpr Triple boundary{0, 1, 2};
constexpr std::array<Triple, 3> faces{{{0, 1, 3}, {0, 2, 3}, {1, 2, 3}}};
constexpr std::array<std::array<int, 2>, 3> pairs{{{0, 1}, {0, 2}, {1, 2}}};
constexpr int forbidden = (1 << 4) | (1 << 8) | (1 << 16);

Bits bit(int vertex) {
    return Bits{1} << vertex;
}

int take(Bits& set) {
    int first = std::countr_zero(set);
    set &= set - 1;
    return first;
}

void edge(Graph& graph, int a, int b) {
    graph[a] |= bit(b);
    graph[b] |= bit(a);
}

// The small representatives use one machine word per neighborhood. Exceeding
// the representation aborts the proof attempt instead of dropping a graph.
void glue(Graph& graph, const Graph& child, Triple where) {
    int offset = static_cast<int>(graph.size()) - 3;
    if (offset + child.size() > 64) {
        throw std::runtime_error("representative exceeds one machine word");
    }
    graph.resize(offset + child.size());
    auto label = [&](int i) { return i < 3 ? where[i] : offset + i; };
    for (int i = 0; i < static_cast<int>(child.size()); ++i) {
        for (Bits neighbors = child[i]; neighbors;) {
            graph[label(i)] |= bit(label(take(neighbors)));
        }
    }
}

bool cycleFrom(const Graph& graph, int start, int v, Bits seen, int length,
               int targets, int maxSteps) {
    if (length >= 3 && ((targets >> (length + 1)) & 1) &&
        (graph[v] & bit(start))) {
        return true;
    }
    if (length == maxSteps) return false;
    for (Bits next = graph[v] & ~seen; next;) {
        int w = take(next);
        if (cycleFrom(graph, start, w, seen | bit(w), length + 1, targets, maxSteps)) return true;
    }
    return false;
}

// Every cycle new to a composition meets its central bag. Only those starts
// are necessary when the inputs are already certified free of forbidden cycles.
bool forbiddenCycle(const Graph& graph, int bagSize, int targets = forbidden) {
    int maxSteps = std::bit_width(static_cast<unsigned>(targets)) - 2;
    for (int i = 0; i < bagSize; ++i) {
        // Examine only cycles whose least vertex is i.
        if (cycleFrom(graph, i, i, bit(i) | (bit(i) - 1), 0, targets, maxSteps)) return true;
    }
    return false;
}

struct Profile {
    Triple degree{};
    // Each pair has two length sets, respectively avoiding and visiting the
    // third terminal. Bit l records an l-edge simple path, for 1 <= l <= 15.
    std::array<std::array<int, 2>, 3> paths{};
    auto operator<=>(const Profile&) const = default;
};

void pathsFrom(const Graph& graph, int start, int v, Bits seen, int length,
               Profile& profile) {
    if (start < v && v < 3) {
        int pair = start == 0 ? v - 1 : 2;
        int third = 3 - start - v;
        profile.paths[pair][(seen & bit(third)) != 0] |= 1 << length;
    }
    if (length == 15) return;
    for (Bits next = graph[v] & ~seen; next;) {
        int w = take(next);
        pathsFrom(graph, start, w, seen | bit(w), length + 1, profile);
    }
}

Profile profileOf(const Graph& graph) {
    Profile result;
    for (int i = 0; i < 3; ++i) {
        result.degree[i] = std::min(3, std::popcount(graph[i]));
    }
    for (int start : {0, 1}) {
        pathsFrom(graph, start, start, bit(start), 0, result);
    }
    return result;
}

// The two faces share exactly the endpoints of the specified pair. One
// path from each forms a simple cycle, even when either uses its third port.
bool incompatible(const Profile& left, int i, const Profile& right, int j) {
    unsigned a = left.paths[i][0] | left.paths[i][1];
    unsigned b = right.paths[j][0] | right.paths[j][1];
    while (a) {
        int length = std::countr_zero(a);
        if ((b << length) & forbidden) return true;
        a &= a - 1;
    }
    return false;
}

// Extend a partial isomorphism, keeping the three named boundary vertices
// fixed at the specified images. Images of assigned vertices are distinct.
bool isomorphic(const Graph& graph, const Graph& model, Triple ports) {
    if (graph.size() != model.size()) return false;
    const int n = static_cast<int>(graph.size());
    std::vector<int> image(n, -1);
    Bits used = 0;
    auto agrees = [&](int v, int target) {
        if (std::popcount(graph[v]) != std::popcount(model[target])) return false;
        for (int w = 0; w < n; ++w) {
            if (image[w] >= 0 && bool(graph[v] & bit(w)) != bool(model[target] & bit(image[w]))) return false;
        }
        return true;
    };
    for (int v = 0; v < 3; ++v) {
        const int target = ports[v];
        if ((used & bit(target)) || !agrees(v, target)) return false;
        used |= bit(target);
        image[v] = target;
    }
    auto extend = [&](auto&& self, Bits assigned, Bits taken) -> bool {
        int vertex = -1, score = -1;
        for (int v = 3; v < n; ++v) {
            const int neighbors = std::popcount(graph[v] & assigned);
            if (image[v] < 0 && neighbors > score) {
                vertex = v;
                score = neighbors;
            }
        }
        if (vertex < 0) return true;
        for (int target = 0; target < n; ++target) {
            if ((taken & bit(target)) || !agrees(vertex, target)) continue;
            image[vertex] = target;
            if (self(self, assigned | bit(vertex), taken | bit(target))) return true;
            image[vertex] = -1;
        }
        return false;
    };
    return extend(extend, bit(0) | bit(1) | bit(2), used);
}

struct Piece {
    Graph graph;
    Triple ports;
};

std::array<Piece, 4> twoDegreePieces() {
    Graph triangle(3);
    for (auto [a, b] : pairs) edge(triangle, a, b);
    Graph symmetric(7);
    for (int i = 0; i < 3; ++i) {
        edge(symmetric, i, 3);
        edge(symmetric, i, 4 + i);
        edge(symmetric, 4 + i, 4 + (i + 1) % 3);
    }
    constexpr std::array<std::array<int, 2>, 9> h7Edges{{
        {1,3}, {3,4}, {4,2}, {5,1}, {2,6}, {3,5}, {5,0}, {0,6}, {6,4}
    }};
    Graph h7(7), h15(15);
    for (auto [v, w] : h7Edges) {
        edge(h7, v, w);
        edge(h15, v, w);
        edge(h15, v + 7, w + 7);
    }
    edge(h15, 1, 8);
    edge(h15, 2, 14);
    edge(h15, 14, 9);
    return {{{triangle, boundary}, {h7, boundary}, {symmetric, boundary}, {h15, {0,7,14}}}};
}

bool matchesPiece(const Graph& graph, const Piece& piece) {
    Triple ports = piece.ports;
    do {
        if (isomorphic(graph, piece.graph, ports)) return true;
    } while (std::next_permutation(ports.begin(), ports.end()));
    return false;
}

struct State {
    Profile profile;
    Graph graph;
};

class Catalogue {
public:
    Catalogue() { record(Graph(3)); }

    void check() {
        std::size_t old = 0;
        while (old < states.size()) {
            std::size_t count = states.size();
            std::cout << "profiles " << count << '\n';
            for (std::size_t i = 0; i < count; ++i) {
                for (std::size_t j = std::max(old, i); j < count; ++j) {
                    Graph merged = states[i].graph;
                    glue(merged, states[j].graph, boundary);
                    examine(merged, 3);
                }
            }
            for (std::size_t i = 0; i < count; ++i) {
                for (std::size_t j = 0; j < count; ++j) {
                    if (incompatible(states[i].profile, 1, states[j].profile, 1)) continue;
                    for (std::size_t k = 0; k < count; ++k) {
                        if (std::max({i, j, k}) < old) continue;
                        if (incompatible(states[i].profile, 2, states[k].profile, 1)) continue;
                        if (incompatible(states[j].profile, 2, states[k].profile, 2)) continue;
                        extend(i, j, k);
                    }
                }
            }
            old = count;
        }
        if (states.size() != 62 || maxInterior != 15 ||
            pieceCounts != std::array<int, 4>{1,3,1,3}) {
            throw std::runtime_error("unexpected three-boundary classification");
        }
        std::cout << states.size() << " boundary-fixing isomorphism classes, maximum "
                  << maxInterior << " interior vertices, all interiors cubic\n";
        std::cout << "clean roots with all three boundary degrees at least two: "
                  << pieceCounts[0] << " triangle, " << pieceCounts[1] << " H7, "
                  << pieceCounts[2] << " H7-prime, " << pieceCounts[3] << " H15\n";
        std::cout << states.size() << " distinct profiles, " << finalMasks
                  << " root completions, " << cleanMasks
                  << " clean completions all have maximum boundary degree at most 2\n";
    }

private:
    std::map<Profile, std::size_t> index;
    std::vector<State> states;
    std::size_t finalMasks = 0;
    std::size_t cleanMasks = 0;
    std::size_t maxInterior = 0;
    const std::array<Piece, 4> pieces = twoDegreePieces();
    std::array<int, 4> pieceCounts{};

    void record(Graph graph) {
        Profile profile = profileOf(graph);
        auto [entry, inserted] = index.emplace(profile, states.size());
        if (!inserted) {
            if (!isomorphic(graph, states[entry->second].graph, boundary)) {
                throw std::runtime_error("same profile, different labelled-boundary graph");
            }
            return;
        }
        for (std::size_t v = 3; v < graph.size(); ++v) {
            if (std::popcount(graph[v]) != 3) {
                throw std::runtime_error("clean representative has a noncubic interior vertex");
            }
        }
        maxInterior = std::max(maxInterior, graph.size() - 3);
        states.push_back({profile, graph});
        for (int mask = 0; mask < 8; ++mask) {
            Graph complete = graph;
            for (int i = 0; i < 3; ++i) {
                if ((mask >> i) & 1) edge(complete, pairs[i][0], pairs[i][1]);
            }
            ++finalMasks;
            if (forbiddenCycle(complete, 3)) continue;
            ++cleanMasks;
            bool allTwo = true;
            for (int v = 0; v < 3; ++v) {
                const int degree = std::popcount(complete[v]);
                if (degree < 2) allTwo = false;
                if (degree >= 3) {
                    throw std::runtime_error("clean completion has a boundary degree of three or more");
                }
            }
            if (allTwo) {
                int matches = 0;
                for (std::size_t i = 0; i < pieces.size(); ++i) {
                    if (matchesPiece(complete, pieces[i])) {
                        ++pieceCounts[i];
                        ++matches;
                    }
                }
                if (matches != 1) throw std::runtime_error("unclassified three-port completion");
            }
        }
    }

    void examine(const Graph& graph, int bagSize) {
        if (!forbiddenCycle(graph, bagSize)) record(graph);
    }

    void extend(std::size_t i, std::size_t j, std::size_t k) {
        Graph base(4);
        glue(base, states[i].graph, faces[0]);
        glue(base, states[j].graph, faces[1]);
        glue(base, states[k].graph, faces[2]);
        for (int mask = 0; mask < 8; ++mask) {
            Graph graph = base;
            for (int v = 0; v < 3; ++v) {
                if ((mask >> v) & 1) edge(graph, v, 3);
            }
            if (std::popcount(graph[3]) >= 3) examine(graph, 4);
        }
    }
};

void checkSharpness() {
    constexpr std::array<Triple, 34> neighbors{{
        {3,26,28}, {5,19,22}, {13,16,18}, {0,9,11}, {7,8,15}, {1,7,10},
        {8,9,10}, {4,5,8}, {4,6,7}, {3,6,10}, {5,6,9}, {3,13,14},
        {14,15,16}, {2,11,14}, {11,12,13}, {4,12,16}, {2,12,15}, {20,30,33},
        {2,19,20}, {1,18,20}, {17,18,19}, {24,25,32}, {1,24,27}, {25,26,27},
        {21,22,25}, {21,23,24}, {0,23,27}, {22,23,26}, {0,30,31}, {31,32,33},
        {17,28,31}, {28,29,30}, {21,29,33}, {17,29,32}
    }};
    constexpr std::array<int, 34> order{
        4,6,7,10,8,5,9,11,12,13,16,14,15,2,19,18,1,3,20,21,23,24,27,25,26,22,33,32,0,17,28,29,30,31
    };
    constexpr std::array<int, 16> cycle{
        0,26,27,22,24,25,21,32,33,17,20,18,2,13,11,3
    };
    Graph graph(neighbors.size());
    for (int v = 0; v < static_cast<int>(neighbors.size()); ++v) {
        for (int w : neighbors[v]) {
            if (w < 0 || w >= static_cast<int>(neighbors.size()) || w == v) {
                throw std::runtime_error("invalid example edge");
            }
            edge(graph, v, w);
        }
    }
    for (Bits row : graph) {
        if (std::popcount(row) != 3) throw std::runtime_error("example degree check failed");
    }
    if (forbiddenCycle(graph, graph.size(), (1 << 4) | (1 << 8))) {
        throw std::runtime_error("example contains a 4- or 8-cycle");
    }
    Bits used = 0;
    for (std::size_t i = 0; i < cycle.size(); ++i) {
        int v = cycle[i], w = cycle[(i + 1) % cycle.size()];
        if ((used & bit(v)) || !(graph[v] & bit(w))) {
            throw std::runtime_error("invalid example cycle");
        }
        used |= bit(v);
    }
    Bits remaining = (bit(neighbors.size()) - 1);
    for (int v : order) {
        Bits bag = graph[v] & remaining;
        if (!(remaining & bit(v)) || std::popcount(bag) > 3) {
            throw std::runtime_error("invalid example elimination");
        }
        remaining ^= bit(v);
        for (Bits todo = bag; todo;) {
            int w = take(todo);
            graph[w] |= bag ^ bit(w);
        }
    }
    if (remaining) throw std::runtime_error("incomplete example elimination");
    std::cout << "34-vertex cubic example has width at most 3 and shortest dyadic cycle 16\n";
}

} // namespace

int main() {
    Catalogue catalogue;
    catalogue.check();
    checkSharpness();
}
