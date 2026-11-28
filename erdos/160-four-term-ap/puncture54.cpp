// c++ -std=c++20 -O3 -march=native puncture54.cpp -o puncture54
// ./puncture54 six_color_punctures.txt
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

namespace {
constexpr int N = 54, K = 5;
using Mask = std::uint64_t;
Mask bit(int x) {
    return Mask{1} << x;
}
int first(Mask mask) {
    return std::countr_zero(mask);
}
Mask interval(int n) {
    return bit(n) - 1;
}

// Check the explicit six-color words and their reflections directly.
void check_words(const char *path) {
    std::ifstream in(path);
    if (!in)
        throw std::runtime_error("cannot read puncture words");
    std::string word;
    Mask covered = 0;
    int count = 0;
    while (in >> word) {
        if (word.size() != N || word.find_first_not_of("012345") != std::string::npos)
            throw std::runtime_error("expected a 54-digit word in colors 0 through 5");
        ++count;
        for (int orientation = 0; orientation < 2; ++orientation) {
            Mask common = interval(N);
            for (int d = 1; 3 * d < N; ++d)
                for (int a = 0; a + 3 * d < N; ++a) {
                    Mask e = 0;
                    unsigned colors = 0;
                    for (int j = 0; j < 4; ++j) {
                        int p = a + j * d;
                        e |= bit(p);
                        colors |= 1u << (word[p] - '0');
                    }
                    if (std::popcount(colors) < 3)
                        common &= e;
                }
            covered |= common;
            std::reverse(word.begin(), word.end());
        }
    }
    if (covered != interval(N))
        throw std::runtime_error("a deletion lacks a witness");
    std::cout << count << " six-color words and their reversals cover all 54 deletions.\n";
}

// If two vertices of a 4-AP have the same color, the other two must have
// distinct colors and neither may have that color. These implications fully
// characterize valid colorings. Search propagates each such implication.
struct FiveColorSearch {
    struct State {
        Mask open{}, forced{};
        std::array<Mask, K> classes{};
        std::array<Mask, N> unequal{};
        std::array<unsigned char, N> domain{}, value{};
        int used = 0;
    };
    using Pair = std::array<int, 2>;
    std::array<std::array<std::vector<Pair>, N>, N> other;
    std::array<Mask, N> neighbor{};
    std::array<int, N> degree{}, order{};
    Mask vertices;
    int length;
    std::uint64_t nodes = 0;

    FiveColorSearch(int n, Mask set) : vertices(set), length(n) {
        for (int d = 1; 3 * d < n; ++d)
            for (int a = 0; a + 3 * d < n; ++a) {
                std::array<int, 4> e{a, a + d, a + 2 * d, a + 3 * d};
                if (std::any_of(e.begin(), e.end(), [&](int x) { return !(vertices & bit(x)); }))
                    continue;
                for (int x : e)
                    ++degree[x];
                for (int x : e)
                    for (int y : e)
                        if (x != y) {
                            Pair rest{};
                            int j = 0;
                            for (int z : e)
                                if (z != x && z != y)
                                    rest[j++] = z;
                            other[x][y].push_back(rest);
                            neighbor[x] |= bit(y);
                        }
            }
        for (int i = 0; i < n; ++i)
            order[i] = i;
        std::stable_sort(order.begin(), order.begin() + n,
                         [&](int x, int y) { return degree[x] > degree[y]; });
    }
    bool remove(State &s, int x, unsigned mask) const {
        unsigned dom = (s.domain[x] &= ~mask);
        if (!dom)
            return false;
        if (std::has_single_bit(dom))
            s.forced |= bit(x);
        return true;
    }
    bool assign(State &s, int x, int c) const {
        unsigned mask = 1u << c;
        for (Mask m = s.unequal[x] & s.open; m; m &= m - 1)
            if (!remove(s, first(m), mask))
                return false;
        for (Mask m = s.classes[c] & neighbor[x]; m; m &= m - 1)
            for (auto [a, b] : other[x][first(m)]) {
                int ca = s.value[a], cb = s.value[b];
                if (ca == c || cb == c || (ca < K && ca == cb))
                    return false;
                if (ca == K && !remove(s, a, mask | (cb < K ? 1u << cb : 0)))
                    return false;
                if (cb == K && !remove(s, b, mask | (ca < K ? 1u << ca : 0)))
                    return false;
                if (ca == K && cb == K) {
                    s.unequal[a] |= bit(b);
                    s.unequal[b] |= bit(a);
                }
            }
        s.open &= ~bit(x);
        s.forced &= ~bit(x);
        s.classes[c] |= bit(x);
        s.value[x] = c;
        s.used = std::max(s.used, c + 1);
        return true;
    }
    bool solve(State &s) {
        ++nodes;
        while (s.forced) {
            int x = first(s.forced);
            if (!assign(s, x, std::countr_zero(s.domain[x])))
                return false;
        }
        if (!s.open)
            return true;
        int best = -100000, x = -1;
        for (int j = 0; j < length; ++j) {
            int i = order[j];
            if (!(s.open & bit(i)))
                continue;
            int rank = -1000 * std::popcount(s.domain[i]) +
                       5 * std::popcount(s.unequal[i] & s.open) + degree[i];
            if (rank > best) {
                best = rank;
                x = i;
            }
        }
        // Unused colors are interchangeable. Try at most one fresh name.
        unsigned names = (1u << std::min(K, s.used + 1)) - 1;
        for (unsigned dom = s.domain[x] & names; dom; dom &= dom - 1) {
            State t = s;
            if (assign(t, x, std::countr_zero(dom)) && solve(t))
                return true;
        }
        return false;
    }
    void verify_unsat() {
        State s{};
        s.open = vertices;
        s.domain.fill((1u << K) - 1);
        s.value.fill(K);
        if (solve(s))
            throw std::logic_error("a five-color obstruction was colorable");
        std::cout << "No five-coloring of the " << std::popcount(vertices) << "-point obstruction ("
                  << nodes << " nodes).\n";
    }
};

// Every puncture contains a translate or reflected translate of one of these
// two five-color obstructions. Coordinates inside the program are zero-based.
void check_lower_bound() {
    const Mask solid = interval(36), sparse = interval(52) & ~bit(18) & ~bit(21) & ~bit(24);
    FiveColorSearch(36, solid).verify_unsat();
    FiveColorSearch(52, sparse).verify_unsat();
    Mask covered = 0;
    for (Mask shape : {solid, sparse}) {
        int span = std::bit_width(shape);
        for (int shift = 0; shift + span <= N; ++shift) {
            Mask copy = shape << shift, reversed = 0;
            for (Mask m = copy; m; m &= m - 1)
                reversed |= bit(N - 1 - first(m));
            covered |= interval(N) & ~copy;
            covered |= interval(N) & ~reversed;
        }
    }
    if (covered != interval(N))
        throw std::logic_error("a deletion lacks a five-color obstruction");
    std::cout << "Every one-point deletion of [54] requires exactly six colors.\n";
}
} // namespace
int main(int argc, char **argv) {
    if (argc != 2)
        return 2;
    check_words(argv[1]);
    check_lower_bound();
}
