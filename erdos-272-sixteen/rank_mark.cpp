// Verify a rank certificate for the 16-point arithmetic-progression intersection problem.
// Build with c++ -std=c++20 -O2 rank_mark.cpp -o rank_mark and run ./rank_mark rank.weights.
// A line in rank.weights is "mask weight". Zero marks a mask; omitted weights default to 128.
#include <algorithm>
#include <array>
#include <bit>
#include <fstream>
#include <iostream>
#include <vector>

namespace {
constexpr int points = 16;
constexpr int capacity = 1 << points;
constexpr int default_weight = 128;

std::array<bool, capacity> ap{}, exceptional{}, explicitly_weighted{};
std::array<int, capacity> score{}, weight{};
std::vector<int> long_holders;
std::vector<std::vector<int>> long_neighbors(capacity);

int reflected(int mask) {
    int image = 0;
    for (int i = 0; i < points; ++i)
        image = (image << 1) | ((mask >> i) & 1);
    return image;
}

bool initialize() {
    std::vector<int> counted;
    for (int start = 0; start < points; ++start) {
        for (int step = 1; step <= points; ++step) {
            int mask = 0;
            for (int x = start; x < points; x += step) {
                mask |= 1 << x;
                ap[mask] = true;
            }
        }
    }
    for (int mask = 1; mask < capacity; ++mask) {
        if (!ap[mask]) continue;
        const int size = std::popcount(static_cast<unsigned>(mask));
        if (size == 3 || size == 4 || size == 6) counted.push_back(mask);
        if (size == 7) {
            for (int superset = mask; superset < capacity; superset = (superset + 1) | mask)
                exceptional[superset] = true;
        }
    }
    for (int mask = 1; mask < capacity; ++mask) {
        const int size = std::popcount(static_cast<unsigned>(mask));
        score[mask] = (size - 1) * (size - 2) / 2;
        for (int term : counted) score[mask] -= (mask & term) == term;
        if (exceptional[mask]) {
            long_holders.push_back(mask);
        } else if (ap[mask] ? score[mask] != 0 : score[mask] <= 0) {
            return false;
        }
        if (ap[mask] && score[mask] > 0) return false;
    }
    for (int a : long_holders) {
        for (int b : long_holders) {
            const int trace = a & b;
            if (a != b && ap[trace] && score[trace] < 0) long_neighbors[a].push_back(b);
        }
    }
    return long_holders.size() == 3839;
}

bool read_certificate(const char* path) {
    std::ifstream input(path);
    if (!input) return false;
    weight.fill(default_weight);
    int mask, value;
    while (input >> mask) {
        if (!(input >> value) || mask <= 0 || mask >= capacity || !exceptional[mask] ||
            explicitly_weighted[mask] || value < 0 || value > 10000) return false;
        explicitly_weighted[mask] = true;
        weight[mask] = value;
    }
    return input.eof();
}

// For a fixed A this greedily partitions its relevant neighbors B into classes of
// mutually incompatible sets. A candidate family can use at most one from each
// class, so the sum of the class maxima bounds the off-diagonal contributions.
int off_diagonal_bound(int a) {
    std::vector<int> neighbors;
    for (int b : long_neighbors[a])
        if (weight[b] > 0) neighbors.push_back(b);

    const auto cost = [&](int b) { return -score[a & b] * weight[b]; };
    std::sort(neighbors.begin(), neighbors.end(), [&](int b, int c) {
        if (cost(b) != cost(c)) return cost(b) > cost(c);
        if (long_neighbors[b].size() != long_neighbors[c].size())
            return long_neighbors[b].size() > long_neighbors[c].size();
        return b < c;
    });

    int total = 0;
    std::vector<std::vector<int>> classes;
    for (int b : neighbors) {
        auto compatible_with_b = [&](int c) { return ap[b & c]; };
        auto cls = std::find_if(classes.begin(), classes.end(), [&](const auto& group) {
            return std::none_of(group.begin(), group.end(), compatible_with_b);
        });
        if (cls == classes.end()) {
            classes.push_back({b});
            total += cost(b); // The first member of a class maximizes its cost.
        } else {
            cls->push_back(b);
        }
    }
    return total;
}
}

int main(int argc, char** argv) {
    if (argc != 2 || !initialize() || !read_certificate(argv[1])) {
        std::cerr << "Expected a valid rank weights file.\n";
        return 1;
    }
    std::vector<int> marked;
    for (int a : long_holders) {
        if ((weight[a] == 0) != (weight[reflected(a)] == 0)) {
            std::cerr << "The marked set is not closed under reflection.\n";
            return 1;
        }
        if (weight[a] == 0) {
            marked.push_back(a);
        } else if (score[a] * weight[a] <= off_diagonal_bound(a)) {
            std::cerr << "Diagonal dominance failed at mask " << a << ".\n";
            return 1;
        }
    }
    int pairs = 0;
    for (int a : marked)
        for (int b : marked)
            pairs += a < b && ap[a & b];
    std::cout << "remaining " << marked.size() << " pairs " << pairs << '\n';
    for (int a : marked) std::cout << a << ' ';
    std::cout << '\n';
}
