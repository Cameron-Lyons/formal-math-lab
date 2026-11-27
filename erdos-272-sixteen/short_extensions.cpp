// Check the ordinary completions of the marked families from verify_short.py --instances.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <utility>
#include <vector>

namespace {
using Word = std::uint64_t;
using Bitmap = std::vector<Word>;
constexpr int points = 16;
constexpr int masks = 1 << points;
std::array<bool, masks> short_ap, marked;

bool compatible(int a, int b) { return a != b && short_ap[a & b]; }

void prepare_progressions() {
    for (int first = 0; first < points; ++first)
        for (int step = 1; step < points; ++step) {
            int mask = 0, length = 0;
            for (int p = first; p < points && length < 6; p += step, ++length) {
                mask |= 1 << p;
                short_ap[mask] = true;
            }
        }
}

struct Graph {
    std::vector<int> vertex;
    int words;
    Bitmap edges;
    std::array<Bitmap, points> omits;
    std::vector<Bitmap> contains_pair;
    using Pairs = std::array<Word, 2>;
    std::vector<Pairs> pair_mask;

    void prepare_pairs() {
        contains_pair.assign(120, Bitmap(words));
        pair_mask.resize(vertex.size());
        for (int i = 0; i < static_cast<int>(vertex.size()); ++i) {
            int pair = 0;
            for (int x = 0; x < points; ++x)
                for (int y = 0; y < x; ++y, ++pair) {
                    int mask = (1 << x) | (1 << y);
                    if ((vertex[i] & mask) != mask) continue;
                    contains_pair[pair][i / 64] |= Word{1} << (i % 64);
                    pair_mask[i][pair / 64] |= Word{1} << (pair % 64);
                }
        }
    }

    explicit Graph(std::vector<int> vertices)
        : vertex(std::move(vertices)), words((vertex.size() + 63) / 64),
          edges(words * vertex.size()) {
        for (auto &p : omits) p.resize(words);
        for (int i = 0; i < static_cast<int>(vertex.size()); ++i) {
            for (int j = 0; j < i; ++j)
                if (compatible(vertex[i], vertex[j])) {
                    edges[i * words + j / 64] |= Word{1} << (j % 64);
                    edges[j * words + i / 64] |= Word{1} << (i % 64);
                }
            for (int x = 0; x < points; ++x)
                if (!(vertex[i] & (1 << x))) omits[x][i / 64] |= Word{1} << (i % 64);
        }
    }

    // Reverse smallest-last vertex order for the greedy coloring.
    std::vector<int> ordered_vertices() const {
        int size = vertex.size();
        std::vector<int> result(size), degree(size);
        Bitmap active(words, ~Word{0});
        for (int i = 0; i < size; ++i)
            for (int w = 0; w < words; ++w) degree[i] += std::popcount(edges[i * words + w]);
        for (int pos = size - 1; pos >= 0; --pos) {
            auto smallest = std::min_element(degree.begin(), degree.end());
            int i = smallest - degree.begin();
            result[pos] = vertex[i];
            *smallest = size + 1;
            active[i / 64] &= ~(Word{1} << (i % 64));
            for (int w = 0; w < words; ++w)
                for (Word bits = edges[i * words + w] & active[w]; bits; bits &= bits - 1)
                    --degree[w * 64 + std::countr_zero(bits)];
        }
        return result;
    }

    // Peel independent classes. A clique of the requested size must contain
    // a vertex of the remainder. A negative return proves that no such
    // clique exists.
    int required_remainder(Bitmap &remaining, int count, int need) const {
        for (int color = 1; color < need; ++color) {
            auto available = remaining;
            for (int w = 0; w < words; ++w)
                while (available[w]) {
                    int bit = std::countr_zero(available[w]);
                    int i = w * 64 + bit;
                    remaining[w] ^= Word{1} << bit;
                    available[w] &= available[w] - 1;
                    --count;
                    for (int j = w; j < words; ++j) available[j] &= ~edges[i * words + j];
                }
            if (count < need - color) return -1;
        }
        return count;
    }

    bool can_complete(Bitmap candidates, int count, int need,
                      std::array<int, points> missing, Pairs uncovered_pairs,
                      std::vector<int>& witness) const {
        if (need == 0)
            return uncovered_pairs[0] == 0 && uncovered_pairs[1] == 0 &&
                *std::max_element(missing.begin(), missing.end()) <= 0;
        auto branches = candidates;
        int branch_count = required_remainder(branches, count, need);
        if (branch_count < 0) return false;

        for (int x = 0; x < points; ++x) {
            if (missing[x] <= 0) continue;
            Bitmap pool(words);
            int size = 0;
            for (int w = 0; w < words; ++w) {
                pool[w] = candidates[w] & omits[x][w];
                size += std::popcount(pool[w]);
            }
            if (size < missing[x]) return false;
            if (size < 5 * missing[x]) {
                size = required_remainder(pool, size, missing[x]);
                if (size < 0) return false;
            } else if (size - missing[x] + 1 < branch_count) {
                // A completion must hit this pool even after we exempt
                // any missing[x]-1 of its vertices.
                int exempt = missing[x] - 1;
                for (Word &word : pool)
                    while (word && exempt) {
                        word &= word - 1;
                        --exempt;
                        --size;
                    }
            }
            if (size < branch_count) {
                branch_count = size;
                branches = std::move(pool);
            }
        }
        // When exactly 121 ordinary rows are required, their independence
        // forces each pair-coordinate to occur.
        int best_pair = -1;
        for (int block = 0; block < 2; ++block) {
            for (Word bits = uncovered_pairs[block]; bits; bits &= bits - 1) {
                int p = 64 * block + std::countr_zero(bits);
                int amount = 0;
                for (int w = 0; w < words && amount < branch_count; ++w)
                    amount += std::popcount(candidates[w] & contains_pair[p][w]);
                if (amount == 0) return false;
                if (amount < branch_count) {
                    branch_count = amount;
                    best_pair = p;
                }
            }
        }
        if (best_pair >= 0)
            for (int w = 0; w < words; ++w)
                branches[w] = candidates[w] & contains_pair[best_pair][w];
        for (int w = words - 1; w >= 0; --w)
            while (branches[w]) {
                int bit = 63 - std::countl_zero(branches[w]);
                int i = w * 64 + bit;
                branches[w] ^= Word{1} << bit;
                candidates[w] ^= Word{1} << bit;
                Bitmap next(words);
                int size = 0;
                for (int j = 0; j < words; ++j) {
                    next[j] = candidates[j] & edges[i * words + j];
                    size += std::popcount(next[j]);
                }
                if (size < need - 1) continue;
                auto still_missing = missing;
                for (int x = 0; x < points; ++x)
                    if (!(vertex[i] & (1 << x))) --still_missing[x];
                auto still_uncovered = uncovered_pairs;
                if (still_uncovered[0] || still_uncovered[1])
                    for (int b = 0; b < 2; ++b) still_uncovered[b] &= ~pair_mask[i][b];
                if (can_complete(std::move(next), size, need - 1, still_missing,
                                 still_uncovered, witness)) {
                    witness.push_back(vertex[i]);
                    return true;
                }
            }
        return false;
    }
};

// Every possible ordinary row in the clique has at least two elements:
// a singleton would force its point into all members of the family.
bool check_case(const std::vector<int> &seeds, int target, std::vector<int>& witness) {
    int need = target - static_cast<int>(seeds.size());
    std::vector<int> candidates;
    for (int a = 1; a < masks; ++a)
        if (!marked[a] && std::popcount(static_cast<unsigned>(a)) >= 2 &&
            std::all_of(seeds.begin(), seeds.end(), [a](int b) { return compatible(a, b); }))
            candidates.push_back(a);
    if (static_cast<int>(candidates.size()) < need) return true;
    Graph graph(Graph(std::move(candidates)).ordered_vertices());
    Graph::Pairs uncovered{0, 0};
    if (need == 121) {
        graph.prepare_pairs();
        uncovered = {~Word{0}, (Word{1} << 56) - 1};
    }
    int count = graph.vertex.size();
    Bitmap all(graph.words, ~Word{0});
    if (count % 64) all.back() = (Word{1} << (count % 64)) - 1;
    std::array<int, points> missing;
    for (int x = 0; x < points; ++x) {
        missing[x] = target - 111;
        for (int seed : seeds)
            if (!(seed & (1 << x))) --missing[x];
    }
    return !graph.can_complete(std::move(all), count, need, missing, uncovered, witness);
}
}  // namespace

int main() {
    prepare_progressions();
    int target, mark_count;
    if (!(std::cin >> target >> mark_count) || target < 125 || target > 130 || mark_count != 101)
        return 1;
    for (int i = 0; i < mark_count; ++i) {
        int a;
        if (!(std::cin >> a) || a <= 0 || a >= masks || marked[a]) return 1;
        marked[a] = true;
    }
    int cases = 0, size;
    while (std::cin >> size && size != 0) {
        if (size < target - 121 || size > 9) return 1;
        std::vector<int> seeds(size);
        for (int &a : seeds)
            if (!(std::cin >> a) || a <= 0 || a >= masks || !marked[a]) return 1;
        std::vector<int> witness = seeds;
        if (!check_case(seeds, target, witness)) {
            std::cerr << target << "-member family at masks";
            for (int a : witness) std::cerr << ' ' << a;
            std::cerr << '\n';
            return 2;
        }
        ++cases;
    }
    int expected;
    if (!std::cin || !(std::cin >> expected) || cases != expected || cases == 0) return 1;
    std::cout << "Excluded " << target << " members in " << cases << " marked cases\n";
}
