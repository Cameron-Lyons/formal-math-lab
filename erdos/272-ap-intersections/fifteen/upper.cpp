// Exact clique search for arithmetic-progression intersections on [15].
// A command-line range [begin, end) selects roots by their zero-based canonical index.
#include <algorithm>
#include <array>
#include <bit>
#include <charconv>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <string_view>
#include <vector>

namespace {
using Word = std::uint64_t;
using Bits = std::vector<Word>;
constexpr int points = 15, limit = 1 << points, target = 110;
constexpr int root_count = (limit + (1 << ((points + 1) / 2))) / 2 - 1;
std::array<bool, limit> ap{};
std::vector<int> triples;
std::array<std::vector<int>, limit> triple_indices;

int reflect(int mask) {
    int result = 0;
    for (int x = 0; x < points; ++x) result = 2 * result + ((mask >> x) & 1);
    return result;
}

// The two vertex orders below affect only the size of the search tree.
std::vector<int> removal_order(const std::vector<int>& masks) {
    const int size = static_cast<int>(masks.size());
    std::vector<int> degrees(size), ordered;
    ordered.reserve(size);
    for (int i = 0; i < size; ++i)
        for (int b : masks) degrees[i] += masks[i] != b && ap[masks[i] & b];
    for (int k = 0; k < size; ++k) {
        int best = -1;
        for (int i = 0; i < size; ++i)
            if (degrees[i] >= 0 && (best < 0 || degrees[i] < degrees[best])) best = i;
        int a = masks[best];
        ordered.push_back(a);
        degrees[best] = -1;
        for (int i = 0; i < size; ++i)
            if (degrees[i] >= 0 && ap[a & masks[i]]) --degrees[i];
    }
    return ordered;
}

void prepare_progressions() {
    for (int a = 0; a < points; ++a)
        for (int d = 1; d <= points; ++d) {
            int mask = 0;
            for (int i = a; i < points; i += d) ap[mask |= 1 << i] = true;
        }
    for (int mask = 1; mask < limit; ++mask)
        if (std::popcount(static_cast<unsigned>(mask)) == 3 && !ap[mask]) triples.push_back(mask);
    for (int mask = 1; mask < limit; ++mask)
        for (int t = 0; t < static_cast<int>(triples.size()); ++t)
            if ((mask & triples[t]) == triples[t]) triple_indices[mask].push_back(t);
}

using Quotas = std::array<int, points>;

// Through a point, a clique can take at most one vertex per independent class.
Quotas omission_quotas() {
    std::array<std::vector<int>, 3> groups;
    for (int mask = 1; mask < limit; ++mask) {
        int size = std::popcount(static_cast<unsigned>(mask));
        groups[size <= 3 ? 0 : (ap[mask] ? 1 : 2)].push_back(mask);
    }
    Quotas omit{};
    for (int x = 0; x < points; ++x) {
        std::vector<std::vector<int>> classes;
        for (const auto& group : groups) {
            for (int mask : group) {
                if (!(mask & (1 << x))) continue;
                auto fits = [mask](const auto& members) {
                    return std::none_of(members.begin(), members.end(), [mask](int b) { return ap[mask & b]; });
                };
                auto color = std::find_if(classes.begin(), classes.end(), fits);
                if (color == classes.end()) classes.push_back({mask});
                else color->push_back(mask);
            }
        }
        omit[x] = target - static_cast<int>(classes.size());
    }
    return omit;
}

Quotas including(Quotas omit, int mask) {
    for (int x = 0; x < points; ++x) omit[x] -= !(mask & (1 << x));
    return omit;
}

struct Graph {
    const std::vector<int>& labels;
    int words;
    std::vector<Bits> neighbors, containing, omitting;
    std::uint64_t nodes = 0;
    std::vector<int> witness;

    explicit Graph(const std::vector<int>& masks)
        : labels(masks), words((masks.size() + 63) / 64), neighbors(masks.size(), Bits(words)),
          containing(triples.size(), Bits(words)), omitting(points, Bits(words)) {
        for (int i = 0; i < static_cast<int>(labels.size()); ++i) {
            Word bit = Word{1} << (i % 64);
            for (int t : triple_indices[labels[i]]) containing[t][i / 64] |= bit;
            for (int x = 0; x < points; ++x)
                if (!(labels[i] & (1 << x))) omitting[x][i / 64] |= bit;
            for (int j = 0; j < static_cast<int>(labels.size()); ++j)
                if (i != j && ap[labels[i] & labels[j]]) neighbors[i][j / 64] |= Word{1} << (j % 64);
        }
    }

    int common_size(const Bits& a, const Bits& b) const {
        int count = 0;
        for (int w = 0; w < words; ++w) count += std::popcount(a[w] & b[w]);
        return count;
    }

    // Remove up to need-1 independent classes. A clique of size need must use a leftover vertex.
    int peel(Bits& leftover, int count, int need) const {
        std::vector<int> frequency;
        if (target - need <= 3) {
            for (const auto& pool : containing) frequency.push_back(common_size(leftover, pool));
        }
        for (int color = 1; color < need; ++color) {
            Bits available = leftover;
            auto take = [&](int word, int bit, int first_word) {
                int v = 64 * word + bit;
                Word chosen = Word{1} << bit;
                leftover[word] &= ~chosen;
                available[word] &= ~chosen;
                --count;
                for (int w = first_word; w < words; ++w) available[w] &= ~neighbors[v][w];
                if (!frequency.empty()) {
                    for (int t : triple_indices[labels[v]]) --frequency[t];
                }
            };
            // Prefer vertices containing a frequent triple, then finish the same color in vertex order.
            if (!frequency.empty()) {
                auto best = std::max_element(frequency.begin(), frequency.end());
                if (color > 50 || *best < 4) frequency.clear();
                else {
                    const auto& preferred = containing[best - frequency.begin()];
                    for (int w = 0; w < words; ++w)
                        while (Word bits = available[w] & preferred[w]) take(w, std::countr_zero(bits), 0);
                }
            }
            for (int w = 0; w < words; ++w)
                while (available[w]) take(w, std::countr_zero(available[w]), w);
            if (count < need - color) return 0;
        }
        return count;
    }

    bool search(Bits candidates, int count, int need, Quotas omit) {
        ++nodes;
        if (need == 1) {
            for (int w = 0; w < words; ++w) {
                if (!candidates[w]) continue;
                witness.push_back(labels[64 * w + std::countr_zero(candidates[w])]);
                return true;
            }
            return false;
        }
        int point = -1, smallest = count + 1;
        for (int x = 0; x < points; ++x) {
            if (omit[x] <= 0) continue;
            int size = common_size(candidates, omitting[x]);
            if (size < omit[x]) return false;
            if (size < smallest) {
                smallest = size;
                point = x;
            }
        }
        Bits branches = candidates;
        int left = peel(branches, count, need);
        if (left == 0) return false;
        if (smallest < left)
            for (int w = 0; w < words; ++w) branches[w] = candidates[w] & omitting[point][w];
        for (int w = words - 1; w >= 0; --w) {
            while (branches[w]) {
                int bit = 63 - std::countl_zero(branches[w]);
                int v = 64 * w + bit;
                branches[w] &= ~(Word{1} << bit);
                candidates[w] &= ~(Word{1} << bit);
                Bits next(words);
                int size = 0;
                for (int j = 0; j < words; ++j) {
                    next[j] = candidates[j] & neighbors[v][j];
                    size += std::popcount(next[j]);
                }
                if (size >= need - 1 && search(next, size, need - 1, including(omit, labels[v]))) {
                    witness.push_back(labels[v]);
                    return true;
                }
            }
        }
        return false;
    }
};

bool parse(std::string_view arg, int& value) {
    const char* end = arg.data() + arg.size();
    auto [ptr, error] = std::from_chars(arg.data(), end, value);
    return ptr == end && error == std::errc{};
}
}  // namespace

int main(int argc, char** argv) {
    int begin = 0, end = root_count;
    if (argc != 1 && (argc != 3 || !parse(argv[1], begin) || !parse(argv[2], end)
                      || begin < 0 || begin >= end || end > root_count)) {
        std::cerr << "Usage: verifier [begin end] for a nonempty zero-based range within [0, " << root_count << ").\n";
        return 2;
    }
    prepare_progressions();
    auto omit = omission_quotas();
    std::vector<int> masks(limit - 1);
    std::iota(masks.begin(), masks.end(), 1);
    auto order = removal_order(masks);
    std::array<int, limit> position{};
    for (int i = 0; i < limit - 1; ++i) position[order[i]] = i;
    std::vector<int> roots;
    for (int i = 0; i < limit - 1; ++i)
        if (position[reflect(order[i])] >= i) roots.push_back(i);
    if (roots.size() != root_count) return 2;
    std::uint64_t nodes = 0;
    int checked = 0;
    std::vector<int> found;
#ifdef _OPENMP
#pragma omp parallel for schedule(dynamic) reduction(+:nodes,checked)
#endif
    for (int index = begin; index < end; ++index) {
        int i = roots[index], a = order[i];
        ++checked;
        std::vector<int> candidates;
        for (int j = limit - 2; j > i; --j) {
            int b = order[j];
            if (position[reflect(b)] >= i && ap[a & b]) candidates.push_back(b);
        }
        int size = static_cast<int>(candidates.size());
        if (size < target - 1) continue;
        auto local = removal_order(candidates);
        std::reverse(local.begin(), local.end());
        Graph graph(local);
        Bits all(graph.words, ~Word{0});
        if (size % 64) all.back() = (Word{1} << (size % 64)) - 1;
        if (graph.search(all, size, target - 1, including(omit, a))) {
#ifdef _OPENMP
#pragma omp critical
#endif
            {
                if (found.empty()) {
                    found = graph.witness;
                    found.push_back(a);
                }
            }
        }
        nodes += graph.nodes;
    }
    if (!found.empty()) {
        std::cout << "Clique found (masks):";
        for (int mask : found) std::cout << ' ' << mask;
        std::cout << '\n';
        return 1;
    }
    if (checked != end - begin) return 2;
    std::cout << "Checked " << checked << " roots in [" << begin << ", " << end << ") of " << root_count
              << ". Search nodes: " << nodes << ". No " << target << "-clique in this range.\n";
    return 0;
}
