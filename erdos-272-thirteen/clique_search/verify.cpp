// Exhaustive upper-bound verifier for Erdős problem #272 at n = 13, 14, or 15.
// Compile: c++ -O3 -std=c++23 -march=native clique_search/verify.cpp -o /tmp/erdos272-verify
// Run:     /tmp/erdos272-verify
// Set ERDOS272_N at compile time to select the ground-set size. Bit i represents element i + 1.
#include <algorithm>
#include <array>
#include <bit>
#include <charconv>
#include <cstdint>
#include <iostream>
#include <string_view>
#include <tuple>
#include <vector>

namespace {

using Word = std::uint64_t;
#ifndef ERDOS272_N
#define ERDOS272_N 13
#endif
constexpr int N = ERDOS272_N;
static_assert(13 <= N && N <= 15);
constexpr int limit = 1 << N;
constexpr int pair_dimension = 1 + N * (N - 1) / 2;
constexpr int target = pair_dimension + (N - 1) / 4 + 1;
constexpr int exceptional_needed = target - pair_dimension;
constexpr int seven_term_supersets = std::array{300, 752, 1712}[N - 13];
constexpr int exceptional_count = std::array{300, 752, 1733}[N - 13];
constexpr int canonical_pairs = std::array{3224, 12394, 59836}[N - 13];
constexpr int words = limit / 64;

struct Bits {
    std::array<Word, words> bits{};
    void add(int x) { bits[x / 64] |= Word{1} << (x % 64); }
    void remove(int x) { bits[x / 64] &= ~(Word{1} << (x % 64)); }
};

int reflect(int mask) {
    int out = 0;
    for (int i = 0; i < N; ++i)
        if (mask >> i & 1) out |= 1 << (N - 1 - i);
    return out;
}

bool ap[limit], exceptional[limit];
std::vector<int> masks, exceptional_masks;
int degree[limit];
std::vector<Word> edges;
Bits avoids[N], exceptional_candidates;
std::vector<int> labels;
int active_words = 0;
std::uint64_t nodes = 0;
std::vector<int> selected;

// Each class is independent, so a family through one point uses at most one
// member per class. The order only affects how many classes first fit uses.
bool verify_star_bound() {
    std::array<std::vector<int>, 3> groups;
    for (int mask = 1; mask < limit; ++mask) {
        const int size = std::popcount(static_cast<unsigned>(mask));
        const int group = size <= 3 ? 0 : (ap[mask] ? 1 : 2);
        groups[group].push_back(mask);
    }
    for (int point = 0; point < N; ++point) {
        std::vector<std::vector<int>> classes;
        for (const auto &group : groups) {
            for (int mask : group) {
                if (!(mask & (1 << point))) continue;
                auto color = std::find_if(classes.begin(), classes.end(), [mask](const auto &members) {
                    return std::none_of(members.begin(), members.end(),
                        [mask](int other) { return ap[mask & other]; });
                });
                if (color == classes.end()) classes.push_back({mask});
                else color->push_back(mask);
            }
        }
        if (classes.size() >= target) return false;
    }
    return true;
}

// Check q(S) = 1 + C(|S|,2) - |S| - a3(S) - a4(S) - a6(S) on all nonempty
// subsets avoiding a seven-term AP: q(S) = 0 on APs and q(S) > 0 otherwise.
bool classify_masks_and_check_score() {
    std::vector<int> negative_aps, sevens;
    for (int p = 1; p < limit; ++p) {
        int len = std::popcount((unsigned)p);
        if (ap[p] && (len == 3 || len == 4 || len == 6)) negative_aps.push_back(p);
        if (ap[p] && len == 7) sevens.push_back(p);
    }
    int short_count = 0;
    for (int mask = 1; mask < limit; ++mask) {
        const int sz = std::popcount(static_cast<unsigned>(mask));
        const bool contains_seven = std::any_of(sevens.begin(), sevens.end(),
            [mask](int p) { return (mask & p) == p; });
        exceptional[mask] = contains_seven || (N == 15 && ap[mask] && sz == 5);
        if (contains_seven) continue;
        ++short_count;
        int score = (sz - 1) * (sz - 2) / 2;
        for (int p : negative_aps)
            if ((mask & p) == p) --score;
        if ((ap[mask] && score != 0) || (!ap[mask] && score <= 0)) return false;
    }
    return short_count == limit - 1 - seven_term_supersets;
}

bool search(Bits candidates, int needed, int exceptional_needed, int to_omit) {
    ++nodes;
    if (needed == 0) return exceptional_needed <= 0 && to_omit == 0;

    int total = 0;
    for (int i = 0; i < active_words; ++i) total += std::popcount(candidates.bits[i]);
    if (total < needed) return false;

    // Necessary-pool checks: a completion needs exceptional_needed more exceptional
    // sets and must omit each point in to_omit at least once.
    Bits best_pool;
    int best_pool_size = total + 1;
    auto check_pool = [&](const Bits &pool, int minimum) {
        int count = 0;
        Bits inter;
        for (int j = 0; j < active_words; ++j) {
            inter.bits[j] = candidates.bits[j] & pool.bits[j];
            count += std::popcount(inter.bits[j]);
        }
        if (count < minimum) return false;
        if (count < best_pool_size) {
            best_pool = inter;
            best_pool_size = count;
        }
        return true;
    };
    if (exceptional_needed > 0 && !check_pool(exceptional_candidates, exceptional_needed))
        return false;
    for (int m = 0; m < N; ++m)
        if ((to_omit >> m & 1) && !check_pool(avoids[m], 1)) return false;

    // Greedily peel needed - 1 independent sets; any clique must hit the remainder.
    Bits branches = candidates;
    int uncolored = total;
    for (int k = 1; k < needed; ++k) {
        Bits available = branches;
        for (int i = 0; i < active_words; ++i) {
            while (available.bits[i]) {
                int v = 64 * i + std::countr_zero(available.bits[i]);
                branches.remove(v);
                available.remove(v);
                --uncolored;
                const Word *neighbors = edges.data() + v * active_words;
                for (int j = i; j < active_words; ++j)
                    available.bits[j] &= ~neighbors[j];
            }
        }
        if (uncolored < needed - k) return false;
    }
    if (best_pool_size < uncolored) branches = best_pool;

    for (int i = active_words - 1; i >= 0; --i) {
        while (branches.bits[i]) {
            int v = 64 * i + 63 - std::countl_zero(branches.bits[i]);
            branches.remove(v);
            candidates.remove(v);
            Bits next;
            int count = 0;
            const Word *neighbors = edges.data() + v * active_words;
            for (int j = 0; j < active_words; ++j) {
                next.bits[j] = candidates.bits[j] & neighbors[j];
                count += std::popcount(next.bits[j]);
            }
            if (count < needed - 1) continue;
            int mask = labels[v];
            selected.push_back(mask);
            if (search(next, needed - 1, exceptional_needed - exceptional[mask], to_omit & mask))
                return true;
            selected.pop_back();
        }
    }
    return false;
}

// A smallest-last order makes the greedy independent-set covers tighter.
// Every candidate is kept. This only changes the order in which it is visited.
void order_candidates() {
    const int size = static_cast<int>(labels.size());
    std::vector<int> degrees(size);
    for (int i = 0; i < size; ++i)
        for (int b : labels)
            degrees[i] += (labels[i] != b && ap[labels[i] & b]);

    std::vector<int> ordered(size);
    for (int pos = size - 1; pos >= 0; --pos) {
        int best = -1;
        for (int i = 0; i < size; ++i)
            if (degrees[i] >= 0 && (best < 0 || degrees[i] < degrees[best])) best = i;
        const int mask = labels[best];
        ordered[pos] = mask;
        degrees[best] = -1;
        for (int i = 0; i < size; ++i)
            if (degrees[i] >= 0 && ap[mask & labels[i]]) --degrees[i];
    }
    labels.swap(ordered);
}

bool check_pair(int r, int s) {
    int first = exceptional_masks[r], second = exceptional_masks[s];
    labels.clear();
    for (int mask : masks)
        if (!exceptional[mask] && ap[first & mask] && ap[second & mask])
            labels.push_back(mask);
    for (int t = s + 1; t < (int)exceptional_masks.size(); ++t) {
        int mask = exceptional_masks[t];
        if (ap[first & mask] && ap[second & mask]) labels.push_back(mask);
    }
    int size = (int)labels.size();
    if (size < target - 2) return false;

    order_candidates();

    active_words = (size + 63) / 64;
    edges.assign(size * active_words, 0);
    for (Bits &pool : avoids) pool = {};
    exceptional_candidates = {};
    Bits candidates;
    for (int v = 0; v < size; ++v) {
        int mask = labels[v];
        Word *neighbors = edges.data() + v * active_words;
        for (int w = 0; w < size; ++w)
            if (w != v && ap[mask & labels[w]]) neighbors[w / 64] |= Word{1} << (w % 64);
        for (int m = 0; m < N; ++m)
            if (!(mask >> m & 1)) avoids[m].add(v);
        if (exceptional[mask]) exceptional_candidates.add(v);
        candidates.add(v);
    }
    selected = {first, second};
    return search(candidates, target - 2, exceptional_needed - 2, first & second);
}

bool parse_index(std::string_view input, int &index) {
    const char *end = input.data() + input.size();
    const auto [ptr, error] = std::from_chars(input.data(), end, index);
    return error == std::errc{} && ptr == end;
}

}  // namespace

int main(int argc, char **argv) {
    int begin = 0, end = canonical_pairs;
    if (argc != 1 && (argc != 3 || !parse_index(argv[1], begin) || !parse_index(argv[2], end)
                      || begin < 0 || begin >= end || end > canonical_pairs)) {
        std::cerr << "Usage: verifier [begin end], zero-based, half-open, within [0, "
                  << canonical_pairs << ").\n";
        return 2;
    }

    for (int start = 0; start < N; ++start)
        for (int step = 1; step <= N; ++step) {
            int mask = 0;
            for (int i = start; i < N; i += step) {
                mask |= 1 << i;
                ap[mask] = true;
            }
        }
    if (!verify_star_bound()) {
        std::cerr << "Starred bound check failed.\n";
        return 2;
    }
    std::cout << "Starred upper bound at n = " << N << ": " << target - 1 << '\n';

    if (!classify_masks_and_check_score()) {
        std::cerr << "Score check failed.\n";
        return 2;
    }
    std::cout << "Score check passed on " << limit - 1 - seven_term_supersets
              << " nonempty masks avoiding seven-term APs.\n";

    for (int mask = 1; mask < limit; ++mask) {
        if (N == 15 || !std::has_single_bit(static_cast<unsigned>(mask)))
            masks.push_back(mask);
        if (exceptional[mask]) exceptional_masks.push_back(mask);
    }
    if (exceptional_masks.size() != exceptional_count) {
        std::cerr << "Unexpected exceptional mask count: " << exceptional_masks.size() << '\n';
        return 2;
    }
    for (int a : exceptional_masks)
        for (int b : masks) degree[a] += (a != b && ap[a & b]);

    // Group each set with its reflection i -> N + 1 - i, keeping min(a, reflect(a)) first.
    // Every prefix before a canonical representative is reflection-invariant, so each
    // valid clique (or its reflection) has canonical first choice (and second if palindromic).
    std::sort(exceptional_masks.begin(), exceptional_masks.end(), [](int a, int b) {
        int ca = std::min(a, reflect(a)), cb = std::min(b, reflect(b));
        return std::tuple(degree[a], ca, a) < std::tuple(degree[b], cb, b);
    });
    int pair_index = 0, pairs_checked = 0;
    for (int r = 0; r < (int)exceptional_masks.size(); ++r) {
        int first = exceptional_masks[r];
        if (first > reflect(first)) continue;
        bool palindromic = (first == reflect(first));
        for (int s = r + 1; s < (int)exceptional_masks.size(); ++s) {
            int second = exceptional_masks[s];
            if (palindromic && second > reflect(second)) continue;
            if (!ap[first & second]) continue;
            const int index = pair_index++;
            if (index < begin || index >= end) continue;
            ++pairs_checked;
            if (check_pair(r, s)) {
                std::cout << "Clique found (masks):";
                for (int mask : selected) std::cout << ' ' << mask;
                std::cout << '\n';
                return 1;
            }
        }
    }
    if (pair_index != canonical_pairs || pairs_checked != end - begin) {
        std::cerr << "Unexpected pair totals: " << pair_index << " enumerated, "
                  << pairs_checked << " checked.\n";
        return 2;
    }
    std::cout << "Exceptional masks: " << exceptional_masks.size()
              << "\nCanonical compatible first pairs: " << pair_index
              << "\nPairs checked in [" << begin << ", " << end << "): " << pairs_checked
              << "\nSearch nodes: " << nodes << '\n';
    if (pairs_checked == canonical_pairs) {
        std::cout << "No " << target << "-clique with empty total intersection and "
                  << exceptional_needed << " or more exceptional sets.\n";
    } else {
        std::cout << "No completion in this range.\n";
    }
    return 0;
}
