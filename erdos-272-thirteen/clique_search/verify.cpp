// Exhaustive upper-bound verifier for Erdős problem #272 at n = 13 or 14.
// Compile: c++ -O3 -std=c++23 -march=native clique_search/verify.cpp -o /tmp/erdos272-verify
// Run:     /tmp/erdos272-verify
// Add -DERDOS272_N=14 for the fourteen-point case. Bit i represents element i + 1.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <tuple>
#include <vector>

namespace {

using Word = std::uint64_t;
#ifndef ERDOS272_N
#define ERDOS272_N 13
#endif
constexpr int N = ERDOS272_N;
static_assert(N == 13 || N == 14);
constexpr int limit = 1 << N;
constexpr int pair_dimension = 1 + N * (N - 1) / 2;
constexpr int target = pair_dimension + (N - 1) / 4 + 1;
constexpr int exceptional_needed = target - pair_dimension;
constexpr int exceptional_count = N == 13 ? 300 : 752;
constexpr std::uint64_t canonical_pairs = N == 13 ? 3224 : 12394;
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
Bits edges[limit], avoids[N], exceptional_candidates;
std::vector<int> labels;
int active_words = 0;
std::uint64_t pairs_checked = 0, nodes = 0;
std::vector<int> selected;

// Direct check of the starred bound via non-AP triple buckets.
// For a star centre x, every non-AP of size ≥ 4 contains a non-AP triple t ∋ x
// whose AP-hull is not contained in it, so each triple t forms an independent
// bucket with all such sets and at most one matched AP of size ≥ 4.
bool verify_star_bound() {
    int max_deficit = 0;
    for (int centre = 0; centre < N; ++centre) {
        int bit = 1 << centre;
        std::vector<int> triples, big_aps;
        for (int m = 1; m < limit; ++m) {
            if (!(m & bit)) continue;
            int sz = std::popcount((unsigned)m);
            if (sz == 3 && !ap[m]) triples.push_back(m);
            if (sz >= 4 && ap[m]) big_aps.push_back(m);
        }
        std::vector<int> hull(triples.size(), limit - 1);
        for (std::size_t i = 0; i < triples.size(); ++i)
            for (int p = 1; p < limit; ++p)
                if (ap[p] && (triples[i] & p) == triples[i]) hull[i] &= p;

        for (int a = 1; a < limit; ++a) {
            if (!(a & bit) || std::popcount((unsigned)a) < 4 || ap[a]) continue;
            bool covered = false;
            for (std::size_t i = 0; i < triples.size(); ++i)
                if ((a & triples[i]) == triples[i] && (a & hull[i]) != hull[i]) {
                    covered = true;
                    break;
                }
            if (!covered) return false;
        }

        std::vector<int> match(triples.size(), -1);
        auto augment = [&](auto &self, int u, std::vector<char> &seen) -> bool {
            int p = big_aps[u];
            for (std::size_t i = 0; i < triples.size(); ++i) {
                if ((p & triples[i]) != triples[i] || seen[i]) continue;
                seen[i] = 1;
                if (match[i] < 0 || self(self, match[i], seen)) {
                    match[i] = u;
                    return true;
                }
            }
            return false;
        };
        int matched = 0;
        for (int u = 0; u < (int)big_aps.size(); ++u) {
            std::vector<char> seen(triples.size(), 0);
            if (augment(augment, u, seen)) ++matched;
        }
        max_deficit = std::max(max_deficit, (int)big_aps.size() - matched);
    }
    return max_deficit == (N - 1) / 4;
}

// Check q(S) = 1 + C(|S|,2) - |S| - a3(S) - a4(S) - a6(S) on all nonempty
// subsets avoiding a seven-term AP: q(S) = 0 on APs and q(S) > 0 otherwise.
bool verify_score_bound() {
    std::vector<int> negative_aps;
    for (int p = 1; p < limit; ++p) {
        int len = std::popcount((unsigned)p);
        if (ap[p] && (len == 3 || len == 4 || len == 6)) negative_aps.push_back(p);
    }
    int short_count = 0;
    for (int mask = 1; mask < limit; ++mask) {
        if (exceptional[mask]) continue;
        ++short_count;
        int sz = std::popcount((unsigned)mask);
        int score = (sz - 1) * (sz - 2) / 2;
        for (int p : negative_aps)
            if ((mask & p) == p) --score;
        if ((ap[mask] && score != 0) || (!ap[mask] && score <= 0)) return false;
    }
    return short_count == limit - 1 - exceptional_count;
}

bool search(Bits candidates, int needed, int exceptional_needed, int common) {
    ++nodes;
    if (needed == 0) return exceptional_needed <= 0 && common == 0;

    int total = 0;
    for (int i = 0; i < active_words; ++i) total += std::popcount(candidates.bits[i]);
    if (total < needed) return false;

    // Necessary-pool checks: a completion needs exceptional_needed more exceptional
    // sets and must omit every currently common element at least once.
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
        if ((common >> m & 1) && !check_pool(avoids[m], 1)) return false;

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
                for (int j = i; j < active_words; ++j)
                    available.bits[j] &= ~edges[v].bits[j];
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
            for (int j = 0; j < active_words; ++j) {
                next.bits[j] = candidates.bits[j] & edges[v].bits[j];
                count += std::popcount(next.bits[j]);
            }
            if (count < needed - 1) continue;
            int mask = labels[v];
            selected.push_back(mask);
            if (search(next, needed - 1, exceptional_needed - exceptional[mask], common & mask))
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
    if (!ap[first & second]) return false;
    ++pairs_checked;
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
    for (Bits &pool : avoids) pool = {};
    exceptional_candidates = {};
    Bits candidates;
    for (int v = 0; v < size; ++v) {
        int mask = labels[v];
        edges[v] = {};
        for (int w = 0; w < size; ++w)
            if (w != v && ap[mask & labels[w]]) edges[v].add(w);
        for (int m = 0; m < N; ++m)
            if (!(mask >> m & 1)) avoids[m].add(v);
        if (exceptional[mask]) exceptional_candidates.add(v);
        candidates.add(v);
    }
    selected = {first, second};
    return search(candidates, target - 2, exceptional_needed - 2, first & second);
}

}  // namespace

int main() {
    for (int start = 0; start < N; ++start)
        for (int step = 1; step <= N; ++step) {
            int mask = 0;
            for (int i = start; i < N; i += step) {
                mask |= 1 << i;
                ap[mask] = true;
            }
        }
    for (int p = 1; p < limit; ++p)
        if (ap[p] && std::popcount((unsigned)p) == 7)
            for (int mask = 1; mask < limit; ++mask)
                if ((p & mask) == p) exceptional[mask] = true;

    if (!verify_star_bound()) {
        std::cerr << "Starred bound check failed.\n";
        return 2;
    }
    std::cout << "Starred upper bound at n = " << N << ": " << target - 1 << '\n';

    if (!verify_score_bound()) {
        std::cerr << "Score check failed.\n";
        return 2;
    }
    std::cout << "Score check passed on " << limit - 1 - exceptional_count
              << " nonempty masks avoiding seven-term APs.\n";

    for (int mask = 1; mask < limit; ++mask) {
        if (std::popcount((unsigned)mask) >= 2) masks.push_back(mask);
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
    for (int r = 0; r < (int)exceptional_masks.size(); ++r) {
        int first = exceptional_masks[r];
        if (first > reflect(first)) continue;
        bool palindromic = (first == reflect(first));
        for (int s = r + 1; s < (int)exceptional_masks.size(); ++s) {
            int second = exceptional_masks[s];
            if (palindromic && second > reflect(second)) continue;
            if (check_pair(r, s)) {
                std::cout << "Clique found (masks):";
                for (int mask : selected) std::cout << ' ' << mask;
                std::cout << '\n';
                return 1;
            }
        }
    }
    if (pairs_checked != canonical_pairs) {
        std::cerr << "Unexpected compatible pair count: " << pairs_checked << '\n';
        return 2;
    }
    std::cout << "Exceptional masks: " << exceptional_masks.size()
              << "\nCanonical compatible first pairs: " << pairs_checked
              << "\nSearch nodes: " << nodes
              << "\nNo " << target << "-clique with empty total intersection and "
              << exceptional_needed << " or more exceptional sets.\n";
}
