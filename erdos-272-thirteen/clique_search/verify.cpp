// Run with --simple for the one-page proof (315 exceptional masks).
// The default uses the 300-mask reduction verified by short_bound.py.
// A mask uses bit zero for element 1. Every reported count is an integer.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <string_view>
#include <utility>
#include <vector>

using Word = std::uint64_t;
constexpr int N = 13, limit = 1 << N, target = 83;
constexpr int words = limit / 64;
struct Bits {
    std::array<Word, words> bits{};
    void add(int x) { bits[x / 64] |= Word{1} << (x % 64); }
    void remove(int x) { bits[x / 64] &= ~(Word{1} << (x % 64)); }
};
bool ap[limit], exceptional[limit];
std::vector<int> masks, exceptional_masks;
int degree[limit];
Bits edges[limit], avoids[N], exceptional_candidates;
std::vector<int> labels;
int active_words;
std::uint64_t pairs_checked, nodes;
std::vector<int> selected;

bool search(Bits candidates, int needed, int exceptional_needed, int common) {
    ++nodes;
    if (needed == 0)
        return exceptional_needed <= 0 && common == 0;
    // Color the candidates greedily with needed-1 independent classes.
    // Each possible completion must contain an uncolored vertex.
    Bits branches = candidates;
    int uncolored = 0;
    for (int i = 0; i < active_words; ++i)
        uncolored += std::popcount(branches.bits[i]);
    if (uncolored < needed)
        return false;
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
        if (uncolored < needed - k)
            return false;
    }
    // Two further necessary conditions give alternative lists on which to branch.
    // A completion needs at least four exceptional members and must omit every currently
    // common element at least once. Pick the shortest applicable list.
    auto use_if_shorter = [&](const Bits &pool, int minimum) {
        int count = 0;
        Bits intersection;
        for (int j = 0; j < active_words; ++j) {
            intersection.bits[j] = candidates.bits[j] & pool.bits[j];
            count += std::popcount(intersection.bits[j]);
        }
        if (count < minimum)
            return false;
        if (count < uncolored) {
            branches = intersection;
            uncolored = count;
        }
        return true;
    };
    if (exceptional_needed > 0 && !use_if_shorter(exceptional_candidates, exceptional_needed))
        return false;
    for (int m = 0; m < N; ++m)
        if ((common >> m & 1) && !use_if_shorter(avoids[m], 1))
            return false;

    for (int i = active_words - 1; i >= 0; --i) {
        while (branches.bits[i]) {
            int v = 64 * i + 63 - std::countl_zero(branches.bits[i]);
            branches.remove(v);
            candidates.remove(v); // exclude previously tried branch vertices
            Bits next;
            int count = 0;
            for (int j = 0; j < active_words; ++j) {
                next.bits[j] = candidates.bits[j] & edges[v].bits[j];
                count += std::popcount(next.bits[j]);
            }
            if (count < needed - 1)
                continue;
            int mask = labels[v];
            selected.push_back(mask);
            if (search(next, needed - 1, exceptional_needed - exceptional[mask], common & mask))
                return true;
            selected.pop_back();
        }
    }
    return false;
}

bool check_pair(int r, int s) {
    int first = exceptional_masks[r], second = exceptional_masks[s];
    if (!ap[first & second])
        return false;
    ++pairs_checked;
    labels.clear();
    for (int mask : masks) {
        if (!exceptional[mask] && ap[first & mask] && ap[second & mask])
            labels.push_back(mask);
    }
    for (int t = s + 1; t < (int)exceptional_masks.size(); ++t) {
        int mask = exceptional_masks[t];
        if (ap[first & mask] && ap[second & mask])
            labels.push_back(mask);
    }
    int size = labels.size();
    if (size < target - 2)
        return false;
    // Local degree order improves greedy coloring. Its choice does not affect validity.
    std::vector<std::pair<int, int>> order;
    for (int a : labels) {
        int d = 0;
        for (int b : labels)
            d += a != b && ap[a & b];
        order.emplace_back(-d, a);
    }
    std::sort(order.begin(), order.end());
    for (int v = 0; v < size; ++v)
        labels[v] = order[v].second;
    active_words = (size + 63) / 64;
    for (Bits &pool : avoids)
        pool = {};
    exceptional_candidates = {};
    Bits candidates;
    for (int v = 0; v < size; ++v) {
        int mask = labels[v];
        edges[v] = {};
        for (int w = 0; w < size; ++w)
            if (w != v && ap[mask & labels[w]])
                edges[v].add(w);
        for (int m = 0; m < N; ++m)
            if (!(mask >> m & 1))
                avoids[m].add(v);
        if (exceptional[mask])
            exceptional_candidates.add(v);
        candidates.add(v);
    }
    selected = {first, second};
    return search(candidates, target - 2, 2, first & second);
}

int main(int argc, char **argv) {
    bool simple = argc == 2 && std::string_view(argv[1]) == "--simple";
    if (argc != 1 && !simple) {
        std::cerr << "Usage: verify [--simple]\n"
                  << "  --simple: 315 exceptional masks (one-page proof)\n"
                  << "  default:  300 exceptional masks (also run short_bound.py)\n";
        return 2;
    }
    for (int start = 0; start < N; ++start) {
        for (int step = 1; step <= N; ++step) {
            int mask = 0;
            for (int i = start; i < N; i += step) {
                mask |= 1 << i;
                ap[mask] = true;
            }
        }
    }
    for (int p = 1; p < limit; ++p) {
        if (!ap[p] || std::popcount((unsigned)p) != 7)
            continue;
        for (int mask = 1; mask < limit; ++mask)
            if ((p & mask) == p)
                exceptional[mask] = true;
    }
    std::cout << (simple
                      ? "Reduction: five-term APs and sets containing a seven-term AP.\n"
                      : "Reduction: sets containing a seven-term AP (requires short_bound.py).\n");
    {
        int short_count = 0;
        std::vector<int> negative_aps;
        for (int p = 1; p < limit; ++p) {
            int length = std::popcount((unsigned)p);
            if (ap[p] && (length == 3 || length == 4 || length == 6))
                negative_aps.push_back(p);
        }
        for (int mask = 1; mask < limit; ++mask) {
            if (exceptional[mask])
                continue;
            ++short_count;
            int size = std::popcount((unsigned)mask);
            int score = (size - 1) * (size - 2) / 2;
            for (int p : negative_aps)
                if ((mask & p) == p)
                    --score;
            if ((ap[mask] && score != 0) || (!ap[mask] && score <= 0)) {
                std::cerr << "Score check failed at mask " << mask << '\n';
                return 2;
            }
            // Five-term APs have no coordinate of their own in the proof.
            if (simple && ap[mask] && size == 5)
                exceptional[mask] = true;
        }
        if (short_count != 7891) {
            std::cerr << "Unexpected number of masks avoiding seven-term APs: " << short_count
                      << '\n';
            return 2;
        }
        std::cout << "Score check passed on " << short_count << " nonempty masks.\n";
    }
    for (int mask = 1; mask < limit; ++mask) {
        if (std::popcount((unsigned)mask) >= 2)
            masks.push_back(mask);
        if (exceptional[mask])
            exceptional_masks.push_back(mask);
    }
    if (exceptional_masks.size() != (simple ? 315u : 300u)) {
        std::cerr << "Unexpected exceptional mask count: " << exceptional_masks.size() << '\n';
        return 2;
    }
    for (int a : exceptional_masks)
        for (int b : masks)
            degree[a] += a != b && ap[a & b];
    std::sort(exceptional_masks.begin(), exceptional_masks.end(),
              [](int a, int b) { return std::pair(degree[a], a) < std::pair(degree[b], b); });
    for (int r = 0; r < (int)exceptional_masks.size(); ++r) {
        for (int s = r + 1; s < (int)exceptional_masks.size(); ++s) {
            if (check_pair(r, s)) {
                std::cout << "Clique found (masks):";
                for (int mask : selected)
                    std::cout << ' ' << mask;
                std::cout << '\n';
                return 1;
            }
        }
    }
    if (pairs_checked != (simple ? 9862u : 6357u)) {
        std::cerr << "Unexpected compatible pair count: " << pairs_checked << '\n';
        return 2;
    }
    std::cout
        << "Exceptional masks: " << exceptional_masks.size()
        << "\nCompatible first pairs: " << pairs_checked << "\nSearch nodes: " << nodes
        << "\nNo 83-clique with empty total intersection and four or more exceptional sets.\n";
}
