// Exhaustively check disjoint equal-length intervals with all entries in [1, N].
// Build with c++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror search.cpp -o search
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <limits>
#include <string>
#include <vector>

using Word = std::uint64_t;

// Hashes only select candidates. Every candidate is checked by divisibility.
Word weight(Word x) {
    x += 0x9e3779b97f4a7c15ULL;
    x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
    x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
    return x ^ (x >> 31);
}

struct Range { int first, last; };
struct Entry { Word signature; int start, next; };

bool dividesIntervalLCM(int value, int start, int length) {
    const int before = start - 1, end = before + length;
    for (int p = 2; p <= value / p; ++p) {
        if (value % p != 0) continue;
        int q = 1;
        do {
            value /= p;
            q *= p;
        } while (value % p == 0);
        if (end / q == before / q) return false;
    }
    return value == 1 || end / value > before / value;
}

bool equalLCMs(int first, int later, int length) {
    for (int i = 0; i < length; ++i) {
        if (!dividesIntervalLCM(first + i, later, length) ||
            !dividesIntervalLCM(later + i, first, length)) return false;
    }
    return true;
}

int main(int argc, char** argv) {
    if (argc != 2) {
        std::cerr << "usage: search ENDPOINT\n";
        return 2;
    }
    const long long input = std::stoll(argv[1]);
    if (input <= 0 || input > std::numeric_limits<int>::max() / 2) return 2;
    const int limit = static_cast<int>(input);
    std::vector<bool> prime(limit + 1, true), primePower(limit + 1, false);
    std::vector<Word> weights(limit + 1), prefix(limit + 1);
    for (int p = 2; p <= limit; ++p) {
        if (!prime[p]) continue;
        if (p <= limit / p) {
            for (int i = p * p; i <= limit; i += p) prime[i] = false;
        }
        for (int q = p; ; q *= p) {
            primePower[q] = true;
            Word w = weight(q);
            for (int i = q; i <= limit; i += q) weights[i] += w;
            if (q > limit / p) break;
        }
    }

    // A prime power in the later interval exceeds every element of the earlier
    // interval. Its prime valuation therefore separates the two LCMs.
    std::vector<Range> gaps;
    int gapStart = 1;
    for (int i = 1; i <= limit + 1; ++i) {
        if (i <= limit && !primePower[i]) continue;
        if (gapStart < i) gaps.push_back({gapStart, i - 1});
        gapStart = i + 1;
    }
    const auto gapSize = [](Range g) { return g.last - g.first + 1; };
    std::sort(gaps.begin(), gaps.end(), [&](Range a, Range b) {
        return gapSize(a) > gapSize(b);
    });
    const int maxLength = gaps.empty() ? 0 : gapSize(gaps.front());
    std::size_t active = gaps.size();
    Word laterWindows = 0, exactChecks = 0, witnesses = 0;
    for (int k = 1; k <= maxLength; ++k) {
        // Every q <= k divides every interval LCM. For q > k, at most one
        // multiple occurs, so the interval sum counts weight(q) exactly once
        // if and only if q divides the LCM. Unsigned overflow is intentional.
        if (primePower[k]) {
            Word w = weight(k);
            for (int i = k; i <= limit; i += k) weights[i] -= w;
        }
        if (k == 1 || primePower[k]) {
            for (int i = 1; i <= limit; ++i) prefix[i] = prefix[i-1] + weights[i];
        }
        while (active > 0 && gapSize(gaps[active-1]) < k) --active;
        int count = 0, maxEarlier = 0;
        for (std::size_t j = 0; j < active; ++j) {
            Range g = gaps[j];
            const int first = std::max(k + 1, g.first), last = g.last - k + 1;
            if (last < first) continue;
            count += last - first + 1;
            maxEarlier = std::max(maxEarlier, last - k);
        }
        laterWindows += count;
        if (!count) continue;
        const auto signature = [&](int start) {
            return prefix[start + k - 1] - prefix[start - 1];
        };
        std::size_t buckets = 1;
        while (buckets < static_cast<std::size_t>(count)) buckets *= 2;
        std::vector<int> heads(buckets, -1);
        std::vector<Entry> entries;
        entries.reserve(count);
        for (std::size_t j = 0; j < active; ++j) {
            Range g = gaps[j];
            for (int b = std::max(k + 1, g.first); b <= g.last - k + 1; ++b) {
                Word sig = signature(b);
                int& head = heads[sig & (buckets - 1)];
                entries.push_back({sig, b, head});
                head = static_cast<int>(entries.size()) - 1;
            }
        }
        for (int a = 1; a <= maxEarlier; ++a) {
            Word sig = signature(a);
            for (int i = heads[sig & (buckets - 1)]; i >= 0; i = entries[i].next) {
                const Entry& e = entries[i];
                if (e.signature != sig || e.start < a + k) continue;
                ++exactChecks;
                if (equalLCMs(a, e.start, k)) {
                    ++witnesses;
                    std::cout << "witness n=" << a - 1 << " m=" << e.start - 1
                              << " k=" << k << std::endl;
                }
            }
        }
    }
    std::cout << "endpoint=" << limit << " longest_prime_power_free_run=" << maxLength
              << " eligible_later_windows=" << laterWindows
              << " exact_checks=" << exactChecks << " witnesses=" << witnesses << '\n';
}
