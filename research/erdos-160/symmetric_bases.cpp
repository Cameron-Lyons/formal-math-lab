// Exact small-palette extrema for the symmetric pattern ABBA.
// Build with c++ -O3 -std=c++20 symmetric_bases.cpp -o symmetric_bases.
#include <algorithm>
#include <bit>
#include <cstdint>
#include <iostream>
#include <map>
#include <set>
#include <stdexcept>
#include <string>

namespace {
std::string normalize(std::string word) {
    std::map<char, char> renaming;
    for (char &c : word) {
        const char next = static_cast<char>('0' + renaming.size());
        c = renaming.emplace(c, next).first->second;
    }
    return word;
}

bool cyclic_valid(const std::string &w) {
    const int n = static_cast<int>(w.size());
    for (int d = 1; d <= n / 2; ++d) {
        for (int a = 0; a < n; ++a) {
            if (w[a] == w[(a + 3 * d) % n] && w[(a + d) % n] == w[(a + 2 * d) % n])
                return false;
        }
    }
    return true;
}

class PrefixSearch {
    const int palette;
    const int interval_max;
    const int cyclic_max;
    std::string word;
    std::uint64_t nodes = 0;
    std::uint64_t longest_words = 0;
    int longest = 0;
    int largest_cycle = 0;
    std::set<std::string> interval_extremals;
    std::set<std::string> cyclic_extremals;

    void visit(unsigned used) {
        ++nodes;
        const int n = static_cast<int>(word.size());
        longest = std::max(longest, n);
        if (n > interval_max)
            throw std::logic_error("longer interval found: " + word);
        if (n == interval_max) {
            ++longest_words;
            std::string reversed(word.rbegin(), word.rend());
            interval_extremals.insert(std::min(word, normalize(reversed)));
        }
        // Any cyclic word of length m repeats to a valid interval of length 3m.
        // Smaller moduli cannot affect the stated maximum; all larger candidates
        // are either tested here or excluded by the simultaneous interval search.
        if (cyclic_max <= n && 3 * n <= interval_max && cyclic_valid(word)) {
            largest_cycle = std::max(largest_cycle, n);
            if (n == cyclic_max)
                cyclic_extremals.insert(word);
        }

        // Any color unseen so far may be named 'used'. Test that one fresh
        // name and each old name. Position n completes exactly these APs.
        unsigned allowed = (1u << std::min<unsigned>(palette, used + 1)) - 1;
        for (int d = 1; 3 * d <= n && allowed; ++d) {
            if (word[n - d] == word[n - 2 * d])
                allowed &= ~(1u << (word[n - 3 * d] - '0'));
        }
        while (allowed) {
            const auto c = static_cast<unsigned>(std::countr_zero(allowed));
            allowed &= allowed - 1;
            word.push_back(static_cast<char>('0' + c));
            visit(std::max(used, c + 1));
            word.pop_back();
        }
    }

  public:
    PrefixSearch(int colors, int interval, int cyclic)
        : palette(colors), interval_max(interval), cyclic_max(cyclic) {}

    void verify() {
        visit(0);
        if (longest != interval_max || largest_cycle != cyclic_max)
            throw std::logic_error("extremal values disagree");
        if (palette == 3) {
            // The published word of Deng, Tidor and Zhao generates every extremal.
            std::string published = "1333221232131211333233";
            std::set<std::string> rotations;
            for (int i = 0; i < cyclic_max; ++i) {
                rotations.insert(normalize(published));
                std::rotate(published.begin(), published.begin() + 1, published.end());
            }
            if (cyclic_extremals != rotations)
                throw std::logic_error("unexpected cycle");
        }
        std::cout << palette << " colors, maximum interval " << longest
                  << ", maximum cyclic modulus " << largest_cycle << ", " << nodes
                  << " prefixes. At maximum length: interval words up to color renaming = "
                  << longest_words << ", reversal classes = " << interval_extremals.size()
                  << ", cyclic words up to color renaming = " << cyclic_extremals.size() << ".\n";
        std::cout << "Interval witness: " << *interval_extremals.begin() << '\n';
    }
};
} // namespace

int main() {
    PrefixSearch(2, 14, 2).verify();
    PrefixSearch(3, 69, 22).verify();
}
