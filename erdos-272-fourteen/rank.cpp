// Rank bound for the seven-term-progression-free members in Erdős #272 at n = 14.
// Bit i denotes point i+1. See rank.md for the proof.
#include <array>
#include <bit>
#include <iostream>
#include <stdexcept>
#include <vector>

namespace {

using Mask = unsigned;
constexpr int points = 14;
constexpr Mask limit = 1u << points;

bool contains(Mask set, Mask subset) {
    return (set & subset) == subset;
}

bool is_progression(Mask set) {
    if (set == 0) return false;
    int previous = std::countr_zero(set);
    set &= set - 1;
    if (set == 0) return true;
    int step = std::countr_zero(set) - previous;
    while (set != 0) {
        int next = std::countr_zero(set);
        if (next - previous != step) return false;
        previous = next;
        set &= set - 1;
    }
    return true;
}

struct Progressions {
    std::array<bool, limit> is_ap{};
    std::array<std::vector<Mask>, points + 1> by_size;

    Progressions() {
        for (Mask set = 1; set < limit; ++set) {
            if (is_progression(set)) {
                is_ap[set] = true;
                by_size[std::popcount(set)].push_back(set);
            }
        }
    }
};

void check_scores(const Progressions &aps) {
    int exceptional = 0;
    for (Mask set = 1; set < limit; ++set) {
        bool has_seven = false;
        for (Mask p : aps.by_size[7])
            if (contains(set, p)) has_seven = true;
        if (has_seven) {
            ++exceptional;
            continue;
        }
        int size = std::popcount(set);
        int score = 1 + size * (size - 1) / 2 - size;
        for (int length : {3, 4, 6})
            for (Mask p : aps.by_size[length])
                if (contains(set, p)) --score;
        if ((aps.is_ap[set] && score != 0) || (!aps.is_ap[set] && score <= 0)) {
            std::cerr << "Unexpected score " << score << " on mask " << set << '\n';
            throw std::runtime_error("Score check failed");
        }
    }
    if (exceptional != 752) throw std::runtime_error("Exceptional count check failed");
    std::cout << "Score verified on " << limit - 1 - exceptional
              << " nonempty subsets avoiding seven-term progressions; "
              << exceptional << " exceptional subsets.\n";
}

}  // namespace

int main() {
    try {
        const Progressions aps;
        check_scores(aps);
    } catch (const std::exception &err) {
        std::cerr << err.what() << '\n';
        return 1;
    }
}
