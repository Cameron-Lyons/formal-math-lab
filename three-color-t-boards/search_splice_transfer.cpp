// Enumerate new caps above a fixed row 6. Input lines contain an integer
// witness ID and rows 0 through 6 of one valid board, in flat ternary form.
#include <array>
#include <bit>
#include <iostream>
#include <string>

using Counts = std::array<unsigned, 27>;

struct ReverseSearch {
    std::array<std::array<unsigned, 13>, 7> rows{};
    Counts available{};
    std::string old_pivot;
    unsigned id;

    unsigned triple(unsigned row, unsigned j) const {
        return 9 * rows[row][j] + 3 * rows[row][j + 1] + rows[row][j + 2];
    }

    void record() const {
        std::string prefix;
        for (unsigned r = 0; r <= 5; ++r)
            for (unsigned j = 0; j < 2*r + 1; ++j)
                prefix.push_back(static_cast<char>('0' + rows[r][j]));
        if (prefix.substr(25) != old_pivot)
            std::cout << id << ' ' << prefix << '\n';
    }

    void row(unsigned r) {
        if (r == 0) {
            record();
            return;
        }
        Counts needed{}, next_needed{};
        for (unsigned j = 0; j < 2*r - 1; ++j)
            ++needed[triple(r, j)];
        fill(r, 0, needed, next_needed);
    }

    void fill(unsigned r, unsigned j, Counts& needed, Counts& next_needed) {
        if (j == 2*r - 1) {
            row(r - 1);
            return;
        }
        unsigned lower = triple(r, j);
        unsigned options = available[lower];
        --needed[lower];
        while (options) {
            unsigned top = std::countr_zero(options);
            unsigned bit = 1u << top;
            options ^= bit;
            available[lower] ^= bit;
            rows[r - 1][j] = top;
            unsigned upper = j < 2 ? lower : triple(r - 1, j - 2);
            if (j >= 2)
                ++next_needed[upper];
            auto enough = [&](unsigned code) {
                return needed[code] + next_needed[code] <=
                       static_cast<unsigned>(std::popcount(available[code]));
            };
            if (enough(lower) && enough(upper))
                fill(r, j + 1, needed, next_needed);
            if (j >= 2)
                --next_needed[upper];
            available[lower] ^= bit;
        }
        ++needed[lower];
    }

    bool init(const std::string& prefix) {
        if (prefix.size() != 49 || prefix.find_first_not_of("012") != std::string::npos)
            return false;
        old_pivot = prefix.substr(25, 11);
        for (unsigned r = 0; r <= 6; ++r) {
            for (unsigned j = 0; j < 2*r + 1; ++j)
                rows[r][j] = prefix[r*r + j] - '0';
            for (unsigned j = 0; r > 0 && j < 2*r - 1; ++j) {
                unsigned bit = 1u << rows[r-1][j];
                auto& mask = available[triple(r, j)];
                if (mask & bit)
                    return false;
                mask |= bit;
            }
        }
        return true;
    }
};

int main() {
    unsigned id;
    std::string prefix;
    while (std::cin >> id >> prefix) {
        ReverseSearch search;
        search.id = id;
        if (!search.init(prefix)) {
            std::cerr << "Invalid seven-row input at witness " << id << '\n';
            return 1;
        }
        search.row(6);
    }
    return std::cin.eof() ? 0 : 1;
}
