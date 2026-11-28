#include <algorithm>
#include <array>
#include <bit>
#include <charconv>
#include <cstdint>
#include <iostream>
#include <set>
#include <string>
#include <string_view>
#include <vector>

// Canli's published seven-coloring of [77], in increasing position order.
constexpr std::string_view published = "11621104463534521203342250566043463151352021104225456604146315040331262162520";
constexpr int length = 78;
using Progression = std::array<int, 4>;
using Triple = std::array<int, 3>;

std::string normalize_colors(std::string word) {
    std::array<int, 7> names;
    names.fill(-1);
    int next = 0;
    for (char& digit : word) {
        int& name = names[digit - '0'];
        if (name == -1) name = next++;
        digit = static_cast<char>('0' + name);
    }
    return word;
}

struct Search {
    // A singleton bit represents an assigned color. Zero denotes a free position.
    std::array<unsigned, length> target{};
    std::array<unsigned, length - 1> source{};
    std::array<std::vector<std::array<int, 2>>, length> prior_pairs;
    std::array<std::vector<Triple>, length> prior_triples;
    std::array<std::vector<Progression>, length> incident;
    std::vector<Progression> progressions;
    std::uint64_t nodes = 0;
    std::uint64_t placements = 0;

    Search() {
        std::string word(published);
        std::string reversed(word.rbegin(), word.rend());
        word = std::min(normalize_colors(word), normalize_colors(reversed));
        for (int i = 0; i < static_cast<int>(source.size()); ++i) {
            source[i] = 1u << (word[i] - '0');
        }
        std::set<Triple> subtriples;
        for (int a = 0; a < length; ++a) {
            for (int d = 1; a + 3*d < length; ++d) {
                Progression p{a, a+d, a+2*d, a+3*d};
                progressions.push_back(p);
                prior_triples[p[3]].push_back({p[0], p[1], p[2]});
                for (int omitted = 0; omitted < 4; ++omitted) {
                    incident[p[omitted]].push_back(p);
                    Triple t{};
                    int k = 0;
                    for (int j = 0; j < 4; ++j) {
                        if (j != omitted) t[k++] = p[j];
                    }
                    subtriples.insert(t);
                }
            }
        }
        for (auto [a, b, c] : subtriples) prior_pairs[c].push_back({a, b});
    }

    // A valid completion cannot have three equal colors anywhere on one progression.
    // If a progression is already full, it must also contain at least three colors.
    bool can_match(int pos, unsigned color) const {
        for (auto [a, b] : prior_pairs[pos]) {
            if (target[a] == color && target[b] == color) return false;
        }
        for (auto [a, b, c] : prior_triples[pos]) {
            if (target[a] && target[b] && target[c] &&
                std::popcount(target[a] | target[b] | target[c] | color) < 3) return false;
        }
        return true;
    }

    bool consistent_at(int pos) const {
        for (const auto& p : incident[pos]) {
            unsigned colors = 0;
            int assigned = 0;
            for (int i : p) {
                colors |= target[i];
                assigned += target[i] != 0;
            }
            // The unassigned terms of this progression can add at most one color each.
            if (std::popcount(colors) + 4 - assigned < 3) return false;
        }
        return true;
    }

    bool fill_free_positions() {
        int best_pos = -1;
        unsigned best_options = 127;
        for (int i = 0; i < length; ++i) {
            if (target[i]) continue;
            unsigned options = 0;
            for (unsigned c = 1; c < 128; c <<= 1) {
                target[i] = c;
                if (consistent_at(i)) options |= c;
            }
            target[i] = 0;
            if (!options) return false;
            if (best_pos == -1 || std::popcount(options) < std::popcount(best_options)) {
                best_pos = i;
                best_options = options;
            }
        }
        if (best_pos == -1) {
            for (const auto& p : progressions) {
                unsigned m = target[p[0]] | target[p[1]] | target[p[2]] | target[p[3]];
                if (std::popcount(m) < 3) return false;
            }
            return true;
        }
        for (unsigned c = 1; c < 128; c <<= 1) {
            if (!(best_options & c)) continue;
            target[best_pos] = c;
            if (fill_free_positions()) return true;
        }
        target[best_pos] = 0;
        return false;
    }

    // Between successive matches, skipping source positions commutes with leaving
    // target positions free. Always place the source skips first in such a gap.
    bool visit(int s, int t, int deletions, int insertions, bool just_inserted) {
        ++nodes;
        if (s == static_cast<int>(source.size()) && t == length) {
            ++placements;
            return fill_free_positions();
        }
        if (s < static_cast<int>(source.size()) && t < length && can_match(t, source[s])) {
            target[t] = source[s];
            if (visit(s+1, t+1, deletions, insertions, false)) return true;
            target[t] = 0;
        }
        if (s < static_cast<int>(source.size()) && deletions && !just_inserted) {
            if (visit(s+1, t, deletions-1, insertions, false)) return true;
        }
        if (t < length && insertions) {
            if (visit(s, t+1, deletions, insertions-1, true)) return true;
        }
        return false;
    }
};

int main(int argc, char** argv) {
    static_assert(published.size() == 77);
    int radius = 3;
    if (argc == 2) {
        std::string_view text(argv[1]);
        const auto [end, ec] = std::from_chars(text.data(), text.data()+text.size(), radius);
        if (ec != std::errc{} || end != text.data()+text.size() || radius < 0 || radius > 77) return 2;
    } else if (argc != 1) return 2;
    Search search;
    bool found = search.visit(0, 0, radius, radius+1, false);
    std::cout << "Source deletions " << radius << ", target insertions " << radius+1
              << ", nodes " << search.nodes << ", consistent placements " << search.placements << '\n';
    if (found) {
        for (unsigned color : search.target) std::cout << std::countr_zero(color);
        std::cout << '\n';
        return 1;
    }
    std::cout << "No valid seven-coloring has a common subsequence of length " << 77-radius
              << " with the published word.\n";
    return 0;
}
