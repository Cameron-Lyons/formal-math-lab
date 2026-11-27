// Replay the elimination of small members in a fixed marked case.
#include "private_triples.hpp"
#include <charconv>
#include <fstream>
#include <iostream>
#include <map>
#include <sstream>
#include <string>
#include <string_view>

using namespace erdos272_private;

namespace {
struct Requirements {
    int target = 125;
    int marks = 4;
    int through_three = 2;
    int nonprogression_triples = 1;
    int large_members = at_least_five_bound;
};
// In a short-intersection quartet every size bound is derived locally.
constexpr Requirements short_requirements{125, 0, 0, 0, 125};
std::array<bool, limit> excluded_candidate{};
std::uint64_t work, work_limit;
struct BudgetReached {};

int bound(const std::vector<int>& roots, int s, const std::vector<int>& domain,
          const std::array<bool, limit>& allowed, int price_limit = max_price) {
    if (work_limit && work == work_limit) throw BudgetReached{};
    ++work;
    return private_triple_bound(roots, s, domain, allowed, price_limit);
}

// A completion using need of these candidates must meet at least need colors.
bool enough_colors(const std::vector<int>& pool, const std::array<bool, limit>* allowed,
                   int s, int need) {
    if (need <= 0) return true;
    std::vector<std::vector<int>> colors;
    for (int a : pool) {
        if ((allowed && !(*allowed)[a]) || (s && (a == s || !compatible_trace[a & s]))) continue;
        auto group = std::find_if(colors.begin(), colors.end(), [a](const auto& cls) {
            return std::none_of(cls.begin(), cls.end(), [a](int b) { return compatible_trace[a & b]; });
        });
        if (group == colors.end()) {
            colors.push_back({a});
            if (static_cast<int>(colors.size()) == need) return true;
        } else {
            group->push_back(a);
        }
    }
    return false;
}

bool exclude_with_roots(const std::vector<int>& roots, int largest_mark,
                        const Requirements& required) {
    const int target = required.target;
    std::vector<int> domain, small, large, further_marks;
    std::array<bool, limit> allowed{};
    for (int a = 1; a < limit; ++a) {
        if (size(a) < 2 || excluded_candidate[a] || (marked[a] && size(a) > largest_mark)) continue;
        if (std::any_of(roots.begin(), roots.end(), [a](int r) {
            return a == r || !compatible_trace[a & r];
        })) continue;
        domain.push_back(a);
        if (marked[a]) further_marks.push_back(a);
        if (size(a) <= 4) {
            small.push_back(a);
            allowed[a] = true;
        } else {
            large.push_back(a);
        }
    }

    int marks_needed = required.marks, fixed_small = 0, fixed_through_three = 0, fixed_nonap_triples = 0;
    for (int r : roots) {
        marks_needed -= marked[r];
        fixed_small += size(r) <= 4;
        fixed_through_three += size(r) <= 3;
        fixed_nonap_triples += size(r) == 3 && !progression[r];
    }
    if (!enough_colors(further_marks, nullptr, 0, marks_needed)) return true;
    if (bound(roots, 0, domain, allowed) < target) return true;
    const int large_bound = std::min(required.large_members,
                                      bound(roots, 0, large, allowed, 10) - fixed_small);
    const int small_needed = target - large_bound - fixed_small;
    std::stable_sort(small.begin(), small.end(), [](int a, int b) { return size(a) < size(b); });

    for (;;) {
        int remaining = 0, removed = 0, through_three = fixed_through_three;
        int nonap_triples = fixed_nonap_triples;
        bool reached_four = false;
        for (int s : small) {
            if (!allowed[s]) continue;
            if (size(s) == 4 && !reached_four) {
                if (nonap_triples < required.nonprogression_triples || through_three < required.through_three)
                    return true;
                if (removed > 15 && bound(roots, 0, domain, allowed) < target) return true;
                reached_four = true;
            }
            if (!enough_colors(further_marks, nullptr, s, marks_needed) ||
                !enough_colors(small, &allowed, s, small_needed - 1) ||
                bound(roots, s, domain, allowed) < target) {
                allowed[s] = false;
                ++removed;
            } else {
                ++remaining;
                through_three += size(s) <= 3;
                nonap_triples += size(s) == 3 && !progression[s];
            }
        }
        if (remaining < small_needed || !enough_colors(small, &allowed, 0, small_needed)) return true;
        if (!removed) return false;
    }
}

bool exclude_case(const std::vector<int>& roots, int largest_mark, const Requirements& required) {
    if (exclude_with_roots(roots, largest_mark, required)) return true;

    std::vector<int> candidates;
    for (int t = 1; t < limit; ++t) {
        if (size(t) == 3 && !progression[t] &&
            std::all_of(roots.begin(), roots.end(), [t](int r) { return compatible_trace[r & t]; }))
            candidates.push_back(t);
    }
    // Try fixing each candidate triple. After excluding it, subsequent
    // branches may omit it. Also test the case with all exclusions in force.
    for (;;) {
        int left = 0, removed = 0;
        for (int t : candidates) {
            if (excluded_candidate[t]) continue;
            auto next = roots;
            next.push_back(t);
            if (exclude_with_roots(next, largest_mark, required)) {
                excluded_candidate[t] = true;
                ++removed;
            } else {
                ++left;
            }
        }
        if (!left && required.nonprogression_triples > 0) return true;
        if (exclude_with_roots(roots, largest_mark, required)) return true;
        if (!left || !removed) return false;
    }
}

bool load_weighted_marks(const char* path) {
    std::ifstream input(path);
    int a, weight;
    while (input >> a) {
        if (!(input >> weight) || a <= 0 || a >= limit || weight < 0) return false;
        marked[a] = weight == 0;
    }
    return input.eof() && std::count(marked.begin(), marked.end(), true) == 363;
}

bool set_short_marks() {
    std::vector<int> score_terms;
    for (int p = 1; p < limit; ++p) {
        if (progression[p] && (size(p) == 3 || size(p) == 4 || size(p) == 6)) score_terms.push_back(p);
        compatible_trace[p] = progression[p] && size(p) <= 6;
    }
    for (int a = 1; a < limit; ++a) {
        if (compatible_trace[a]) continue;
        const int k = size(a);
        int score = (k - 1) * (k - 2) / 2;
        for (int p : score_terms) score -= (a & p) == p;
        marked[a] = score <= 0;
    }
    return std::count(marked.begin(), marked.end(), true) == 101;
}

// Read the order of the marks and the possible first four from verify_short.py.
int check_short_quartets() {
    initialize();
    if (!set_short_marks()) return 1;
    int count;
    if (!(std::cin >> count) || count != 101) return 1;
    std::vector<int> order(count);
    std::array<int, limit> position;
    position.fill(-1);
    for (int i = 0; i < count; ++i) {
        int& a = order[i];
        if (!(std::cin >> a) || a <= 0 || a >= limit || !marked[a] || position[a] != -1) return 1;
        position[a] = i;
    }
    int checked = 0, length;
    while (std::cin >> length && length == 4) {
        std::vector<int> roots(4);
        int last = -1;
        for (int& a : roots) {
            if (!(std::cin >> a) || a <= 0 || a >= limit || position[a] <= last) return 1;
            last = position[a];
        }
        excluded_candidate.fill(false);
        for (int i = 0; i <= last; ++i) excluded_candidate[order[i]] = true;
        if (!exclude_case(roots, n, short_requirements)) {
            std::cerr << "Unexcluded quartet";
            for (int a : roots) std::cerr << ' ' << a;
            std::cerr << '\n';
            return 2;
        }
        ++checked;
        if (checked % 100 == 0) std::cerr << "Checked " << checked << " quartets\n";
    }
    int expected;
    if (!std::cin || length != 0 || !(std::cin >> expected) || expected != checked) return 1;
    std::cout << "Excluded 125 members in " << checked << " quartets by private triples.\n";
    return 0;
}

struct Case { int id; std::vector<int> roots; };

std::vector<Case> make_cases(bool short_mode) {
    std::vector<Case> cases;
    if (!short_mode) {
        for (int a = 1; a < limit; ++a)
            if (marked[a] && size(a) >= 8 && a <= reflected(a)) cases.push_back({a, {a}});
    }
    for (int signature = 0; signature < (1 << seven.size()); ++signature) {
        if (size(signature) != 4) continue;
        std::vector<int> roots, reflected_roots;
        for (std::size_t i = 0; i < seven.size(); ++i)
            if ((signature >> i) & 1) {
                roots.push_back(seven[i]);
                reflected_roots.push_back(reflected(seven[i]));
            }
        std::sort(reflected_roots.begin(), reflected_roots.end());
        if (reflected_roots < roots) continue;
        bool ok = true;
        for (int a : roots)
            for (int b : roots)
                if (a != b && !compatible_trace[a & b]) ok = false;
        if (ok) cases.push_back({limit + signature, roots});
    }
    return cases;
}

struct RecordedCase {
    bool closed;
    bool large_member;
    std::uint64_t budget;
};

bool load_status(const char* path, std::map<int, RecordedCase>& ledger) {
    std::ifstream input(path);
    std::string line;
    while (std::getline(input, line)) {
        if (line.empty() || line.front() == '#') continue;
        std::istringstream row(line);
        std::string state;
        std::uint64_t budget;
        if (!(row >> state >> budget) || (state != "closed" && state != "budget" && state != "open" && state != "large")) return false;
        int id;
        bool any = false;
        while (row >> id) {
            if (!ledger.emplace(id, RecordedCase{state == "closed", state == "large", budget}).second) return false;
            any = true;
        }
        if (!row.eof() || !any) return false;
    }
    return input.eof();
}

template<typename T> bool parse(std::string_view text, T& value) {
    const auto [last, error] = std::from_chars(text.data(), text.data() + text.size(), value);
    return error == std::errc{} && last == text.data() + text.size();
}
} // namespace

int main(int argc, char** argv) {
    if (argc == 2 && std::string_view(argv[1]) == "quartets") return check_short_quartets();
    if (argc == 2 && std::string_view(argv[1]) == "residual-triples") {
        initialize();
        if (triples.size() != 504) return 1;
        for (const auto& t : triples) excluded_candidate[t.mask] = true;
        // A 116-member residual retains a pair or progression triple because
        // the original family has at most 115 members of size at least four.
        constexpr Requirements residual{116, 0, 1, 0};
        int cases = 0;
        for (int s = 1; s < limit; ++s) {
            if (size(s) < 2 || size(s) > 3 || !progression[s] || s > reflected(s)) continue;
            if (!exclude_with_roots({s}, n, residual)) {
                std::cerr << "Unexcluded residual member " << s << '\n';
                return 1;
            }
            ++cases;
        }
        std::cout << cases << " pair and progression-triple roots excluded at " << residual.target
                  << " residual members.\n";
        return cases == 92 ? 0 : 1;
    }
    if (argc < 3) return 1;
    const bool short_mode = std::string_view(argv[1]) == "short";
    if (!short_mode && std::string_view(argv[1]) != "full") return 1;
    const int budget_arg = short_mode ? 2 : 3;
    if (argc < budget_arg + 1 || argc > budget_arg + 3) {
        std::cerr << "Expected full WEIGHTS or short, then WORK or list and optional FIRST LAST case IDs.\n";
        return 1;
    }
    const bool list = std::string_view(argv[budget_arg]) == "list";
    const bool replay = std::string_view(argv[budget_arg]) == "replay";
    std::map<int, RecordedCase> ledger;
    if (replay) {
        if (argc != budget_arg + 2 || !load_status(argv[budget_arg + 1], ledger)) return 1;
    } else if (!list && !parse(argv[budget_arg], work_limit)) {
        return 1;
    }
    int first = 1, last = 2 * limit;
    if (!replay && argc > budget_arg + 1) {
        if (!parse(argv[budget_arg + 1], first)) return 1;
        last = first;
    }
    if (argc > budget_arg + 2 && !parse(argv[budget_arg + 2], last)) return 1;

    initialize();
    if (seven.size() != 14 || triples.size() != 504 ||
        !(short_mode ? set_short_marks() : load_weighted_marks(argv[2]))) return 1;
    for (int a = 1; a < limit; ++a)
        if (marked[a] != marked[reflected(a)]) return 1;
    const auto cases = make_cases(short_mode);
    if (cases.size() != (short_mode ? 248u : 426u)) return 1;
    // The short-intersection proof derives every size bound from the fixed
    // quartet. It also checks the branch with no nonprogression triple.
    const auto required = short_mode ? short_requirements : Requirements{};
    if (replay && ledger.size() != cases.size()) return 1;
    int checked = 0, pending = 0, external = 0;
    for (const auto& [id, roots] : cases) {
        if (id < first || id > last) continue;
        if (replay) {
            const auto entry = ledger.find(id);
            if (entry == ledger.end()) return 1;
            if (entry->second.large_member) {
                if (short_mode || roots.size() != 1 || size(roots.front()) < 13) return 1;
                ++external;
                continue;
            }
            if (!entry->second.closed) {
                ++pending;
                continue;
            }
            work_limit = entry->second.budget;
        }
        ++checked;
        if (list) {
            std::cout << id;
            for (int r : roots) std::cout << ' ' << r;
            std::cout << '\n';
            continue;
        }
        work = 0;
        excluded_candidate.fill(false);
        const char* state = "open";
        try {
            if (exclude_case(roots, size(roots.front()), required)) state = "closed";
        } catch (const BudgetReached&) {
            state = "budget";
        }
        if (replay && std::string_view(state) != "closed") {
            std::cerr << "Failed to replay case " << id << '\n';
            return 1;
        }
        std::cout << id << ' ' << state << ' ' << work << ' '
                  << std::count(excluded_candidate.begin(), excluded_candidate.end(), true) << std::endl;
    }
    if (replay) std::cout << checked << " closed cases replayed, " << external
                          << " external large-member cases, " << pending << " pending.\n";
    return checked || (replay && (pending || external)) ? 0 : 1;
}
