// Test prescribed intersections in a 125-member family whose members have size at most 12.
#include "compatibility_graph.hpp"
#include <charconv>
#include <iostream>
#include <string_view>

using namespace erdos272_graph;

namespace {
const Progressions ap = progressions(points);
constexpr int max_member = 12;
constexpr int target = 125;

int reflected(int a) {
    int image = 0;
    for (int i = 0; i < points; ++i) image = (image << 1) | ((a >> i) & 1);
    return image;
}

template<class Predicate>
bool supports(const Graph& graph, const Bits& live, const std::vector<int>& fixed,
              int required, Predicate satisfies) {
    for (int a : fixed) required -= satisfies(a);
    if (required <= 0) return true;
    Bits pool = live;
    int size = 0;
    for (int j = 0; j < static_cast<int>(graph.labels.size()); ++j) if (has(pool, j)) {
        if (satisfies(graph.labels[j])) ++size;
        else erase(pool, j);
    }
    return graph.required_pool(pool, size, required);
}

// The input already respects the fixed members preceding fixed.back().
bool excludes(const std::vector<int>& fixed, const std::vector<int>& previous) {
    const int latest = fixed.back();
    const int goal = target - static_cast<int>(fixed.size());
    std::vector<int> candidates;
    for (int a : previous)
        if (a != latest && ap[a & latest]) candidates.push_back(a);
    int count = candidates.size();
    if (count < goal) return true;
    Graph graph = ordered_graph(std::move(candidates), ap);
    Bits live(graph.words, ~Word{0});
    if (count % 64) live.back() = (Word{1} << (count % 64)) - 1;
    Bits pool = live;
    if (!graph.required_pool(pool, count, goal)) return true;
    count = graph.refine(live, count, goal, [](int a) { return cardinality(a) <= 3; });
    if (count < goal) return true;
    pool = live;
    if (!graph.required_pool(pool, count, goal)) return true;

    for (int i = 0; i < points; ++i)
        if (!supports(graph, live, fixed, 14, [i](int a) { return !(a & (1 << i)); })) return true;
    if (!supports(graph, live, fixed, 32, [](int a) { return cardinality(a) <= 4; }) ||
        !supports(graph, live, fixed, 10, [](int a) { return cardinality(a) <= 3; })) return true;
    if (fixed.size() == 3) return false;

    // Every putative family contains a three-element member which is not a progression.
    std::vector<int> survivors;
    for (int j = 0; j < static_cast<int>(graph.labels.size()); ++j)
        if (has(live, j)) survivors.push_back(graph.labels[j]);
    for (int t : survivors)
        if (cardinality(t) == 3 && !ap[t] && !excludes({fixed[0], fixed[1], t}, survivors)) return false;
    return true;
}

bool check_progression(int p, int& cases) {
    std::vector<int> possible;
    for (int a = 1; a < limit; ++a)
        if (a != p && cardinality(a) >= 2 && cardinality(a) <= max_member &&
            (!(a & p) || ap[a & p])) possible.push_back(a);
    possible.push_back(p);
    int outside = (limit - 1) ^ p;
    for (int x = outside; ; x = (x - 1) & outside) {
        int a = p | x;
        if (cardinality(a) <= max_member) {
            std::vector<int> companions;
            for (int m : possible) if (m != a && ap[m & a]) companions.push_back(m);
            int unused = outside ^ x;
            for (int y = unused; ; y = (y - 1) & unused) {
                int b = p | y;
                if (a < b && cardinality(b) <= max_member) {
                    int ra = reflected(a), rb = reflected(b);
                    if (std::pair{a, b} <= std::pair{std::min(ra, rb), std::max(ra, rb)}) {
                        if (!excludes({a, b}, companions)) {
                            std::cerr << "Unexcluded masks " << a << " and " << b << '\n';
                            return false;
                        }
                        ++cases;
                    }
                }
                if (!y) break;
            }
        }
        if (!x) break;
    }
    return true;
}
} // namespace

int main(int argc, char** argv) {
    int length = 11;
    if (argc == 2) {
        std::string_view arg(argv[1]);
        auto [end, error] = std::from_chars(arg.data(), arg.data() + arg.size(), length);
        if (error != std::errc{} || end != arg.data() + arg.size()) return 1;
    }
    if (argc > 2 || length < 7 || length >= max_member) return 1;
    int cases = 0;
    for (int p = 1; p < limit; ++p)
        if (ap[p] && cardinality(p) == length && !check_progression(p, cases)) return 2;
    std::cout << "Intersection length " << length << ": all " << cases << " cases excluded.\n";
    return 0;
}
