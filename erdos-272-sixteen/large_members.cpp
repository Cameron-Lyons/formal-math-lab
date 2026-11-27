// Exclude a family of 125 containing a large member, by graph coloring.
#include "compatibility_graph.hpp"
#include <charconv>
#include <iostream>
#include <string_view>

using namespace erdos272_graph;

namespace {
const Progressions ap = progressions(points);

int reflected(int a) {
    int image = 0;
    for (int i = 0; i < points; ++i) image = (image << 1) | ((a >> i) & 1);
    return image;
}

bool excludes_largest_member(int root, int target) {
    // Every other member meets the chosen largest member in a nonempty AP.
    const int largest = cardinality(root);
    std::vector<int> candidates;
    for (int a = 1; a < limit; ++a) {
        int size = cardinality(a);
        if (a != root && size >= 2 && size <= largest && ap[a & root]) candidates.push_back(a);
    }
    const int need = target - 1;
    int count = candidates.size();
    if (count < need) return true;
    Graph graph = ordered_graph(std::move(candidates), ap);
    Bits live(graph.words, ~Word{0});
    if (count % 64) live.back() = (Word{1} << (count % 64)) - 1;
    Bits pool = live;
    if (!graph.required_pool(pool, count, need)) return true;
    count = graph.refine(live, count, need, [](int a) { return cardinality(a) <= 3; });
    return count < need || !graph.required_pool(live, count, need);
}
} // namespace

int main(int argc, char** argv) {
    int minimum = 13, target = 125;
    if (argc > 3) return 1;
    for (int i = 1; i < argc; ++i) {
        std::string_view arg(argv[i]);
        int& value = i == 1 ? minimum : target;
        auto [end, error] = std::from_chars(arg.data(), arg.data() + arg.size(), value);
        if (error != std::errc{} || end != arg.data() + arg.size()) return 1;
    }
    if (minimum < 2 || minimum > points || target < 125 || target >= limit) return 1;
    for (int size = points; size >= minimum; --size) {
        int count = 0;
        for (int a = 1; a < limit; ++a) {
            if (cardinality(a) != size || a > reflected(a)) continue;
            if (!excludes_largest_member(a, target)) {
                std::cerr << "Unexcluded largest member at mask " << a << '\n';
                return 2;
            }
            ++count;
        }
        std::cout << "Size " << size << ": all " << count << " cases excluded." << std::endl;
    }
}
