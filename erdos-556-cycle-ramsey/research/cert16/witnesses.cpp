// Read the complement graph6 representatives produced by geng, and write
// independently checkable path and relabeling witnesses for all extensions.
// Build against nauty's 32-bit, one-word objects.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <sstream>
#include <string>
#include <vector>
extern "C" {
#include "nauty.h"
}
using U = unsigned;
__extension__ using Wide = unsigned __int128;
using Rows = std::array<graph, 16>;
using Perm = std::array<int, 16>;

struct Rep {
    Rows g{};
    Wide code;
    Perm lab{};
};
static std::string number(Wide x) {
    if (!x)
        return "0";
    std::string out;
    for (; x; x /= 10)
        out += char('0' + x % 10);
    std::reverse(out.begin(), out.end());
    return out;
}
static Wide encode(const Rows &g, int n) {
    Wide v = 0;
    for (int i = 0; i < n; i++)
        for (int j = 0; j < i; j++)
            if (g[i] & bit[j])
                v |= Wide(1) << (i * (i - 1) / 2 + j);
    return v;
}
static Wide canon(Rows &g, int n, Perm &lab) {
    DEFAULTOPTIONS_GRAPH(opts);
    opts.getcanon = TRUE;
    int part[16], orbit[16];
    statsblk stats;
    Rows canonical{};
    densenauty(g.data(), lab.data(), part, orbit, &opts, &stats, 1, n, canonical.data());
    return encode(canonical, n);
}
static constexpr int threshold[] = {0, 0, 1, 2, 4, 6, 9, 12, 16, 20, 24, 29, 34, 40, 46, 53, 60};
static bool path(const std::array<U, 16> &nb, int dst, U avail, int cur, int left, uint32_t &code) {
    code |= uint32_t(cur) << (4 * (7 - left));
    if (left == 0)
        return cur == dst;
    U choices = nb[cur] & avail;
    if (left == 1)
        choices &= 1u << dst;
    else
        choices &= ~(1u << dst);
    auto prefix = code;
    while (choices) {
        int next = __builtin_ctz(choices);
        choices &= choices - 1;
        code = prefix;
        if (path(nb, dst, avail ^ (1u << next), next, left - 1, code))
            return true;
    }
    code = prefix;
    return false;
}
int main(int argc, char **argv) {
    if (argc != 3) {
        std::cerr << "witnesses GRAPH6DIR OUTPUTDIR\n";
        return 1;
    }
    std::array<std::vector<Rep>, 17> reps;
    std::array<std::map<Wide, int>, 17> canonicalIds;
    for (int n = 1; n <= 16; n++) {
        std::ifstream input(std::string(argv[1]) + "/graphs" + std::to_string(n) + ".g6");
        std::string line;
        while (std::getline(input, line)) {
            if (line.empty() || line[0] != 63 + n)
                abort();
            Rows g{};
            int ix = 0;
            for (int i = 0; i < n; i++)
                for (int j = 0; j < i; j++, ix++)
                    if (!((line[1 + ix / 6] - 63) & (1u << (5 - ix % 6)))) {
                        g[i] |= bit[j];
                        g[j] |= bit[i];
                    }
            Perm lab{};
            Wide key = canon(g, n, lab);
            int idx = reps[n].size();
            if (!canonicalIds[n].emplace(key, idx).second)
                abort();
            reps[n].push_back({g, encode(g, n), lab});
        }
        if (reps[n].empty())
            abort();
    }
    for (int n = 1; n <= 16; n++) {
        std::ofstream out(std::string(argv[2]) + "/witness" + std::to_string(n) + ".txt");
        if (!out)
            abort();
        for (const auto &rep : reps[n]) {
            std::array<U, 16> nb{}, conf{};
            std::vector<uint32_t> paths;
            int count = 0;
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    if (rep.g[i] & bit[j]) {
                        nb[i] |= 1u << j;
                        count++;
                    }
            count /= 2;
            U full = (1u << n) - 1;
            out << number(rep.code) << "\n";
            if (n == 16) {
                U sides = 0;
                for (; sides <= full; sides++) {
                    bool ok = true;
                    for (int i = 0; i < n; i++)
                        if (nb[i] & ((sides & (1u << i)) ? sides : (full ^ sides))) {
                            ok = false;
                            break;
                        }
                    if (ok)
                        break;
                }
                if (sides > full)
                    abort();
                out << sides << "\n";
                continue;
            }
            if (n >= 8)
                for (int i = 0; i < n; i++)
                    for (int j = 0; j < i; j++) {
                        uint32_t code = 0;
                        if (path(nb, j, full ^ (1u << i), i, 7, code)) {
                            paths.push_back(code);
                            conf[i] |= 1u << j;
                            conf[j] |= 1u << i;
                        }
                    }
            for (auto code : paths)
                out << code << " ";
            out << "\n";
            for (U m = 0; m <= full; m++) {
                if (count + __builtin_popcount(m) < threshold[n + 1])
                    continue;
                bool blocked = false;
                for (U s = m; s; s &= s - 1)
                    if (conf[__builtin_ctz(s)] & s) {
                        blocked = true;
                        break;
                    }
                if (blocked)
                    continue;
                Rows g = rep.g;
                for (int i = 0; i < n; i++)
                    if (m & (1u << i)) {
                        g[i] |= bit[n];
                        g[n] |= bit[i];
                    }
                Perm lab{};
                Wide key = canon(g, n + 1, lab);
                auto found = canonicalIds[n + 1].find(key);
                if (found == canonicalIds[n + 1].end()) {
                    std::cerr << "No representative at " << n << "/" << m << "\n";
                    abort();
                }
                int ix = found->second;
                auto &target = reps[n + 1][ix];
                uint64_t perm = 0;
                for (int i = 0; i <= n; i++)
                    perm |= uint64_t(target.lab[i]) << (4 * lab[i]);
                out << m << " " << ix << " " << perm << " ";
            }
            out << "\n";
        }
        std::cerr << "wrote " << n << ": " << reps[n].size() << " graphs\n";
    }
}
