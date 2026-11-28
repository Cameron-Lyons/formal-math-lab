#include <bits/stdc++.h>
using namespace std;

// 1. Exhaustive search over ALL bi-Cayley (2-orbit semiregular) graphs on 40 vertices
//    for ALL 5 groups of order 20: C20, C10xC2, D20, Dic20, F20!
// 2. Fast parallel SA/Tabu search over:
//    - 4-circulants (C_10 on 4 orbits of 10)
//    - 5-circulants (C_8 on 5 orbits of 8)
//    - 8-circulants (C_5 on 8 orbits of 5)
//    - Z_2-symmetric (20 orbits of 2)

static inline int popcnt(uint64_t x) { return __builtin_popcountll(x); }
static inline int ctz(uint64_t x) { return __builtin_ctzll(x); }

struct Graph40 {
    uint64_t adj[40];
    static constexpr uint64_t FULL = (1ULL << 40) - 1;

    uint64_t find_indep_ge(uint64_t P, int k) const {
        if (k <= 0) return 0;
        int sz = popcnt(P);
        if (sz < k) return 0;
        if (k == 1) return (1ULL << ctz(P));
        if (k == 2) {
            uint64_t m = P;
            while (m) {
                int v = ctz(m); m &= m - 1;
                uint64_t non_nb = P & ~(adj[v] | (1ULL << v));
                if (non_nb) return (1ULL << v) | (1ULL << ctz(non_nb));
            }
            return 0;
        }
        uint64_t forced = 0;
        while (true) {
            int best_v = -1, max_deg = -1, deg01 = -1;
            uint64_t m = P;
            while (m) {
                int v = ctz(m); m &= m - 1;
                int d = popcnt(adj[v] & P);
                if (d <= 1) { deg01 = v; break; }
                if (d > max_deg) { max_deg = d; best_v = v; }
            }
            if (deg01 != -1) {
                forced |= (1ULL << deg01);
                P &= ~(adj[deg01] | (1ULL << deg01));
                k--;
                if (k == 0) return forced;
                if (popcnt(P) < k) return 0;
                continue;
            }
            uint64_t sub = find_indep_ge(P & ~(adj[best_v] | (1ULL << best_v)), k - 1);
            if (sub) return forced | (1ULL << best_v) | sub;
            P &= ~(1ULL << best_v);
            if (popcnt(P) < k) return 0;
        }
    }
};

struct Group20 {
    string name;
    int mul[20][20];
    int inv[20];
    bool verify() const {
        for (int a = 0; a < 20; a++) {
            if (mul[0][a] != a || mul[a][0] != a) return false;
            if (mul[a][inv[a]] != 0 || mul[inv[a]][a] != 0) return false;
        }
        for (int a = 0; a < 20; a++)
            for (int b = 0; b < 20; b++)
                for (int c = 0; c < 20; c++)
                    if (mul[mul[a][b]][c] != mul[a][mul[b][c]]) return false;
        return true;
    }
};

// All 5 groups of order 20 are C_5 \rtimes_phi P where P has order 4 (C_4 or C_2 x C_2)
Group20 make_g20(const string& name, const int pmul[4][4], const int phi[4]) {
    Group20 G; G.name = name;
    for (int x = 0; x < 5; x++) for (int p = 0; p < 4; p++)
        for (int y = 0; y < 5; y++) for (int q = 0; q < 4; q++) {
            int z = (x + phi[p] * y) % 5;
            G.mul[x*4 + p][y*4 + q] = z*4 + pmul[p][q];
        }
    for (int a = 0; a < 20; a++)
        for (int b = 0; b < 20; b++)
            if (G.mul[a][b] == 0) { G.inv[a] = b; break; }
    return G;
}

vector<Group20> build_all_5_groups20() {
    int pm_C4[4][4], pm_V4[4][4];
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) {
        pm_C4[i][j] = (i + j) % 4;
        pm_V4[i][j] = i ^ j;
    }
    vector<Group20> gs;
    { int phi[4] = {1,1,1,1}; gs.push_back(make_g20("C20", pm_C4, phi)); }
    { int phi[4] = {1,4,1,4}; gs.push_back(make_g20("Dic20", pm_C4, phi)); }
    { int phi[4] = {1,2,4,3}; gs.push_back(make_g20("F20", pm_C4, phi)); }
    { int phi[4] = {1,1,1,1}; gs.push_back(make_g20("C10xC2", pm_V4, phi)); }
    { int phi[4] = {1,4,1,4}; gs.push_back(make_g20("D20", pm_V4, phi)); }
    return gs;
}

// Exhaustive bi-Cayley search for a group H of order 20:
// Vertices: H_0 (0..19) and H_1 (20..39).
// Left action of H: h acts as (x, i) -> (h*x, i).
// Edges:
//   within H_0: (x, 0) ~ (x*s, 0) for s in S0 (symmetric, 0 not in S0)
//   within H_1: (x, 1) ~ (x*s, 1) for s in S1 (symmetric, 0 not in S1)
//   between H_0 and H_1: (x, 0) ~ (x*t, 1) for t in T subset H (shift T by right-mult so 0 in T!)
// Triangle-free iff:
//   1. S0 * S0 disjoint from S0; S1 * S1 disjoint from S1
//   2. A-A-B triangle: x ~ x*s0 in H_0 and x ~ x*t1, x*s0 ~ x*t1 => s0^{-1}*t1 in T => t1 * t2^{-1} in S0!
//      Wait carefully: (x*s0, 0) ~ (x*s0*t2, 1). Equals (x*t1, 1) iff s0*t2 = t1 iff t1*t2^{-1} = s0 in S0!
//   3. A-B-B triangle: (x, 0) ~ (x*t1, 1) and (x, 0) ~ (x*t2, 1), adjacent in H_1 iff (x*t1)^{-1}*(x*t2) = t1^{-1}*t2 in S1!
//   SO T is an independent set in the graph on H where u ~ v iff (u*v^{-1} in S0) OR (u^{-1}*v in S1)!!
//   (Notice u*v^{-1} in S0 is symmetric because S0 = S0^{-1}; u^{-1}*v in S1 is symmetric because S1 = S1^{-1}!)
//   Also we can relabel H_1 by right-multiplying by t0^{-1} (which conjugates S1 -> t0*S1*t0^{-1} and shifts T -> T*t0^{-1})
//   to assume 0 in T! (Since we iterate over ALL valid S1, conjugation stays within all valid S1!)
void check_bicayley(const Group20& H) {
    // Find all symmetric product-free sets S subset H \ {0} with |S| <= 8
    vector<uint32_t> pairs;
    uint32_t seen = 1U;
    for (int a = 1; a < 20; a++) {
        if ((seen >> a) & 1) continue;
        uint32_t m = (1U << a) | (1U << H.inv[a]);
        seen |= m;
        pairs.push_back(m);
    }
    int P = pairs.size();
    auto is_prod_free = [&](uint32_t S) {
        uint32_t m1 = S;
        while (m1) {
            int a = ctz(m1); m1 &= m1 - 1;
            uint32_t m2 = S;
            while (m2) {
                int b = ctz(m2); m2 &= m2 - 1;
                if ((S >> H.mul[a][b]) & 1) return false;
            }
        }
        return true;
    };
    auto cay20_alpha_ge = [&](uint32_t S, int k) {
        uint32_t adj[20] = {0};
        for (int u = 0; u < 20; u++) {
            uint32_t m = S;
            while (m) { int s = ctz(m); m &= m - 1; adj[u] |= (1U << H.mul[u][s]); }
        }
        function<bool(uint32_t, int)> rec = [&](uint32_t cand, int r) -> bool {
            if (r <= 0) return true;
            if (__builtin_popcount(cand) < r) return false;
            int v = ctz(cand);
            if (rec(cand & ~(adj[v] | (1U << v)), r - 1)) return true;
            return rec(cand & ~(1U << v), r);
        };
        return rec(((1U << 20) - 1) & ~(adj[0] | 1U), k - 1);
    };

    vector<uint32_t> valid_S;
    function<void(int, uint32_t, int)> gen_S = [&](int idx, uint32_t S, int deg) {
        if (!cay20_alpha_ge(S, 10)) valid_S.push_back(S);
        for (int i = idx; i < P; i++) {
            int nd = deg + __builtin_popcount(pairs[i]);
            if (nd > 8) continue;
            uint32_t nS = S | pairs[i];
            if (is_prod_free(nS)) gen_S(i + 1, nS, nd);
        }
    };
    gen_S(0, 0, 0);

    // Wait: compute automorphisms of H to deduplicate (S0, S1) pairs!
    // Even simpler: find all automorphisms of H by checking bijections preserving mul (H is generated by 2 elements: x of ord 5 and p_gen of P).
    // Actually |valid_S| is small! Let's see how many valid_S there are, and also deduplicate (S0, S1) by S0 <= S1 and conjugacy on S1.
    // Wait: swapping H_0 and H_1 swaps S0 <-> S1 and T -> T^{-1}, so wlog S0 <= S1!
    // And for fast deduplication, compute Aut(H) (just check maps of generators: 5 choices for img(x=4) * ... actually < 200 checks!).
    vector<array<int, 20>> auts;
    // Generator set of H: element 4 (= (1,0) of order 5) and elements 1, 2 (in P, indices 0..3)
    // Since element (x, p) = (1,0)^x * (0, p), any hom is determined by f(4) in {4,8,12,16} and f|_P: P -> H!
    // Wait: f(4) must have order 5, so f(4) in {4,8,12,16} (4 choices, since C_5 is characteristic!).
    // For P (4 elements: 0,1,2,3): check all 20*20 images of (1, 2)? For C4, 1 generates P (20 choices!). For V4, 1 and 2 generate P (20*20=400 choices!).
    // Let's just find all auts by checking f(4) in {4,8,12,16}, f(1) in 0..19, f(2) in 0..19 (if V4) or f(2)=f(1)^2 (if C4)!
    bool is_c4 = (H.mul[1][1] == 2);
    for (int f4 : {4, 8, 12, 16}) {
        for (int f1 = 1; f1 < 20; f1++) {
            int f2_lo = is_c4 ? H.mul[f1][f1] : 1;
            int f2_hi = is_c4 ? f2_lo : 19;
            for (int f2 = f2_lo; f2 <= f2_hi; f2++) {
                array<int, 20> f;
                int fp[4] = {0, f1, f2, H.mul[f1][f2]};
                int fx[5] = {0, f4, H.mul[f4][f4], 0, 0};
                fx[3] = H.mul[fx[2]][f4]; fx[4] = H.mul[fx[3]][f4];
                uint32_t used = 0;
                bool bij = true;
                for (int x = 0; x < 5; x++) for (int p = 0; p < 4; p++) {
                    int v = H.mul[fx[x]][fp[p]];
                    f[x*4 + p] = v;
                    if ((used >> v) & 1) bij = false;
                    used |= (1U << v);
                }
                if (!bij) continue;
                bool hom = true;
                for (int a = 0; a < 20 && hom; a++)
                    for (int b = 0; b < 20; b++)
                        if (f[H.mul[a][b]] != H.mul[f[a]][f[b]]) { hom = false; break; }
                if (hom) auts.push_back(f);
            }
        }
    }

    auto apply_aut = [&](uint32_t S, const array<int, 20>& f) {
        uint32_t R = 0;
        while (S) { int a = ctz(S); S &= S - 1; R |= (1U << f[a]); }
        return R;
    };
    auto canon_pair = [&](uint32_t S0, uint32_t S1) {
        pair<uint32_t, uint32_t> best = {min(S0, S1), max(S0, S1)};
        for (auto& f : auts) {
            uint32_t a = apply_aut(S0, f), b = apply_aut(S1, f);
            best = min(best, {min(a, b), max(a, b)});
        }
        return best;
    };

    set<pair<uint32_t, uint32_t>> uniq_pairs;
    for (int i = 0; i < (int)valid_S.size(); i++)
        for (int j = i; j < (int)valid_S.size(); j++)
            uniq_pairs.insert(canon_pair(valid_S[i], valid_S[j]));

    long long tested = 0, hits = 0;
    for (auto [S0, S1] : uniq_pairs) {
        int d0 = __builtin_popcount(S0), d1 = __builtin_popcount(S1);
        int max_t = 9 - max(d0, d1);
        int min_t = max(1, 5 - min(d0, d1)); // Note: we already proved delta >= 5 (no deg 4)! Still let's use 4 to be completely unconditional!
        min_t = max(1, 4 - min(d0, d1));
        if (min_t > max_t) continue;

        uint32_t adjT[20] = {0};
        for (int u = 0; u < 20; u++) {
            for (int v = 0; v < 20; v++) {
                if (u == v) continue;
                if (((S0 >> H.mul[u][H.inv[v]]) & 1) || ((S1 >> H.mul[H.inv[u]][v]) & 1)) {
                    adjT[u] |= (1U << v);
                }
            }
        }

        uint32_t initP = ((1U << 20) - 1) & ~(adjT[0] | 1U);
        function<void(uint32_t, uint32_t, uint32_t, int)> dfs_t = [&](uint32_t cur, uint32_t cand, uint32_t skipped, int sz) {
            if (sz == max_t || cand == 0) {
                if (sz >= min_t) {
                    if (sz < max_t) {
                        uint32_t m = skipped;
                        while (m) {
                            int v = ctz(m); m &= m - 1;
                            if ((adjT[v] & cur) == 0) return;
                        }
                    }
                    // Build 40-vertex graph
                    Graph40 gr;
                    for (int u = 0; u < 20; u++) {
                        uint64_t nb0 = 0, nb1 = 0;
                        uint32_t m = S0;
                        while (m) { int s = ctz(m); m &= m - 1; nb0 |= (1ULL << H.mul[u][s]); }
                        m = S1;
                        while (m) { int s = ctz(m); m &= m - 1; nb1 |= (1ULL << (20 + H.mul[u][s])); }
                        m = cur;
                        while (m) {
                            int t = ctz(m); m &= m - 1;
                            nb0 |= (1ULL << (20 + H.mul[u][t]));
                            nb1 |= (1ULL << H.mul[u][H.inv[t]]);
                        }
                        gr.adj[u] = nb0;
                        gr.adj[20 + u] = nb1;
                    }
                    tested++;
                    // Since alpha(H_1) < 10, every 10-IS hits H_0; by H-symmetry wlog vertex 0 is in it!
                    uint64_t rem = Graph40::FULL & ~(gr.adj[0] | 1ULL);
                    if (gr.find_indep_ge(rem, 9) == 0) {
                        hits++;
                        cout << "!!! JACKPOT BI-CAYLEY R(3,10,40) in " << H.name
                             << " S0=" << S0 << " S1=" << S1 << " T=" << cur << endl;
                    }
                }
                return;
            }
            int v = ctz(cand);
            uint32_t rest = cand & ~(1U << v);
            dfs_t(cur | (1U << v), rest & ~adjT[v], skipped & ~adjT[v], sz + 1);
            dfs_t(cur, rest, skipped | (1U << v), sz);
        };
        dfs_t(1U, initP, 0U, 1);
    }
    cout << setw(8) << left << H.name
         << " | |Aut|=" << setw(3) << auts.size()
         << " | valid_S=" << setw(4) << valid_S.size()
         << " | uniq_pairs=" << setw(6) << uniq_pairs.size()
         << " | max_biCayley_tested=" << setw(8) << tested
         << " | hits=" << hits << "\n" << flush;
}

int main() {
    auto gs = build_all_5_groups20();
    cout << "=== Exhaustive Bi-Cayley (2-Orbit) Search over ALL 5 Groups of Order 20 ===\n";
    for (auto& H : gs) {
        if (!H.verify()) { cerr << "Group20 axiom fail " << H.name << "\n"; return 1; }
        check_bicayley(H);
    }
    return 0;
}
