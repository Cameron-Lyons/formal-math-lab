#include <bits/stdc++.h>
using namespace std;

// Exhaustive search over:
// 1. ALL triangle-free Cayley graphs on ALL 14 groups of order 40
// 2. ALL triangle-free bicirculant (C_20-invariant) graphs on 40 vertices

struct Graph40 {
    uint64_t adj[40];
    static constexpr uint64_t FULL = (1ULL << 40) - 1;

    bool is_triangle_free() const {
        for (int i = 0; i < 40; i++) {
            uint64_t m = adj[i];
            while (m) {
                int j = __builtin_ctzll(m);
                m &= m - 1;
                if (j > i && (adj[i] & adj[j])) return false;
            }
        }
        return true;
    }

    // Find an independent set of size >= k, returning its bitmask (or 0 if none exists)
    uint64_t find_indep_ge(uint64_t P, int k) const {
        if (k <= 0) return 0; // handled by caller
        int sz = __builtin_popcountll(P);
        if (sz < k) return 0;
        if (k == 1) return (1ULL << __builtin_ctzll(P));
        if (k == 2) {
            uint64_t m = P;
            while (m) {
                int v = __builtin_ctzll(m);
                m &= m - 1;
                uint64_t non_nb = P & ~(adj[v] | (1ULL << v));
                if (non_nb) return (1ULL << v) | (1ULL << __builtin_ctzll(non_nb));
            }
            return 0;
        }
        uint64_t forced = 0;
        while (true) {
            int best_v = -1, max_deg = -1;
            int deg01 = -1;
            uint64_t m = P;
            while (m) {
                int v = __builtin_ctzll(m);
                m &= m - 1;
                int d = __builtin_popcountll(adj[v] & P);
                if (d <= 1) { deg01 = v; break; }
                if (d > max_deg) { max_deg = d; best_v = v; }
            }
            if (deg01 != -1) {
                forced |= (1ULL << deg01);
                P &= ~(adj[deg01] | (1ULL << deg01));
                k--;
                if (k == 0) return forced;
                if (__builtin_popcountll(P) < k) return 0;
                continue;
            }
            // Branch on best_v: include
            uint64_t sub = find_indep_ge(P & ~(adj[best_v] | (1ULL << best_v)), k - 1);
            if (sub) return forced | (1ULL << best_v) | sub;
            // Exclude best_v
            P &= ~(1ULL << best_v);
            if (__builtin_popcountll(P) < k) return 0;
        }
    }
};

struct Group40 {
    string name;
    int mul[40][40];
    int inv[40];

    bool verify_axioms() const {
        // Identity is 0
        for (int a = 0; a < 40; a++) {
            if (mul[0][a] != a || mul[a][0] != a) return false;
            if (mul[a][inv[a]] != 0 || mul[inv[a]][a] != 0) return false;
        }
        for (int a = 0; a < 40; a++)
            for (int b = 0; b < 40; b++)
                for (int c = 0; c < 40; c++)
                    if (mul[mul[a][b]][c] != mul[a][mul[b][c]]) return false;
        return true;
    }

    string fingerprint() const {
        map<int, int> ord_cnt;
        int center = 0;
        for (int a = 0; a < 40; a++) {
            int cur = a, o = 1;
            while (cur != 0) { cur = mul[cur][a]; o++; }
            ord_cnt[o]++;
            bool cent = true;
            for (int b = 0; b < 40; b++) if (mul[a][b] != mul[b][a]) { cent = false; break; }
            if (cent) center++;
        }
        ostringstream oss;
        oss << "Z=" << center << " ords={";
        for (auto [o, c] : ord_cnt) oss << o << ":" << c << ",";
        oss << "}";
        return oss.str();
    }
};

// Build semidirect product C_5 \rtimes_phi P where P has order 8 (elements 0..7)
// Element index: x * 8 + p  (x in 0..4, p in 0..7)
// Multiplication: (x, p) * (y, q) = ((x + phi[p] * y) % 5, pmul[p][q])
Group40 make_sdp(const string& name, const int pmul[8][8], const int phi[8]) {
    Group40 G;
    G.name = name;
    for (int x = 0; x < 5; x++) {
        for (int p = 0; p < 8; p++) {
            int a = x * 8 + p;
            for (int y = 0; y < 5; y++) {
                for (int q = 0; q < 8; q++) {
                    int b = y * 8 + q;
                    int z = (x + phi[p] * y) % 5;
                    int r = pmul[p][q];
                    G.mul[a][b] = z * 8 + r;
                }
            }
        }
    }
    for (int a = 0; a < 40; a++) {
        for (int b = 0; b < 40; b++) {
            if (G.mul[a][b] == 0) { G.inv[a] = b; break; }
        }
    }
    return G;
}

vector<Group40> build_all_14_groups() {
    int pm_C8[8][8], pm_C4C2[8][8], pm_C2C2C2[8][8], pm_D8[8][8], pm_Q8[8][8];

    // 1. C8: 0..7
    for (int i = 0; i < 8; i++)
        for (int j = 0; j < 8; j++)
            pm_C8[i][j] = (i + j) % 8;

    // 2. C4 x C2: (a, b) -> a + 4*b (a in 0..3, b in 0..1)
    for (int a1 = 0; a1 < 4; a1++) for (int b1 = 0; b1 < 2; b1++)
        for (int a2 = 0; a2 < 4; a2++) for (int b2 = 0; b2 < 2; b2++)
            pm_C4C2[a1 + 4*b1][a2 + 4*b2] = ((a1 + a2) % 4) + 4*((b1 + b2) % 2);

    // 3. C2^3: bitwise xor
    for (int i = 0; i < 8; i++)
        for (int j = 0; j < 8; j++)
            pm_C2C2C2[i][j] = i ^ j;

    // 4. D8: r^a s^b -> a + 4*b (a in 0..3, b in 0..1), s r^a = r^{-a} s
    for (int a1 = 0; a1 < 4; a1++) for (int b1 = 0; b1 < 2; b1++)
        for (int a2 = 0; a2 < 4; a2++) for (int b2 = 0; b2 < 2; b2++) {
            int a = b1 ? (a1 - a2 + 4) % 4 : (a1 + a2) % 4;
            int b = b1 ^ b2;
            pm_D8[a1 + 4*b1][a2 + 4*b2] = a + 4*b;
        }

    // 5. Q8: 0=1, 1=i, 2=-1, 3=-i, 4=j, 5=k, 6=-j, 7=-k
    // Represent as i^a j^b with i^4=1, j^2=i^2, j i = i^3 j
    for (int a1 = 0; a1 < 4; a1++) for (int b1 = 0; b1 < 2; b1++)
        for (int a2 = 0; a2 < 4; a2++) for (int b2 = 0; b2 < 2; b2++) {
            int a = (a1 + (b1 ? (4 - a2) % 4 : a2) + (b1 && b2 ? 2 : 0)) % 4;
            int b = b1 ^ b2;
            pm_Q8[a1 + 4*b1][a2 + 4*b2] = a + 4*b;
        }

    vector<Group40> gs;
    // C8 (3)
    { int phi[8] = {1,1,1,1,1,1,1,1}; gs.push_back(make_sdp("C40", pm_C8, phi)); }
    { int phi[8] = {1,4,1,4,1,4,1,4}; gs.push_back(make_sdp("C5_sdp2_C8", pm_C8, phi)); }
    { int phi[8] = {1,2,4,3,1,2,4,3}; gs.push_back(make_sdp("C5_sdp4_C8", pm_C8, phi)); }

    // C4 x C2 (4)
    { int phi[8] = {1,1,1,1, 1,1,1,1}; gs.push_back(make_sdp("C20xC2", pm_C4C2, phi)); }
    { int phi[8] = {1,1,1,1, 4,4,4,4}; gs.push_back(make_sdp("C4xD10", pm_C4C2, phi)); }
    { int phi[8] = {1,4,1,4, 1,4,1,4}; gs.push_back(make_sdp("C2xDic20", pm_C4C2, phi)); }
    { int phi[8] = {1,2,4,3, 1,2,4,3}; gs.push_back(make_sdp("C2xF20", pm_C4C2, phi)); }

    // C2^3 (2)
    { int phi[8] = {1,1,1,1,1,1,1,1}; gs.push_back(make_sdp("C10xC2xC2", pm_C2C2C2, phi)); }
    { int phi[8] = {1,4,1,4,1,4,1,4}; gs.push_back(make_sdp("C2xC2xD10", pm_C2C2C2, phi)); }

    // D8 (3)
    { int phi[8] = {1,1,1,1, 1,1,1,1}; gs.push_back(make_sdp("C5xD8", pm_D8, phi)); }
    { int phi[8] = {1,1,1,1, 4,4,4,4}; gs.push_back(make_sdp("D40", pm_D8, phi)); }
    { int phi[8] = {1,4,1,4, 1,4,1,4}; gs.push_back(make_sdp("C5_sdp_D8", pm_D8, phi)); }

    // Q8 (2)
    { int phi[8] = {1,1,1,1, 1,1,1,1}; gs.push_back(make_sdp("C5xQ8", pm_Q8, phi)); }
    { int phi[8] = {1,1,1,1, 4,4,4,4}; gs.push_back(make_sdp("Q40", pm_Q8, phi)); }

    return gs;
}

// Exhaustively enumerate ALL maximal triangle-free Cayley graphs for group G with |S| <= 9
// Wait: any triangle-free Cayley graph with |S| <= 9 is a subgraph of a MAXIMAL triangle-free Cayley graph?
// CAREFUL: What if a maximal triangle-free Cayley graph has |S| >= 10?!
// If |S| >= 10, then N(0) = S is ALREADY an independent set of size >= 10, so alpha >= 10!
// WAIT: If S has |S| <= 9 and is NOT maximal as a triangle-free symmetric set, adding more symmetric pairs
// to make it maximal could either keep |S'| <= 9 (and alpha(S') <= alpha(S)) OR push |S'| >= 10!
// So to be 100% EXACT and sound, we simply enumerate ALL symmetric product-free sets S with 5 <= |S| <= 9
// (Wait: and even skip subsets of already-checked sets with |S'| <= 9! Better: enumerate ALL symmetric product-free sets with |S| <= 9 — there are very few!).
void check_cayley_group(const Group40& G) {
    // Partition G \ {0} into inverse pairs {a, inv[a]}
    vector<uint64_t> pairs;
    vector<int> pair_sz;
    uint64_t seen = 1ULL; // skip 0
    for (int a = 1; a < 40; a++) {
        if ((seen >> a) & 1) continue;
        int b = G.inv[a];
        uint64_t mask = (1ULL << a) | (1ULL << b);
        seen |= mask;
        // Skip pair if a == b? Wait: if a^2 = 0 (involution), a * a = 0, not a triangle! (0 is not in S).
        // What if a^3 = 0 (order 3)? Impossible since 3 does not divide 40!
        // Still check if pair itself contains a triangle: a*b in pair? a*a in pair?
        bool self_tri = false;
        vector<int> elems = {a};
        if (b != a) elems.push_back(b);
        for (int x : elems)
            for (int y : elems)
                if ((mask >> G.mul[x][y]) & 1) self_tri = true;
        if (!self_tri) {
            pairs.push_back(mask);
            pair_sz.push_back(__builtin_popcountll(mask));
        }
    }
    int P = pairs.size();
    // Precompute for each pair i and j: what elements are forbidden if we pick both, or actually:
    // S is triangle-free iff for all x, y in S, x*y not in S!
    // In Cayley graphs, edges are (u, u*s) for s in S. Triangle u, u*s1, u*s1*s2 iff s1*s2 in S!
    // Check incrementally when adding pair idx to S!
    // Precompute pair elements
    vector<vector<int>> pelems(P);
    for (int i = 0; i < P; i++) {
        uint64_t m = pairs[i];
        while (m) { int x = __builtin_ctzll(m); m &= m - 1; pelems[i].push_back(x); }
    }

    // Collect all valid S with 4 <= |S| <= 9 (and maximal among |S| <= 9)
    // Wait: we only need to test S that CANNOT be extended by another pair while staying |S| <= 9!
    // Because if S subset S' with |S'| <= 9 and S' is triangle-free, then alpha(S') <= alpha(S).
    // So if alpha(S') >= 10, then alpha(S) >= 10 automatically!
    // Let's count both total valid S (|S|<=9) and maximal-within-|S|<=9!
    long long total_valid = 0, max_checked = 0, hits = 0;
    // Track how many have alpha >= 10 vs alpha <= 9.

    function<void(int, uint64_t, uint64_t, int)> dfs = [&](int idx, uint64_t S, uint64_t forbid, int deg) {
        if (deg >= 4) total_valid++;
        bool extended = false;
        for (int i = idx; i < P; i++) {
            if (deg + pair_sz[i] > 9) continue;
            if (pairs[i] & forbid) continue;
            // Check if pairs[i] * S or S * pairs[i] hits pairs[i] (since S*S is already in forbid,
            // wait: forbid should contain S*S AND S^{-1}*S = S*S!
            // If we add x in pairs[i]: we need x*y not in S (i.e. x not in S*y^{-1} = S*S),
            // AND y*x not in S (x not in y^{-1}*S = S*S),
            // AND x*y not in pairs[i] (for y in S -> S*pairs[i] disjoint from pairs[i], same as x*x' not in S -> x*x' in S? Wait: pairs[i]*pairs[i] disjoint from S!)
            bool ok = true;
            for (int x : pelems[i]) {
                for (int y : pelems[i]) {
                    if ((S >> G.mul[x][y]) & 1) { ok = false; break; }
                }
                if (!ok) break;
            }
            if (!ok) continue;
            extended = true;
            // Compute new forbid = forbid | (S * pairs[i]) | (pairs[i] * S) | (pairs[i] * pairs[i])
            uint64_t nforbid = forbid;
            uint64_t m = S;
            while (m) {
                int s = __builtin_ctzll(m);
                m &= m - 1;
                for (int x : pelems[i]) {
                    nforbid |= (1ULL << G.mul[s][x]);
                    nforbid |= (1ULL << G.mul[x][s]);
                }
            }
            for (int x : pelems[i])
                for (int y : pelems[i])
                    nforbid |= (1ULL << G.mul[x][y]);
            dfs(i + 1, S | pairs[i], nforbid, deg + pair_sz[i]);
        }
        // Check if S can be extended by ANY earlier pair < idx (to see if S is truly maximal within deg <= 9)
        if (!extended && deg >= 4) {
            bool can_ext_earlier = false;
            for (int i = 0; i < idx; i++) {
                if (pairs[i] & S) continue;
                if (deg + pair_sz[i] > 9) continue;
                if (pairs[i] & forbid) continue;
                bool ok = true;
                for (int x : pelems[i])
                    for (int y : pelems[i])
                        if ((S >> G.mul[x][y]) & 1) { ok = false; break; }
                if (ok) { can_ext_earlier = true; break; }
            }
            if (!can_ext_earlier) {
                max_checked++;
                Graph40 gr;
                for (int u = 0; u < 40; u++) {
                    uint64_t nb = 0;
                    uint64_t m = S;
                    while (m) {
                        int s = __builtin_ctzll(m);
                        m &= m - 1;
                        nb |= (1ULL << G.mul[u][s]);
                    }
                    gr.adj[u] = nb;
                }
                // Vertex-transitive: 0 is in SOME max IS! So we can fix 0 in the IS and search for size 9 in V \ N[0]!
                uint64_t rem = Graph40::FULL & ~(gr.adj[0] | 1ULL);
                uint64_t witness = gr.find_indep_ge(rem, 9);
                if (witness == 0) {
                    hits++;
                    cout << "!!! JACKPOT R(3,10,40) FOUND in " << G.name << " !!! S_mask=" << S << " deg=" << deg << endl;
                }
            }
        }
    };

    dfs(0, 0, 0, 0);
    cout << setw(12) << left << G.name
         << " | pairs=" << setw(2) << P
         << " | valid_4..9=" << setw(7) << total_valid
         << " | max_checked=" << setw(6) << max_checked
         << " | R(3,10,40)_hits=" << hits
         << " | " << G.fingerprint() << "\n";
}

// Also check ALL bicirculant graphs on 40 vertices (2 orbits of C_20: 0..19 and 20..39)
// Edges:
//   within A (0..19): circulant diff set S_A subset {1..19}, symmetric, tri-free
//   within B (20..39): circulant diff set S_B subset {1..19}, symmetric, tri-free
//   between A and B: i in A adjacent to 20 + ((i + d) % 20) for d in S_AB subset {0..19}
// Triangle-free iff:
//   1. S_A is sum-free mod 20 (no x,y in S_A with (x+y)%20 in S_A)
//   2. S_B is sum-free mod 20
//   3. For all d1, d2 in S_AB: (d1 - d2) mod 20 NOT in S_A and NOT in S_B!
//      (Wait: A-A-B triangle: i in A, i+a in A, i+d1 in B adjacent to i+a iff d1-a in S_AB -> d1-d2 = a in S_A!
//       B-B-A triangle: i in A, i+d1 in B, i+d2 in B adjacent iff d1-d2 in S_B!)
//   SO S_AB MUST BE AN INDEPENDENT SET IN THE CIRCULANT GRAPH C_20(S_A U S_B)!!
// Degree constraints:
//   deg(A) = |S_A| + |S_AB| in [4, 9]
//   deg(B) = |S_B| + |S_AB| in [4, 9]
//   By symmetry swap A <-> B: |S_A| <= |S_B| (or S_A <= S_B lex).
//   Also we can shift S_AB so that 0 in S_AB (if S_AB non-empty; if S_AB empty, disconnected -> alpha = alpha(A)+alpha(B) >= 6+6 = 12 > 9!).
void check_bicirculants_40() {
    cout << "\n=== Exhaustive Bicirculant (C_20-invariant) Search on 40 vertices ===\n";
    // Enumerate all symmetric sum-free subsets S of Z_20 \ {0} with |S| <= 8
    // Pairs in Z_20 \ {0}: {1,19}, {2,18}, ..., {9,11}, {10} (10 pairs)
    vector<uint32_t> pairs;
    for (int d = 1; d <= 9; d++) pairs.push_back((1U << d) | (1U << (20 - d)));
    pairs.push_back(1U << 10);

    auto is_sum_free = [](uint32_t S) {
        for (int a = 1; a < 20; a++) if ((S >> a) & 1)
            for (int b = a; b < 20; b++) if ((S >> b) & 1)
                if ((S >> ((a + b) % 20)) & 1) return false;
        return true;
    };

    vector<uint32_t> valid_S;
    for (int mask = 0; mask < (1 << 10); mask++) {
        uint32_t S = 0;
        for (int i = 0; i < 10; i++) if ((mask >> i) & 1) S |= pairs[i];
        if (__builtin_popcount(S) <= 8 && is_sum_free(S)) valid_S.push_back(S);
    }
    cout << "Valid sum-free symmetric sets in Z_20 (|S|<=8): " << valid_S.size() << "\n";

    // Filter valid_S up to Z_20^* automorphism? Better: keep all valid_S for S_B, only canonical for S_A!
    // Units mod 20: {1, 3, 7, 9, 11, 13, 17, 19}
    int units[8] = {1, 3, 7, 9, 11, 13, 17, 19};
    auto apply_unit = [&](uint32_t S, int u) {
        uint32_t R = 0;
        for (int d = 1; d < 20; d++) if ((S >> d) & 1) R |= (1U << ((d * u) % 20));
        return R;
    };
    auto canon_pair = [&](uint32_t SA, uint32_t SB) {
        pair<uint32_t, uint32_t> best = {min(SA, SB), max(SA, SB)};
        for (int u : units) {
            uint32_t a = apply_unit(SA, u), b = apply_unit(SB, u);
            best = min(best, {min(a, b), max(a, b)});
        }
        return best;
    };

    set<pair<uint32_t, uint32_t>> uniq_pairs;
    for (uint32_t SA : valid_S)
        for (uint32_t SB : valid_S)
            uniq_pairs.insert(canon_pair(SA, SB));

    cout << "Unique (S_A, S_B) pairs up to swap & Z_20^*: " << uniq_pairs.size() << "\n";

    long long total_bicirc = 0, tested_bicirc = 0, hits = 0;
    // For each (SA, SB), find all maximal-within-deg<=9 independent sets S_AB in C_20(SA | SB) containing 0!
    // Wait: what if alpha(C_20(SA)) >= 10 or alpha(C_20(SB)) >= 10? Immediate skip!
    auto circ20_alpha_ge = [](uint32_t S, int k) {
        uint32_t adj[20] = {0};
        for (int i = 0; i < 20; i++)
            for (int d = 1; d < 20; d++)
                if ((S >> d) & 1) adj[i] |= (1U << ((i + d) % 20));
        // 0 in IS
        function<bool(uint32_t, int)> rec = [&](uint32_t P, int r) -> bool {
            if (r <= 0) return true;
            if (__builtin_popcount(P) < r) return false;
            int v = __builtin_ctz(P);
            if (rec(P & ~(adj[v] | (1U << v)), r - 1)) return true;
            return rec(P & ~(1U << v), r);
        };
        return rec(((1U << 20) - 1) & ~(adj[0] | 1U), k - 1);
    };

    int skipped_ab = 0;
    for (auto [SA, SB] : uniq_pairs) {
        if (circ20_alpha_ge(SA, 10) || circ20_alpha_ge(SB, 10)) { skipped_ab++; continue; }
        int dA = __builtin_popcount(SA), dB = __builtin_popcount(SB);
        int max_ab = 9 - max(dA, dB);
        int min_ab = max(1, 5 - min(dA, dB)); // deg >= 5 (or >= 4; let's use 4 to be completely unconditional!)
        min_ab = max(1, 4 - min(dA, dB));
        if (min_ab > max_ab) continue;

        uint32_t U = SA | SB;
        uint32_t adjU[20] = {0};
        for (int i = 0; i < 20; i++)
            for (int d = 1; d < 20; d++)
                if ((U >> d) & 1) adjU[i] |= (1U << ((i + d) % 20));

        // Enumerate independent sets in C_20(U) containing 0 of size in [min_ab, max_ab]
        // Only check those maximal within size <= max_ab (no vertex can be added while keeping size <= max_ab)
        uint32_t initP = ((1U << 20) - 1) & ~(adjU[0] | 1U);
        function<void(uint32_t, uint32_t, uint32_t, int)> dfs_ab = [&](uint32_t cur, uint32_t cand, uint32_t skipped, int sz) {
            if (sz == max_ab || cand == 0) {
                if (sz >= min_ab) {
                    // Check if any skipped vertex could still be added (if sz < max_ab)
                    if (sz < max_ab) {
                        uint32_t m = skipped;
                        while (m) {
                            int v = __builtin_ctz(m);
                            m &= m - 1;
                            if ((adjU[v] & cur) == 0) return; // not maximal within max_ab
                        }
                    }
                    total_bicirc++;
                    // Build 40-vertex graph
                    Graph40 gr;
                    for (int i = 0; i < 20; i++) {
                        uint64_t nbA = 0, nbB = 0;
                        for (int d = 1; d < 20; d++) {
                            if ((SA >> d) & 1) nbA |= (1ULL << ((i + d) % 20));
                            if ((SB >> d) & 1) nbB |= (1ULL << (20 + ((i + d) % 20)));
                        }
                        for (int d = 0; d < 20; d++) {
                            if ((cur >> d) & 1) {
                                nbA |= (1ULL << (20 + ((i + d) % 20)));
                                nbB |= (1ULL << ((i - d + 20) % 20));
                            }
                        }
                        gr.adj[i] = nbA;
                        gr.adj[20 + i] = nbB;
                    }
                    tested_bicirc++;
                    // Check if alpha(gr) >= 10!
                    // Note: every IS of size 10 has either some vertex in A (by C_20 symmetry, wlog 0 in IS!)
                    // OR lies entirely in B (already ruled out since alpha(B) < 10!).
                    // WAIT A SECOND! THAT'S 100% EXACT!
                    // Since alpha(B) <= 9, ANY independent 10-set MUST contain at least one vertex in A!
                    // By C_20 symmetry, we can assume vertex 0 is in the independent 10-set!
                    uint64_t rem = Graph40::FULL & ~(gr.adj[0] | 1ULL);
                    if (gr.find_indep_ge(rem, 9) == 0) {
                        hits++;
                        cout << "!!! JACKPOT BICIRCULANT R(3,10,40) FOUND !!! SA=" << SA
                             << " SB=" << SB << " SAB=" << cur << endl;
                    }
                }
                return;
            }
            int v = __builtin_ctz(cand);
            uint32_t rest = cand & ~(1U << v);
            // Include v
            dfs_ab(cur | (1U << v), rest & ~adjU[v], skipped & ~adjU[v], sz + 1);
            // Exclude v
            dfs_ab(cur, rest, skipped | (1U << v), sz);
        };
        dfs_ab(1U, initP, 0U, 1);
    }
    cout << "Skipped (alpha(A) or alpha(B) >= 10): " << skipped_ab
         << " | maximal bicirculants tested: " << tested_bicirc
         << " | R(3,10,40) hits: " << hits << "\n";
}

int main() {
    auto gs = build_all_14_groups();
    cout << "=== Verifying all " << gs.size() << " groups of order 40 ===\n";
    for (auto& G : gs) {
        if (!G.verify_axioms()) {
            cerr << "GROUP AXIOM FAILURE for " << G.name << "!\n";
            return 1;
        }
    }
    cout << "All 14 groups passed associativity/identity/inverse axioms!\n\n";
    cout << "=== Exhaustive Cayley Graph Search over ALL 14 Groups of Order 40 ===\n";
    for (auto& G : gs) {
        check_cayley_group(G);
    }
    check_bicirculants_40();
    return 0;
}
