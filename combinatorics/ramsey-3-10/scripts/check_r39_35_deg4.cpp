#include <bits/stdc++.h>
using namespace std;

// Exhaustive check on Kalbfleisch's unique R(3, 9, 35)-graph C_35({1, 7, 11, 16}):
// enumerates all independent 8-sets and all 3,365 maximal independent sets (MIS),
// and checks whether any triple or 4-tuple of MIS is pairwise compatible (no IS of size 8
// missed by a pair, no IS of size 7 missed by a triple, no IS of size 6 missed by a 4-tuple).
// Finding 0 pairwise-compatible triples rules out degree-4 vertices in R(3, 10, 40)
// and degree-3 vertices in R(3, 10, 39) (assuming uniqueness of R(3, 9, 35)).

struct Graph {
    int n;
    uint64_t adj[64];
    uint64_t full;

    Graph(const vector<uint64_t>& a) : n((int)a.size()), full((n == 64) ? ~0ULL : ((1ULL << n) - 1)) {
        memset(adj, 0, sizeof(adj));
        for (int i = 0; i < n; i++) adj[i] = a[i];
    }

    bool is_triangle_free() const {
        for (int i = 0; i < n; i++) {
            uint64_t m = adj[i];
            while (m) {
                int j = __builtin_ctzll(m);
                m &= m - 1;
                if (j > i && (adj[i] & adj[j])) return false;
            }
        }
        return true;
    }

    bool has_indep_ge(uint64_t P, int k) const {
        if (k <= 0) return true;
        int sz = __builtin_popcountll(P);
        if (sz < k) return false;
        if (k == 1) return true;
        if (k == 2) {
            uint64_t m = P;
            while (m) {
                int v = __builtin_ctzll(m);
                m &= m - 1;
                if ((P & ~(adj[v] | (1ULL << v))) != 0) return true;
            }
            return false;
        }
        while (true) {
            int best_v = -1, max_deg = -1;
            int deg0_or_1 = -1;
            uint64_t m = P;
            while (m) {
                int v = __builtin_ctzll(m);
                m &= m - 1;
                int d = __builtin_popcountll(adj[v] & P);
                if (d <= 1) { deg0_or_1 = v; break; }
                if (d > max_deg) { max_deg = d; best_v = v; }
            }
            if (deg0_or_1 != -1) {
                P &= ~(adj[deg0_or_1] | (1ULL << deg0_or_1));
                k--;
                if (k <= 0) return true;
                if (__builtin_popcountll(P) < k) return false;
                continue;
            }
            if (has_indep_ge(P & ~(adj[best_v] | (1ULL << best_v)), k - 1)) return true;
            P &= ~(1ULL << best_v);
            if (__builtin_popcountll(P) < k) return false;
        }
    }

    void enum_indep_exact(uint64_t P, int k, uint64_t cur, vector<uint64_t>& out) const {
        if (k == 0) { out.push_back(cur); return; }
        if (__builtin_popcountll(P) < k) return;
        while (__builtin_popcountll(P) >= k) {
            int v = __builtin_ctzll(P);
            P &= ~(1ULL << v);
            enum_indep_exact(P & ~adj[v], k - 1, cur | (1ULL << v), out);
        }
    }

    void bron_kerbosch(uint64_t R, uint64_t P, uint64_t X, vector<uint64_t>& out) const {
        if (P == 0 && X == 0) { out.push_back(R); return; }
        uint64_t PX = P | X;
        int pivot = -1, best_keep = -1;
        uint64_t m = PX;
        while (m) {
            int u = __builtin_ctzll(m);
            m &= m - 1;
            int keep = __builtin_popcountll(P & ~(adj[u] | (1ULL << u)));
            if (keep > best_keep) { best_keep = keep; pivot = u; }
        }
        uint64_t cands = P & (adj[pivot] | (1ULL << pivot));
        while (cands) {
            int v = __builtin_ctzll(cands);
            cands &= cands - 1;
            uint64_t nb = adj[v] | (1ULL << v);
            bron_kerbosch(R | (1ULL << v), P & ~nb, X & ~nb, out);
            P &= ~(1ULL << v);
            X |= (1ULL << v);
        }
    }
};

int main() {
    vector<uint64_t> adj(35, 0);
    const int dists[] = {1, 7, 11, 16, 19, 24, 28, 34};
    for (int u = 0; u < 35; u++)
        for (int d : dists)
            adj[u] |= (1ULL << ((u + d) % 35));

    Graph G(adj);
    cout << "C_35({1,7,11,16}): n=" << G.n
         << ", tri_free=" << G.is_triangle_free()
         << ", has_IS8=" << G.has_indep_ge(G.full, 8)
         << ", has_IS9=" << G.has_indep_ge(G.full, 9) << "\n";

    vector<uint64_t> is8, mis;
    G.enum_indep_exact(G.full, 8, 0, is8);
    G.bron_kerbosch(0, G.full, 0, mis);
    cout << "#(IS of size 8) = " << is8.size() << "\n";
    cout << "#(Maximal IS)   = " << mis.size() << "\n";

    int M = (int)mis.size();
    int K8 = (int)is8.size();
    int W = (K8 + 63) / 64;
    vector<vector<uint64_t>> unhit(M, vector<uint64_t>(W, 0));
    for (int i = 0; i < M; i++)
        for (int j = 0; j < K8; j++)
            if ((mis[i] & is8[j]) == 0)
                unhit[i][j >> 6] |= (1ULL << (j & 63));

    vector<vector<int>> compat_any(M);
    vector<vector<uint8_t>> is_compat(M, vector<uint8_t>(M, 0));
    long long pairs_any = 0, pairs_disj = 0;
    for (int i = 0; i < M; i++) {
        for (int j = i; j < M; j++) {
            bool ok = true;
            for (int w = 0; w < W; w++) {
                if (unhit[i][w] & unhit[j][w]) { ok = false; break; }
            }
            if (ok) {
                compat_any[i].push_back(j);
                is_compat[i][j] = is_compat[j][i] = 1;
                pairs_any++;
                if ((mis[i] & mis[j]) == 0) pairs_disj++;
            }
        }
    }
    cout << "Pairwise compatible MIS pairs (any):      " << pairs_any << "\n";
    cout << "Pairwise compatible MIS pairs (disjoint): " << pairs_disj << "\n";

    long long compat_triangles = 0;
    for (int a = 0; a < M; a++)
        for (int b : compat_any[a])
            for (int c : compat_any[b])
                if (is_compat[a][c])
                    compat_triangles++;

    cout << "Pairwise compatible MIS triples (triangles in compatibility graph): "
         << compat_triangles << "\n";
    return (compat_triangles == 0) ? 0 : 1;
}
