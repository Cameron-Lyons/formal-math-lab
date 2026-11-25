#!/usr/bin/env python3
"""Find a dominating set of n/2 + 1 queens on the n x n board (n even; written for n = 48, where it gives
gamma(Q_48) <= 25) of the classical shape used by find_plus1.py: one queen in every odd-indexed column and
every odd-indexed row (a permutation on the n/2 odd lines) plus one further queen.
Self-contained: no python-sat, no numpy.  Two search methods:

  --method sa   (default)  simulated annealing on the permutation (swap two queens) and on the extra queen,
                which is kept on an even column and an even row.  Pure Python; with --cc the same algorithm
                (same random numbers, same trajectory, so the same answer for the same seed) is run by a
                small C program embedded below and compiled with `cc` into --work, about 40x faster.
  --method sat  the CNF of find_plus1.py, written here in DIMACS and solved by the CaDiCaL binary
                tools/cadical (exit code 10 = SAT, model on the "v" lines).  Far slower at n = 48.

Nothing about the search needs to be trusted: the result is checked by geom.dominated AND by a second
from-scratch test (check_direct below, which marks the squares attacked queen by queen along the 8 rays).

usage:  find_q48.py [n] [--method sa|sat] [--cc] [--indep] [--extra X Y] [--seed S] [--work DIR] [--out FILE.json]
                    [--iters N] [--t0 T] [--t1 T] [--pw P] [--max-cpu SEC]          (sa)
                    [--config sat|default|unsat] [--timeout SEC] [--keep]           (sat)
  --indep       additionally ask for an INDEPENDENT set: the extra queen is on an even column and an even
                row, and no difference diagonal and no sum diagonal holds two queens
  --extra X Y   fix the position of the extra queen (sa: X and Y even)
  --out FILE    also write the result in the style of data/frame/q46_24.json

Why only the even/even squares matter.  Squares are (x, y) = (column, row); difference diagonal t = y - x,
sum diagonal s = x + y.  The permutation occupies every odd column and every odd row, so a square with an
odd coordinate is dominated.  A square (2a, 2b) is dominated iff a permutation queen (2i+1, 2j+1) has
j - i = b - a or i + j + 1 = a + b, or the extra queen (2a0, 2b0) has a = a0, b = b0, b - a = b0 - a0 or
a + b = a0 + b0.  The annealer minimises the number of even/even squares for which none of this holds
(+ pw * number of diagonal clashes with --indep); cost 0 is a dominating (independent) set.

SAT encoding:
  p[x,y]   x, y odd      queen of the permutation at (x, y); exactly one per odd column and per odd row
  EC[x], ER[y]           column / row of the extra queen; exactly one each (the queen is read off these)
  e[x,y]                 e[x,y] -> EC[x] and e[x,y] -> ER[y]   (so e[x,y] true => the extra queen is at (x,y))
  T[t], S[s]  t, s even  T[t] -> some p or e on the difference diagonal t;  S[s] likewise for the sum diagonal
  for all x, y even:     T[y-x] or S[x+y] or ER[y] or EC[x]
With --indep also (EC[x] and ER[y]) -> e[x,y], and at-most-one over the p and e on every diagonal."""

import argparse
import contextlib
import json
import math
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
CADICAL = os.path.normpath(os.path.join(HERE, "..", "..", "tools", "cadical"))
M64 = 0xFFFFFFFFFFFFFFFF


# ------------------------------------------------------------------------------------------------ annealing
def anneal_py(
    m,
    seed,
    iters_per=16000000,
    T0=1.2,
    T1=0.12,
    indep=False,
    pw=1,
    fixed=None,
    max_cpu=None,
):
    """Half-board coordinates: permutation queen i -> (2i+1, 2 perm[i]+1), extra queen (2 a0, 2 b0).
    Geometric cooling T0 -> T1 over iters_per moves, then restart from a random permutation.
    -> (a0, b0, perm, restarts, moves) or None when max_cpu seconds are used up.
    Bit sets: missD = differences d + m - 1 held by no queen; sblk = blocks (W bits per sum) of the sums held
    by no queen; K(a0, b0) = the even/even squares the extra queen does not dominate, bit d + m - 1 of block s."""
    W = 2 * m - 1
    m1 = m - 1
    rs = (seed * 0x9E3779B97F4A7C15 + 0x1234567) & M64

    def rnd():  # xorshift64
        nonlocal rs
        rs ^= (rs << 13) & M64
        rs ^= rs >> 7
        rs ^= (rs << 17) & M64
        return rs

    for _ in range(20):
        rnd()
    cell = [0] * (2 * m)
    for a in range(m):
        for b in range(m):
            cell[a + b] |= 1 << (b - a + m1)
    REP = sum(1 << (W * s) for s in range(2 * m))
    BLK = [((1 << W) - 1) << (W * s) for s in range(2 * m)]
    Kcache = {}

    def K(a0, b0):
        k = Kcache.get((a0, b0))
        if k is None:
            k = 0
            for s in range(2 * m - 1):
                if s == a0 + b0:
                    continue
                mk = cell[s] & ~(1 << (b0 - a0 + m1))
                for kk in (
                    s - 2 * a0 + m1,
                    2 * b0 - s + m1,
                ):  # the square of this sum in column a0 / row b0
                    if 0 <= kk <= 2 * m - 2:
                        mk &= ~(1 << kk)
                k |= mk << (W * s)
            Kcache[(a0, b0)] = k
        return k

    t_start = time.process_time()
    restarts = 0
    moves = 0
    ratio = T1 / T0
    exp = math.exp
    pw_ = pw if indep else 0
    a0, b0 = fixed or (0, 0)
    while True:
        restarts += 1
        perm = list(range(m))
        for i in range(m - 1, 0, -1):
            j = rnd() % (i + 1)
            perm[i], perm[j] = perm[j], perm[i]
        cntD = [0] * (2 * m)
        cntS = [0] * (2 * m + 1)
        missD = (1 << W) - 1
        sblk = (1 << (W * 2 * m)) - 1
        pen = 0
        for i in range(m):
            d = perm[i] - i + m1
            s = i + perm[i] + 1
            if cntD[d]:
                pen += 1
            else:
                missD ^= 1 << d
            cntD[d] += 1
            if cntS[s]:
                pen += 1
            else:
                sblk ^= BLK[s]
            cntS[s] += 1
        if not fixed:
            a0 = rnd() % m
            b0 = rnd() % m
        Kc = K(a0, b0)
        d0 = b0 - a0 + m1
        s0 = a0 + b0
        cur = (Kc & (missD * REP) & sblk).bit_count()
        if pw_:
            cur += pw_ * (pen + (1 if cntD[d0] else 0) + (1 if cntS[s0] else 0))
        for it in range(iters_per):
            T = T0 * math.pow(ratio, it / iters_per)
            if (
                not it & 0xFFFFF
                and max_cpu is not None
                and time.process_time() - t_start > max_cpu
            ):
                return None
            moves += 1
            if not fixed and rnd() % 16 == 0:  # move the extra queen
                oa, ob = a0, b0
                if rnd() & 1:
                    a0 = rnd() % m
                    b0 = rnd() % m
                else:
                    a0 = (a0 + rnd() % 3 - 1 + m) % m
                    b0 = (b0 + rnd() % 3 - 1 + m) % m
                Kn = K(a0, b0)
                d0 = b0 - a0 + m1
                s0 = a0 + b0
                nc = (Kn & (missD * REP) & sblk).bit_count()
                if pw_:
                    nc += pw_ * (pen + (1 if cntD[d0] else 0) + (1 if cntS[s0] else 0))
                if nc <= cur or (rnd() >> 11) * (1.0 / 9007199254740992.0) < exp(
                    (cur - nc) / T
                ):
                    cur = nc
                    Kc = Kn
                else:
                    a0, b0 = oa, ob
                    d0 = b0 - a0 + m1
                    s0 = a0 + b0
            else:  # swap the rows of two permutation queens
                i = rnd() % m
                j = rnd() % m1
                if j >= i:
                    j += 1
                pi = perm[i]
                pj = perm[j]
                doi = pi - i + m1
                doj = pj - j + m1
                dni = pj - i + m1
                dnj = pi - j + m1
                soi = i + pi + 1
                soj = j + pj + 1
                sni = i + pj + 1
                snj = j + pi + 1
                o_missD = missD
                o_sblk = sblk
                o_pen = pen
                c = cntD[doi] - 1
                cntD[doi] = c
                if c:
                    pen -= 1
                else:
                    missD ^= 1 << doi
                c = cntD[doj] - 1
                cntD[doj] = c
                if c:
                    pen -= 1
                else:
                    missD ^= 1 << doj
                c = cntD[dni]
                cntD[dni] = c + 1
                if c:
                    pen += 1
                else:
                    missD ^= 1 << dni
                c = cntD[dnj]
                cntD[dnj] = c + 1
                if c:
                    pen += 1
                else:
                    missD ^= 1 << dnj
                c = cntS[soi] - 1
                cntS[soi] = c
                if c:
                    pen -= 1
                else:
                    sblk ^= BLK[soi]
                c = cntS[soj] - 1
                cntS[soj] = c
                if c:
                    pen -= 1
                else:
                    sblk ^= BLK[soj]
                c = cntS[sni]
                cntS[sni] = c + 1
                if c:
                    pen += 1
                else:
                    sblk ^= BLK[sni]
                c = cntS[snj]
                cntS[snj] = c + 1
                if c:
                    pen += 1
                else:
                    sblk ^= BLK[snj]
                nc = (Kc & (missD * REP) & sblk).bit_count()
                if pw_:
                    nc += pw_ * (pen + (1 if cntD[d0] else 0) + (1 if cntS[s0] else 0))
                if nc <= cur or (rnd() >> 11) * (1.0 / 9007199254740992.0) < exp(
                    (cur - nc) / T
                ):
                    cur = nc
                    perm[i] = pj
                    perm[j] = pi
                else:
                    cntD[dni] -= 1
                    cntD[dnj] -= 1
                    cntD[doi] += 1
                    cntD[doj] += 1
                    cntS[sni] -= 1
                    cntS[snj] -= 1
                    cntS[soi] += 1
                    cntS[soj] += 1
                    missD = o_missD
                    sblk = o_sblk
                    pen = o_pen
            if cur == 0:
                return a0, b0, perm, restarts, moves


# The same algorithm in C (same xorshift64 stream, same floating-point expressions), used with --cc.
C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
static int m, perm[64], cntD[128], cntS[130], a0, b0, indep, pw;
static uint64_t cellmask[128], rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int cost(void) {
    uint64_t missD = 0; int c = 0, pen = 0;
    for (int d = 0; d <= 2 * m - 2; d++) { if (!cntD[d]) missD |= 1ULL << d; else pen += cntD[d] - 1; }
    int d0 = b0 - a0 + m - 1, s0 = a0 + b0;
    if (cntD[d0]) pen++;
    missD &= ~(1ULL << d0);
    for (int s = 0; s <= 2 * m - 2; s++) {
        if (cntS[s] || s == s0) continue;
        uint64_t mk = cellmask[s] & missD;
        int k = s - 2 * a0 + m - 1; if (k >= 0 && k <= 2 * m - 2) mk &= ~(1ULL << k);
        k = 2 * b0 - s + m - 1; if (k >= 0 && k <= 2 * m - 2) mk &= ~(1ULL << k);
        c += __builtin_popcountll(mk);
    }
    if (indep) {
        for (int s = 1; s <= 2 * m - 1; s++) if (cntS[s] > 1) pen += cntS[s] - 1;
        if (cntS[s0]) pen++;
        c += pw * pen;
    }
    return c;
}
static inline void put(int i, int v) { cntD[perm[i] - i + m - 1] += v; cntS[i + perm[i] + 1] += v; }
/* args: m seed iters_per T0 T1 indep pw max_cpu(<0: none) fixed a0 b0 */
int main(int argc, char **argv) {
    if (argc != 12) return 2;
    m = atoi(argv[1]); uint64_t seed = strtoull(argv[2], 0, 10); long iters_per = atol(argv[3]);
    double T0 = atof(argv[4]), T1 = atof(argv[5]); indep = atoi(argv[6]); pw = atoi(argv[7]);
    double max_cpu = atof(argv[8]); int fixed = atoi(argv[9]); a0 = atoi(argv[10]); b0 = atoi(argv[11]);
    if (m < 2 || m > 32) return 2;
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL; for (int i = 0; i < 20; i++) rnd();
    for (int a = 0; a < m; a++) for (int b = 0; b < m; b++) cellmask[a + b] |= 1ULL << (b - a + m - 1);
    double t0 = (double)clock() / CLOCKS_PER_SEC, ratio = T1 / T0; long restarts = 0, moves = 0;
    for (;;) {
        restarts++;
        for (int i = 0; i < m; i++) perm[i] = i;
        for (int i = m - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
        memset(cntD, 0, sizeof cntD); memset(cntS, 0, sizeof cntS);
        for (int i = 0; i < m; i++) put(i, 1);
        if (!fixed) { a0 = rnd() % m; b0 = rnd() % m; }
        int cur = cost();
        for (long it = 0; it < iters_per; it++) {
            double T = T0 * pow(ratio, (double)it / (double)iters_per);
            if ((it & 0xfffff) == 0 && max_cpu >= 0 && (double)clock() / CLOCKS_PER_SEC - t0 > max_cpu) { printf("TIMEOUT\n"); return 1; }
            int nc; moves++;
            if (!fixed && (rnd() % 16) == 0) {
                int oa = a0, ob = b0;
                if (rnd() & 1) { a0 = rnd() % m; b0 = rnd() % m; }
                else { a0 = (a0 + (int)(rnd() % 3) - 1 + m) % m; b0 = (b0 + (int)(rnd() % 3) - 1 + m) % m; }
                nc = cost();
                if (nc <= cur || urand() < exp((cur - nc) / T)) cur = nc; else { a0 = oa; b0 = ob; }
            } else {
                int i = rnd() % m, j = rnd() % (m - 1); if (j >= i) j++;
                put(i, -1); put(j, -1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; put(i, 1); put(j, 1);
                nc = cost();
                if (nc <= cur || urand() < exp((cur - nc) / T)) cur = nc;
                else { put(i, -1); put(j, -1); t = perm[i]; perm[i] = perm[j]; perm[j] = t; put(i, 1); put(j, 1); }
            }
            if (cur == 0) {
                printf("SOL %d %d %ld %ld", a0, b0, restarts, moves);
                for (int k = 0; k < m; k++) printf(" %d", perm[k]);
                printf("\n"); return 0;
            }
        }
    }
}
"""


def anneal_c(
    work,
    m,
    seed,
    iters_per=16000000,
    T0=1.2,
    T1=0.12,
    indep=False,
    pw=1,
    fixed=None,
    max_cpu=None,
):
    """compile C_SOURCE into `work` and run it; same result as anneal_py"""
    src = os.path.join(work, "find_q48_sa.c")
    exe = os.path.join(work, "find_q48_sa")
    with open(src, "w") as f:
        f.write(C_SOURCE)
    subprocess.run(
        [
            "cc",
            "-std=c23",
            "-O2",
            "-Wall",
            "-Wextra",
            "-Wpedantic",
            "-Werror",
            "-o",
            exe,
            src,
            "-lm",
        ],
        check=True,
    )
    a0, b0 = fixed or (0, 0)
    out = subprocess.run(
        [
            exe,
            str(m),
            str(seed),
            str(iters_per),
            repr(T0),
            repr(T1),
            str(int(indep)),
            str(pw),
            repr(float(max_cpu)) if max_cpu is not None else "-1",
            str(int(bool(fixed))),
            str(a0),
            str(b0),
        ],
        stdout=subprocess.PIPE,
        text=True,
        check=False,
    ).stdout.split()
    if not out or out[0] != "SOL":
        return None
    v = list(map(int, out[1:]))
    return v[0], v[1], v[4:], v[2], v[3]


# ------------------------------------------------------------------------------------------------------ SAT
def encode(n, extra=None, indep=False):
    """-> (number of variables, list of clauses, p, EC, ER)"""
    assert n % 2 == 0
    odd = list(range(1, n, 2))
    even = list(range(0, n, 2))
    nv = [0]

    def new():
        nv[0] += 1
        return nv[0]

    cls = []

    def at_most_one(lits):
        cls.extend(
            [-lits[i], -lits[j]]
            for i in range(len(lits))
            for j in range(i + 1, len(lits))
        )

    def exactly_one(lits):
        cls.append(list(lits))
        at_most_one(lits)

    p = {(x, y): new() for x in odd for y in odd}
    excols = (
        even if indep else list(range(n))
    )  # an independent extra queen needs an empty column and row
    EC = {x: new() for x in excols}
    ER = {y: new() for y in excols}
    e = {(x, y): new() for x in excols for y in excols}
    T = {t: new() for t in range(2 - n, n, 2)}
    S = {s: new() for s in range(0, 2 * n - 1, 2)}
    for x in odd:
        exactly_one([p[(x, y)] for y in odd])
    for y in odd:
        exactly_one([p[(x, y)] for x in odd])
    exactly_one(list(EC.values()))
    exactly_one(list(ER.values()))
    for (x, y), v in e.items():
        cls.append([-v, EC[x]])
        cls.append([-v, ER[y]])
        if indep:
            cls.append([-EC[x], -ER[y], v])
    if extra is not None:
        cls.append([EC[extra[0]]])
        cls.append([ER[extra[1]]])
    for t, tv in T.items():
        on = [v for (x, y), v in p.items() if y - x == t] + [
            v for (x, y), v in e.items() if y - x == t
        ]
        cls.append([-tv, *on])
    for s, sv in S.items():
        on = [v for (x, y), v in p.items() if x + y == s] + [
            v for (x, y), v in e.items() if x + y == s
        ]
        cls.append([-sv, *on])
    for x in even:
        for y in even:
            c = [T[y - x], S[x + y]]
            if y in ER:
                c.append(ER[y])
            if x in EC:
                c.append(EC[x])
            cls.append(c)
    if indep:
        for t in range(1 - n, n):
            at_most_one(
                [v for (x, y), v in p.items() if y - x == t]
                + [v for (x, y), v in e.items() if y - x == t]
            )
        for s in range(2 * n - 1):
            at_most_one(
                [v for (x, y), v in p.items() if x + y == s]
                + [v for (x, y), v in e.items() if x + y == s]
            )
    return nv[0], cls, p, EC, ER


def write_dimacs(path, nvars, cls):
    with open(path, "w") as f:
        f.write(f"p cnf {nvars:d} {len(cls):d}\n")
        f.writelines(" ".join(map(str, c)) + " 0\n" for c in cls)


def run_cadical(cnf, log, seed=0, config="sat", timeout=None):
    """-> (exit code, set of true variables or None)"""
    cmd = [CADICAL, "-q", f"--seed={seed:d}"]
    if config != "default":
        cmd.append("--" + config)
    if timeout:
        cmd += ["-t", str(int(timeout))]
    cmd.append(cnf)
    with open(log, "w") as out:
        rc = subprocess.run(
            cmd, stdout=out, stderr=subprocess.STDOUT, check=False
        ).returncode
    if rc != 10:
        return rc, None
    true = set()
    with open(log) as f:
        for line in f:
            if line.startswith("v "):
                true.update(int(w) for w in line.split()[1:] if int(w) > 0)
    return rc, true


# ------------------------------------------------------------------------------------------------- checking
def check_direct(n, D):
    """second, from-scratch domination test (no line sets): walk the 8 rays of every queen and mark squares.
    -> number of undominated squares"""
    assert all(0 <= x < n and 0 <= y < n for x, y in D)
    hit = [[False] * n for _ in range(n)]
    for x, y in D:
        hit[x][y] = True
        for dx, dy in (
            (1, 0),
            (-1, 0),
            (0, 1),
            (0, -1),
            (1, 1),
            (-1, -1),
            (1, -1),
            (-1, 1),
        ):
            u, v = x + dx, y + dy
            while 0 <= u < n and 0 <= v < n:
                hit[u][v] = True
                u += dx
                v += dy
    return sum(1 for x in range(n) for y in range(n) if not hit[x][y])


def independent(D):
    D = list(D)
    return all(
        a[0] != b[0]
        and a[1] != b[1]
        and a[1] - a[0] != b[1] - b[0]
        and a[0] + a[1] != b[0] + b[1]
        for i, a in enumerate(D)
        for b in D[i + 1 :]
    )


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("n", nargs="?", type=int, default=48)
    ap.add_argument("--method", default="sa", choices=["sa", "sat"])
    ap.add_argument("--cc", action="store_true")
    ap.add_argument("--indep", action="store_true")
    ap.add_argument("--extra", nargs=2, type=int, default=None)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--iters", type=int, default=16000000)
    ap.add_argument("--t0", type=float, default=1.2)
    ap.add_argument("--t1", type=float, default=0.12)
    ap.add_argument("--pw", type=int, default=1)
    ap.add_argument("--max-cpu", type=float, default=None)
    ap.add_argument("--config", default="sat", choices=["sat", "default", "unsat"])
    ap.add_argument("--timeout", type=int, default=None)
    ap.add_argument("--work", default=".")
    ap.add_argument("--out", default=None)
    ap.add_argument("--keep", action="store_true")
    a = ap.parse_args()
    n = a.n
    extra = tuple(a.extra) if a.extra else None
    assert n % 2 == 0 and n >= 4
    t0 = time.time()
    c0 = os.times()
    res = {
        "n": n,
        "method": a.method + ("-c" if a.cc and a.method == "sa" else ""),
        "seed": a.seed,
        "indep_requested": a.indep,
        "extra_fixed": extra,
    }
    D = ex = None
    if a.method == "sa":
        assert n <= 64, "the C twin keeps a diagonal set in one 64-bit word"
        fixed = None
        if extra is not None:
            assert extra[0] % 2 == 0 and extra[1] % 2 == 0, (
                "the annealer keeps the extra queen on even lines"
            )
            fixed = (extra[0] // 2, extra[1] // 2)
        kw = {
            "iters_per": a.iters,
            "T0": a.t0,
            "T1": a.t1,
            "indep": a.indep,
            "pw": a.pw,
            "fixed": fixed,
            "max_cpu": a.max_cpu,
        }
        r = (
            anneal_c(a.work, n // 2, a.seed, **kw)
            if a.cc
            else anneal_py(n // 2, a.seed, **kw)
        )
        res.update({"iters_per_restart": a.iters, "T0": a.t0, "T1": a.t1, "pw": a.pw})
        if r is not None:
            a0, b0, perm, restarts, moves = r
            ex = (2 * a0, 2 * b0)
            D = sorted([ex] + [(2 * i + 1, 2 * perm[i] + 1) for i in range(n // 2)])
            res.update({"restarts": restarts, "moves": moves})
        sa_impl = "embedded C twin (--cc)" if a.cc else "pure Python"
        pw_flag = f" --pw {a.pw:d}" if a.indep else ""
        how = f"simulated annealing, {sa_impl}, --iters {a.iters:d} --t0 {a.t0!r} --t1 {a.t1!r}{pw_flag}"
    else:
        indep_tag = "_indep" if a.indep else ""
        extra_tag = f"_e{extra[0]:d}_{extra[1]:d}" if extra is not None else ""
        tag = f"q{n:d}{indep_tag}{extra_tag}_s{a.seed:d}_{a.config}"
        cnf = os.path.join(a.work, tag + ".cnf")
        log = os.path.join(a.work, tag + ".out")
        nvars, cls, p, EC, ER = encode(n, extra, a.indep)
        write_dimacs(cnf, nvars, cls)
        rc, true = run_cadical(cnf, log, a.seed, a.config, a.timeout)
        res.update(
            {"vars": nvars, "clauses": len(cls), "cadical_exit": rc, "config": a.config}
        )
        if true is not None:
            exs = [
                (x, y)
                for x, cx in EC.items()
                if cx in true
                for y, ry in ER.items()
                if ry in true
            ]
            assert len(exs) == 1
            ex = exs[0]
            D = sorted(set([sq for sq, v in p.items() if v in true] + [ex]))
        if not a.keep:
            with contextlib.suppress(OSError):
                os.remove(cnf)
        how = (
            f"CaDiCaL 3.1.0 binary --{a.config} on a DIMACS file written by the script"
        )
    c1 = os.times()
    cpu = (c1.user + c1.system + c1.children_user + c1.children_system) - (
        c0.user + c0.system + c0.children_user + c0.children_system
    )
    res.update({"cpu_s": round(cpu, 1), "wall_s": round(time.time() - t0, 1)})
    if D is not None:
        assert ex is not None
        sys.path.insert(0, HERE)
        from geom import dominated

        und = check_direct(n, D)
        res.update(
            {
                "size": len(set(D)),
                "set_col_row": [list(q) for q in D],
                "undominated": und,
                "geom_dominated": bool(dominated(n, D)),
                "independent": independent(D),
                "extra_queen": list(ex),
            }
        )
        ok = len(set(D)) == len(D) == n // 2 + 1 and und == 0 and res["geom_dominated"]
        res["dominating"] = ok
        if a.out and ok and (res["independent"] or not a.indep):
            cc_flag = " --cc" if a.cc and a.method == "sa" else ""
            indep_flag = " --indep" if a.indep else ""
            extra_flag = (
                f" --extra {extra[0]:d} {extra[1]:d}" if extra is not None else ""
            )
            pos_desc = (
                "fixed"
                if extra is not None
                else "free"
                + (" on the even lines" if a.method == "sa" or a.indep else "")
            )
            rec = {
                "n": n,
                "size": len(D),
                "set_col_row": [list(q) for q in D],
                "undominated": und,
                "geom_dominated": res["geom_dominated"],
                "independent": res["independent"],
                "source": (
                    f"frame/find_q48.py {n:d} --method {a.method}{cc_flag}{indep_flag}{extra_flag} "
                    f"--seed {a.seed:d} ({how}; no PySAT; permutation on the odd lines + one "
                    f"extra queen, position {pos_desc}; the search put it at ({ex[0]:d},{ex[1]:d})); "
                    f"uncertified search, {cpu:.0f} CPU-s, "
                    "checked directly by geom.dominated and by find_q48.check_direct (ray marking)"
                ),
            }
            with open(a.out, "w") as f:
                f.write(json.dumps(rec))
    print(json.dumps(res))
    return 0 if D is not None and res.get("dominating") else 1


if __name__ == "__main__":
    sys.exit(main())
