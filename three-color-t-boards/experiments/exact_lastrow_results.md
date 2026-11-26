# Exact final-row transfer and reusable suffix counts

The unrestricted ternary count is still **open**. Although an exact bottom-row dynamic program can reuse suffix counts across different upper boards, our benchmark shows that bottom-row work is already a tiny fraction of CPU time on a complete six-row search, so speeding up the bottom row alone cannot fix that search's bottleneck.

## The exact terminal problem

Once rows 0 through 8 are fixed, 64 patterns are used and 17 remain. Let `S` be the remaining pattern set and `t[0..16]` be row 8. View each pattern `(t, l, m, r)` as a directed edge

    (l, m) -> (m, r), labeled t

on the 9 ordered color pairs (parallel edges with different top colors stay distinct). A valid bottom row is exactly a trail using every edge of `S` once whose labels spell `t`; its starting pair and sequence of edges uniquely determine all 19 bottom cells.

For a remaining edge set `R`, current pair `p`, and remaining label suffix `w`, define

    D(empty, p, empty) = 1
    D(R, p, a::w) = sum D(R \ {e}, destination(e), w),

summing over edges `e` in `R` leaving `p` with label `a`, and sum over valid starting pairs to get the completion count. For a fixed 17-letter word `t`, the position follows from `|R|`, leaving at most **9 × 2^17 = 1,179,648** `(R, p)` states, each with at most 3 outgoing edges.

Reusing entries across different prefixes requires keying on the full remaining suffix `w`. For example, `(0, 0, 0, 1)` and `(1, 0, 1, 2)` form one valid trail for label word `01` and none for `10`, even though both words share the same color counts, so counting unlabeled Euler trails and dividing by label permutations would fail.

## Exact cache across different upper boards

`exact_lastrow.hpp` implements `D`, consuming forced single edges before touching the cache. Each cache key packs the remaining 81-bit pattern mask, the remaining suffix in base 3 (whose length equals `|R|`, avoiding leading-zero ambiguity), and the current pair into 112 disjoint bits; hash collisions resolve by exact 128-bit equality.

Any two upper boards (even with different row-8 words) share a cache entry whenever their remaining edges, current pair, and remaining suffix match. Cached counts add cleanly across incoming histories without losing any board, and 64-bit integers easily hold the bottom-row total (at most $3^{19}$).

`exact_lastrow.cpp` is a standalone reader taking flattened 9-row prefixes one per line. `exact_lastrow_search.cpp` copies `splice_search.cpp` (leaving the original untouched), replaces only row 9 with this DP, keeps all row 6-8 pruning unchanged, and checks for 64-bit overflow when accumulating fixed-prefix counts.

## Exhaustive validation

`python experiments/exact_lastrow_check.py` passed every test:

* All 65,536 binary four-row prefixes match the published cell-by-cell enumerator, summing to **168**, with cache depths 0, 4, and 7 agreeing.
* 31 ternary nine-row prefixes match an independent row-major counter (including one with **6** completions), repeated to test cache reuse, with cache depths 0, 8, and 17 agreeing.
* Every experimental search of six-row group 1 exhausts its fiber and returns **138**, with no timeouts or incomplete runs.

See `exact_lastrow_check.log`, `exact_lastrow_benchmark.json`, and `exact_lastrow_cpu_benchmark.json`.

## What the completed fiber shows

Group 1 fixes the six-row prefix `000000100002011001202102210110211112`. The search reaches only 52,132 row-9 subproblems, visiting **468,915 terminal states** without caching (about 9 states per subproblem, far below the DP's worst case):

| Cache depth | Entries retained | Lookups | Hits | Terminal states |
|---:|---:|---:|---:|---:|
| 0 | 0 | 0 | 0 | 468,915 |
| 4 | 42 | 48 | 6 | 468,889 |
| 8 | 2,185 | 2,279 | 94 | 468,481 |
| 17 | 92,893 | 93,665 | 772 | 461,016 |

Full caching trims only **1.68%** of terminal states (a **0.82%** hit rate), costing more in key packing and table lookups than it saves.

A dedicated CPU timing run separated process CPU from concurrent wall load:

| Configuration | Total CPU | CPU inside terminal calls |
|---|---:|---:|
| No memoization | 15.8577 s | 0.030408 s |
| Full-depth memoization | 15.7210 s | 0.089982 s |

Even including timer overhead, bottom-row work uses only **0.19%** of baseline CPU, and caching nearly triples time spent inside terminal calls. Eliminating bottom-row work completely would barely change total runtime on this fiber (though other algorithms might behave differently).

## Meet-in-the-middle for one terminal row

Splitting row 9 into 8-edge forward trails and 9-edge backward trails, bucketed by meeting pair and used edge subset, builds at most

    9 × (3^8 + 3^9) = 236,196

candidate half-trails before pruning. That gives a nice worst-case bound for a single bottom row, yet because row 9 averages only 9 states per call here, it still leaves the row-8 search untouched.

Nor does a small bottom-row bound control the number of upper-board states: `exact_algo_results.md` already measured only 0.1327% state merging at four ternary rows. While that does not rule out a stronger global aggregation, bottom-row DP alone does not supply one.

## An exact two-row recurrence, and its limitation

After row 7 (word `u` of length 15), 32 patterns `S` remain for rows 8 and 9. Track the last two colors `(a, b)` of row 8 and `(c, d)` of row 9. At step `i`, pick new colors `x` and `y` so that two distinct patterns in `S`,

    upper = (u[i], a, b, x)
    lower = (a, c, d, y),

are consumed, then advance to `(b, x)`, `(d, y)`, `i + 1`, and `S \ {upper, lower}` (summing over all $3^4$ starting pair choices). After 15 steps, 2 lower edges remain above `(a, b)` starting from `(c, d)`, handled by the bottom-row DP.

This exact recurrence merges multiplicities without enumerating full row-8 words first, yet with **32** remaining edges and **81** pair frontiers, the generic state bound for even-sized subsets is

    81 × 2^31 = 173,946,175,488,

and the top word `u` still varies across prefixes. Because reachable tables are no longer uniformly small and the timing data already pinpointed the earlier-row bottleneck, we documented this recurrence without adding another unpromising benchmark here.

## Reproduction

```sh
python experiments/exact_lastrow_check.py
python experiments/exact_lastrow_benchmark.py --groups 1 --depths 0,4,8,17
python experiments/exact_lastrow_benchmark.py --groups 1 --depths 0,17 --output experiments/exact_lastrow_cpu_benchmark.json
```

The benchmark checks the exact saved fiber count on every completed run under a 120-second cap and never marks a timeout complete. Standalone bottom-row tool:

```sh
g++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror experiments/exact_lastrow.cpp -o /tmp/tboard-lastrow
/tmp/tboard-lastrow 3 17 1000000 < nine-row-prefixes.txt
```

Arguments are color count, max remaining size to cache, and max cache entries; output logs reuse by remaining size. The copied six-row search takes a six-row prefix, cache depth, and capacity, printing `COMPLETE` only upon exhausting the prefix.
