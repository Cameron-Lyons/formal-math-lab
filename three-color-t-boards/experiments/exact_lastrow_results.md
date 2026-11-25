# Exact final-row transfer and reusable suffix counts

The unrestricted ternary count remains **unevaluated**. An exact small
terminal dynamic program does exist, including reuse across different
prefixes. The completed experiment shows that this terminal work is already
a negligible part of one established long prefix search; accelerating it
alone cannot address that search's bottleneck.

## The exact terminal problem

After rows 0 through 8 are fixed, 64 patterns have been used and 17 remain.
Let S be the residual pattern set and let `t[0..16]` be row 8. Regard each
pattern `(t,l,m,r)` as a distinct directed edge

    (l,m) -> (m,r), labeled t.

The nine vertices are ordered color pairs. A bottom row is exactly a trail
that uses every edge of S once and reads the prescribed label word t.
Its initial pair and successive edge endpoints recover all nineteen bottom
cells uniquely. Parallel edges with different top colors remain distinct.

For a remaining set R, current pair p, and remaining label suffix w, define

    D(empty, p, empty) = 1
    D(R, p, a::w) = sum D(R\{e}, destination(e), w)

where the sum is over edges e in R whose source is p and label is a.
The terminal completion count is the sum over permitted initial pairs.
For one fixed seventeen-letter word, the position is determined by |R|,
so at most **9 × 2^17 = 1,179,648** subset/pair states are possible. Each
has at most three outgoing choices.

The complete suffix w is required for reuse across different prefixes.
For example, the two edges `(0,0,0,1)` and `(1,0,1,2)` admit the label word
`01` in exactly one order, while `10` admits no trail, even though both
words have the same color counts. Counting unlabeled Euler trails and
dividing by a number of label words would therefore be invalid.

## Exact cache across different upper boards

`exact_lastrow.hpp` implements D. It consumes forced edges before caching.
A key contains the actual remaining 81-bit pattern mask, the prescribed
suffix encoded in base three, and the current pair. The suffix length is
recoverable from the number of remaining edges, so leading zero colors do
not create ambiguous keys. These fields occupy 112 bits without overlap.
Hash collisions are resolved by equality of the complete 128-bit key.

Two different upper boards, and even two different row-8 words, can reuse
a cache entry when their remaining edge set, current pair, and remaining
label suffix agree. Cached values count multiplicities; they are added for
each incoming upper-board history. No individual board is discarded.
The terminal count is at most 3^19, so its 64-bit arithmetic is sufficient.

The standalone program `exact_lastrow.cpp` reads flattened prefixes of all
rows except the last, one per line. The experimental copy
`exact_lastrow_search.cpp` replaces only the final-row enumeration of
`splice_search.cpp`, preserving its search and necessary-condition pruning
for rows 6, 7 and 8. The original file is unchanged. The copy detects
64-bit overflow of its accumulated fixed-prefix count rather than wrapping.

## Exhaustive validation

`python experiments/exact_lastrow_check.py` passed:

* Every one of the 65,536 binary first-four-row assignments agrees with
  the independent published cell-by-cell enumerator. The valid full boards
  sum to **168**. Cache depths zero, four and seven agree separately.
* Thirty-one ternary nine-row prefixes agree with an independent full-board
  row-major counter, including a prefix with **six** bottom-row completions.
  The whole input list is repeated to exercise reuse across requests.
  Cache depths zero, eight and seventeen all agree.
* Every experimental six-row search of group 1 exhausts its region and
  returns the established **138** completions. No timeout or incomplete
  global run is used in these measurements.

See `exact_lastrow_check.log`, `exact_lastrow_benchmark.json` and
`exact_lastrow_cpu_benchmark.json`.

## What the completed fiber shows

Group 1 uses the six-row prefix
`000000100002011001202102210110211112`. Its optimized search reaches only
52,132 final-row problems. Without memoization, their combined evaluation
visits **468,915 terminal states**, about nine states per request. This is
far below the terminal DP's worst-case bound.

| Cache depth | Entries retained | Lookups | Hits | Terminal states |
|---:|---:|---:|---:|---:|
| 0 | 0 | 0 | 0 | 468,915 |
| 4 | 42 | 48 | 6 | 468,889 |
| 8 | 2,185 | 2,279 | 94 | 468,481 |
| 17 | 92,893 | 93,665 | 772 | 461,016 |

Full-depth memoization removes only **1.68%** of terminal states, with a
**0.82%** hit rate. It correctly aggregates some completions, but the
extra key construction and lookup cost exceeds that saving.

A separate timing run measured process CPU rather than relying only on
wall time under concurrent machine load:

| Configuration | Total CPU | CPU inside terminal calls |
|---|---:|---:|
| No memoization | 15.8577 s | 0.030408 s |
| Full-depth memoization | 15.7210 s | 0.089982 s |

The terminal measurements include timing overhead. Nevertheless, all
terminal work accounts for only about **0.19%** of baseline CPU. The small
change in total time is insufficient evidence of a speedup; the measured
terminal work itself nearly triples with the cache. Even eliminating that
work entirely would leave essentially all of this fiber's runtime intact.
This conclusion is scoped to the tested fiber, not a universal lower bound
on every possible counting algorithm.

## Meet-in-the-middle for one terminal row

A different exact implementation could enumerate eight-edge forward trails
and nine-edge backward trails. Record counts by their meeting pair and used
edge subset, then join complementary subsets. The two halves have at most

    9 × (3^8 + 3^9) = 236,196

candidate trails before pruning. This is a useful worst-case bound, but it
still solves only a terminal problem. In the measured fiber the ordinary
terminal search averages about nine states, so generating both halves
would not address the dominant work of finding row-8 candidates.

The local bound also does not control the number of different upper-board
states. Across arbitrary prefixes the residual set can vary among subsets
of the 81-pattern universe, and the label suffix varies as well. The
ordinary row-transfer experiment in `exact_algo_results.md` already found
only 0.1327% state compression at four ternary rows. None of these facts
proves that a stronger global aggregation is impossible; they show why the
small terminal DP alone does not provide one.

## An exact two-row recurrence, and its limitation

After row 7, let u be its fifteen colors and let S contain the 32 patterns
remaining for rows 8 and 9. Maintain the last two middle-row colors `(a,b)`
and the last two bottom-row colors `(c,d)`. At column i, choose new colors
x and y and consume the two distinct patterns

    upper = (u[i], a, b, x)
    lower = (a, c, d, y).

Both must lie in S. Continue with `(b,x)`, `(d,y)`, `i+1`, and the two
patterns removed. Start by summing over all 3^4 initial pair choices.
After the fifteen upper windows, exactly two lower windows remain; their
top word is `(a,b)` and their initial lower pair is `(c,d)`, so the terminal
DP above handles the base case.

This recurrence is exact and permits multiplicity merging without first
enumerating complete middle rows. However, it has **32** residual edges and
**81** pair-frontier combinations. The generic bound on its even-sized
subset states is about

    81 × 2^31 = 173,946,175,488.

Reachable states could be much fewer, but this is no longer a uniformly
small endgame table. The fixed top word also varies between upper prefixes.
Consequently the recurrence is a legitimate further decomposition, but no
practical unrestricted evaluation or strong compression guarantee follows
from it. It was documented rather than adding another unmotivated search
benchmark after the terminal timing located the actual bottleneck.

## Reproduction

```sh
python experiments/exact_lastrow_check.py
python experiments/exact_lastrow_benchmark.py --groups 1 --depths 0,4,8,17
python experiments/exact_lastrow_benchmark.py --groups 1 --depths 0,17 --output experiments/exact_lastrow_cpu_benchmark.json
```

The benchmark wrapper verifies the exact saved fiber count after every
completed run and imposes an external 120-second limit per run. It never
labels a timed-out result complete. The standalone terminal interface is:

```sh
g++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror experiments/exact_lastrow.cpp -o /tmp/tboard-lastrow
/tmp/tboard-lastrow 3 17 1000000 < nine-row-prefixes.txt
```

Its arguments are the number of colors, maximum residual size to cache,
and maximum cache entries. Diagnostics report reuse separately at every
remaining size. The compiled search copy accepts a six-row prefix, cache
depth and capacity; it reports `COMPLETE` only after exhausting that region.
