# Interleaved exact transfer for the final two rows

The interleaved recurrence is implemented and independently tested. It consumes
bottom-row patterns while building the penultimate row, pruning dead ends
before a full penultimate row is completed. On small fibers, the node-count
results are mixed, and integrating it into the known six-row 138-board fiber
did **not** finish within the 90-second wall limit. The unrestricted count
remains uncomputed.

## Exact recurrence

For ternary boards, fix rows 0 through 7. Write `u` for the 15 colors in row 7
and `S` for the 32 unused patterns. Let `(a, b)` be the current pair in row 8
and `(c, d)` the current pair in row 9. At step `i`, pick new colors `x` and
`y` and consume the two distinct patterns

    upper = (u[i], a, b, x)
    lower = (a, c, d, y).

Both must lie in `S`. Remove both and move to pairs `(b, x)` and `(d, y)`.
After 15 steps, two patterns remain: the final two bottom-row windows, with top
word `(a, b)` and starting bottom pair `(c, d)`. Their completion count comes
directly from those two remaining pattern masks.

Every valid coloring of the last two rows corresponds to one unique sequence of
choices, and every valid sequence uses each remaining pattern once. The
recurrence therefore counts extensions exactly, with no extra assumptions on
board shape or colors. The binary version uses 5 paired steps and 12 residual
patterns.

## Pruning and exact memoization

Row 8 has a known color histogram: for each color `t`, its quota equals the
number of residual patterns with top color `t` minus the occurrences of `t` in
`u`. The counter rejects negative quotas and decrements the quota as each row-8
cell is chosen.

Each residual pattern also acts as a directed edge from its lower-left pair to
its lower-right pair. Let `D` be residual outdegree minus indegree. Given
starting pairs `v` and `w`, the required multiset of ending pairs is

    E = unit(v) + unit(w) - D.

Every entry of `E` must be nonnegative, and its entries sum to 2, which prunes
impossible starting-pair choices. The final pair of row 8 must belong to `E`,
pruning the last two row-8 choices as well (this final check can be toggled off
for comparison).

The optional memo key packs the remaining pattern set, both current pairs, and
the remaining suffix of `u` into 112 non-overlapping bits, using exact key
equality to resolve hash collisions. For a fixed `u`, the step index is already
determined by the number of unused patterns; keeping the suffix of `u` makes
cache entries safely reusable across different fixed prefixes.

Neither the color quota nor `E` needs to be stored in the key: both follow from
the remaining patterns, current pairs, and suffix of `u`. In particular,
removing one edge from each path and advancing the two current pairs leaves `E`
unchanged, so identical residual states reached by different histories can
share cached counts.

Counts for a fixed eight-row ternary prefix fit in 64 bits (at most 36 cells
remain, and `3^36 < 2^64`). The integrated earlier-prefix counter checks
accumulation overflow separately.

## Independent verification

`python experiments/exact_tworow_check.py` passed:

* All **512 binary three-row prefixes** (including invalid prefixes) match the
  independent published enumerator and sum to **168**, checked across three
  memo depths and both settings of final-endpoint pruning.
* Seven ternary eight-row fibers match the independent row-major counter, with
  counts from **1 to 10**. All 84 of their global-color and reflection images
  were run twice to test cross-request cache reuse, across all three memo
  depths and with endpoint pruning both on and off.
* Both full published seven-row fibers C and P finished under the integrated
  transfer and returned **2** completions each.

See `exact_tworow_check.log`. These are computational checks rather than a
Lean-verified proof of the counting binary.

## Fixed eight-row measurements

| Region | Exact count | Row-major nodes | Interleaved states, no memo |
|---|---:|---:|---:|
| Published seed 1 prefix | 1 | 334 | 919 |
| Published seed 2 prefix | 1 | 1,106 | 857 |
| Published seed 3 prefix | 1 | 348 | 3,986 |
| Published seed 4 prefix | 1 | 494 | 153 |
| Published seed 5 prefix | 1 | 268 | 891 |
| Extension group 15, selected prefix | 6 | 958 | 4,154 |
| Further group 93, selected prefix | 10 | 2,580 | 2,051 |

The two counters do different work per node, and these fibers are tiny, so
their microsecond runtimes should not be extrapolated into a general speed
ratio. They show that consuming bottom patterns early can shrink or expand the
search tree depending on the prefix.

Memoization was slower on these fibers. It found a few shared states (for
example, 20 cache hits at full depth on the six-board fiber), which was not
enough to pay for hashing and storage. The repeated-input validation creates
artificial cache hits and does not reflect a global search workload. Full
numbers are in `exact_tworow_benchmark.json`.

## Seven-row and six-row integrations

The experimental search copy keeps the original enumeration of earlier rows and
replaces only the last two rows with this recurrence, leaving all original
source files unchanged.

Without memoization, fiber C made 2,808 transfer calls and visited 2,737,309
interleaved states in about 0.0477 CPU seconds, while fiber P made 10,702 calls
and visited 1,879,146 states in about 0.0311 to 0.0329 CPU seconds. Both found
2 boards. Turning on memoization slowed both down significantly and produced
very few cache hits. See `exact_tworow_prefix_benchmark.json` and the
validation log.

Because the small-fiber results were mixed and fiber P looked promising, we
tried a cache-free integration on the known six-row 138-board fiber. It hit the
**90-second wall limit** and was terminated without a count. Although the
earlier final-row integration finished that fiber, machine load changed between
runs and the timed-out run did not record child CPU time. So this shows only
that the integration did not finish within 90 wall seconds, without giving an
exact CPU slowdown or speed ratio.

The timeout is logged as `INCOMPLETE` in
`exact_tworow_integrated_benchmark.json`, claiming no partial count or lower
bound. The recurrence is exact, but this implementation has not shown a gain on
the larger six-row fiber or a route to the unrestricted total.

## Reproduction

```sh
python experiments/exact_tworow_check.py
python experiments/exact_tworow_benchmark.py
python experiments/exact_tworow_integrated.py
```

The last command builds the six-row integration and enforces a 90-second wall
limit. Its wrapper now records child CPU time for future runs (added after the
saved timeout and not used to estimate prior CPU usage).

The standalone counter reads eight-row ternary prefixes (64 digits) or
three-row binary prefixes (9 digits), one per line:

```sh
g++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror experiments/exact_tworow_count.cpp -o /tmp/tboard-tworow
/tmp/tboard-tworow 3 0 0 90 < eight-row-prefixes.txt
```

Arguments are color count, maximum residual-edge count to memoize, maximum
cache entries, per-prefix time budget in seconds, and optional final-endpoint
pruning (1 by default). Every output carries an explicit `COMPLETE` or
`INCOMPLETE` status; only `COMPLETE` gives an exact count. The integrated copy
defaults to seven fixed rows; compile with `-DTWO_START_ROW=6` for six fixed
rows and run under an external time limit.
