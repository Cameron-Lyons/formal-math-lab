# Exact prefix counts and the size of a transfer search

These experiments do **not** compute the unrestricted number of valid ten-row ternary boards. Instead, they count all valid five-row caps exhaustively, measure how much an exact transfer state compresses the search, and build a resumable prefix counter that tracks completion explicitly.

## Exact five-row cap count

There are exactly **198,649,032,096 labeled ternary caps** on rows of lengths 1, 3, 5, 7, and 9 whose 16 T patterns are all distinct. Many of these 25-cell caps do not extend to full ten-row boards.

The census splits all three-row prefixes into orbits under color permutations and horizontal reflection. Out of $3^9 = 19,683$ labeled prefixes, 18,342 have four distinct T patterns and 1,341 repeat a pattern (so they have zero extensions). The valid prefixes form 1,572 orbits: 1,485 of size 12 and 87 of size 6, each size verified by generating all 12 images explicitly. For each representative, the C++ counter searches every assignment of the remaining 16 cells, pruning as soon as a pattern repeats. Weighting each completion count by its orbit size and summing gives the total above.

All 1,572 shards finished in 188.957 seconds on this machine. Individual counts and completeness flags are saved in `exact_algo_census_results.json`, with the progress log in `exact_algo_census.log`. This is an external C++ enumeration, not a Lean proof.

A separate fixed-point counter finds 567,420 valid five-row caps fixed by horizontal reflection alone, and 0 fixed by reflection composed with a color transposition. No nonidentity color permutation can fix a valid five-row cap (a single color would repeat T patterns, so at least two colors appear), and no reflected 3-cycle can fix one because its square is a nonidentity color permutation. By Burnside's lemma, there are exactly

    (198649032096 + 567420) / 12 = 16554133293

cap orbits: 94,570 of size 6 and 16,554,038,723 of size 12. You can also see why transposition-reflection fixes zero caps directly: it fixes 4 T placements in the cap, while fixing only 3 ordered ternary patterns, so the pattern map cannot be injective.

These totals show how large the five-row frontier is and why checking a handful of five-row caps cannot settle the full board count.

## Transfer state and observed compression

To count continuations of a partial board, you only need the pair `(last row, used T-pattern set)`. Given the last row `u` and a candidate next row `v`, form all patterns `(u[j], v[j], v[j+1], v[j+2])`; the step is valid when those patterns are all distinct and disjoint from the used set. Summing weights across incoming transitions from the initial single-cell apex states counts every valid board once, reaching the full count at ten rows.

Materializing this state space exhaustively with the apex fixed to 0 gives:

| Colors | Rows | Distinct-pattern caps | Distinct transfer states |
|---|---:|---:|---:|
| 3 | 3 | 6,114 | 6,114 |
| 3 | 4 | 9,391,598 | 9,379,134 |
| 2 | 5 | 84 | 67 |

At four ternary rows, merging equal transfer states collapses only 12,464 paths (**0.1327%**): 12,428 states appear twice and 18 appear three times. Plain memoization barely compresses the frontier at this depth, though a stronger state reduction might still exist. The full labeled four-row cap count is 28,174,794.

To avoid runaway memory use, the frontier tool refuses to run past four ternary rows (see `exact_algo_frontier.log`).

## Reproduction and verification

From the repository root:

```sh
python experiments/exact_algo_check.py
python experiments/exact_algo_census.py --seconds 240

g++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror experiments/exact_algo_frontier.cpp -o /tmp/tboard-frontier
/tmp/tboard-frontier 3 4

g++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror experiments/exact_algo_fixed.cpp -o /tmp/tboard-fixed
/tmp/tboard-fixed 3 5
```

`exact_algo_check.py` enumerates T placements in Cartesian coordinates over all binary three- and four-row boards and all ternary three-row boards, reproducing the exact counts 360, 5,756, and 18,342. It also reproduces the full binary count of 168, checks prefix-partition sums, checks reflection fixed points against brute force, rejects a repeated-pattern prefix, verifies that timeouts roll back unfinished shards, matches both published seven-row ternary prefix counts of 2, and counts each of the five fixed 100-cell certificates once (`exact_algo_check.log`). Literal prefixes can specify up to all 100 cells directly; only numeric interval splitting is capped at 64-bit prefix integers.

The standalone counter accepts either a literal prefix or a deterministic prefix interval (`--split-cells K` reads the first `K` cells as a base-`q` integer, and `--begin B --end E` runs over `[B, E)`):

```sh
g++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror experiments/exact_algo_count.cpp -o /tmp/tboard-count
/tmp/tboard-count --colors 2 --rows 5
/tmp/tboard-count --colors 3 --rows 5 --prefix 000021121
/tmp/tboard-count --colors 3 --rows 5 --split-cells 9 --begin 205 --end 207
```

The second command finds 13,513,876 five-row completions, and the third finds 26,607,192 across its two prefixes. If a run hits its time limit, it prints `INCOMPLETE`, drops the unfinished shard's count, and reports `completed_end` along with the exact count for completed shards only (nothing is extrapolated). The census wrapper checkpoints every 100 shards and caps each child run's time.

In literal `--prefix` mode, the tool echoes the literal string and reports interval `[0, 1)`. The saved census predates that format tweak and stored short literal prefixes as base-`q` integers; the searched boards and counts did not change.

Totals use unsigned 128-bit integers. The parameterization in `exact_math.md` also covers partial caps (filling unused permutation slots in sorted order and unused boundary cells with zeros) and bounds every valid ternary cap by $3^{19} \cdot 6^{27} < 2^{100}$, so 128 bits cannot overflow even for the full board. The 64-bit node counter is only a diagnostic.
