# Exact prefix counts and the size of a transfer search

The unrestricted number of valid ten-row ternary boards is **not computed**
by these experiments. They provide an exhaustive count of all five-row caps,
measure the effectiveness of an exact transfer state, and provide a resumable
prefix counter with explicit completeness status.

## Exact five-row cap count

There are exactly **198,649,032,096 labeled ternary caps** on rows of lengths
1, 3, 5, 7, 9 whose sixteen T patterns are pairwise distinct. These caps need
not extend to valid ten-row boards.

The census partitions all first-three-row prefixes into color-permutation and
horizontal-reflection orbits. Of the 3^9 = 19,683 labeled prefixes, 18,342 have
four distinct T patterns; 1,341 contain a repetition and have no valid
extensions. The valid prefixes form 1,572 orbits: 1,485 of size twelve and 87
of size six. Every orbit size is checked by explicitly generating all twelve
images. For each representative, the C++ counter exhausts every assignment
of the remaining sixteen cells, rejecting a branch as soon as a T pattern
repeats. Multiplying each completion count by its prefix orbit size and
summing gives the number above.

All 1,572 shards completed in 188.957 seconds on this machine. The individual
counts and completeness flags are in `exact_algo_census_results.json`; the
progress log is `exact_algo_census.log`. This is an ordinary computational
enumeration, not a kernel-checked Lean theorem.

The reflection fixed-point counter independently finds 567,420 such caps
fixed by ordinary horizontal reflection, and none fixed by reflection
combined with a color transposition. Nonidentity color permutations cannot
fix a valid five-row cap: such a cap uses at least two colors, since one color
would repeat T patterns. A reflected three-cycle cannot fix a cap because
its square is a nonidentity color permutation. Burnside's lemma therefore
gives exactly

    (198649032096 + 567420) / 12 = 16554133293

cap orbits. Of these, 94,570 have size six and 16,554,038,723 have size twelve.
The zero transposition-reflection count also follows directly: it fixes four
T placements in this cap, but only three ternary ordered patterns, contrary
to injectivity of the pattern map.

These exact totals show why enumerating a few selected five-row caps cannot
establish the unrestricted board count.

## Transfer state and observed compression

For a partial board, the pair `(last row, used T-pattern set)` is sufficient
for counting continuations. If `u` is the last row and `v` a candidate next
row, calculate all patterns `(u[j], v[j], v[j+1], v[j+2])`. A transition is
allowed precisely when these patterns are distinct and disjoint from the
used set. State weights add across incoming transitions. Starting with one
state per apex color and the empty used set, this recurrence counts every
board exactly once; at ten rows its total is the desired unrestricted count.

The frontier experiment exhaustively materializes this state for small
caps, with the apex fixed to zero:

| Colors | Rows | Distinct-pattern caps | Distinct transfer states |
|---|---:|---:|---:|
| 3 | 3 | 6,114 | 6,114 |
| 3 | 4 | 9,391,598 | 9,379,134 |
| 2 | 5 | 84 | 67 |

At four ternary rows, merging equal states removes only 12,464 paths,
**0.1327%** of the input. There are 12,428 states of multiplicity two and
18 of multiplicity three. Thus this direct memoization has little effect
at this stage; the experiment does not establish that no stronger state
reduction exists. The full labeled four-row cap count is 28,174,794.

The frontier tool rejects more than four ternary rows to prevent an
accidental enormous allocation. See `exact_algo_frontier.log`.

## Reproduction and verification

From the repository root:

```sh
python experiments/exact_algo_check.py
python experiments/exact_algo_census.py --seconds 240

g++ -O3 -std=c++20 experiments/exact_algo_frontier.cpp -o /tmp/tboard-frontier
/tmp/tboard-frontier 3 4

g++ -O3 -std=c++20 experiments/exact_algo_fixed.cpp -o /tmp/tboard-fixed
/tmp/tboard-fixed 3 5
```

The independent check enumerates actual Cartesian-coordinate T placements
for all binary three- and four-row assignments and all ternary three-row
assignments. Their exact counts are 360, 5,756 and 18,342, respectively.
It also reproduces the unrestricted binary count 168, verifies the complete
prefix partition sums, checks reflection fixed points against coordinate
brute force, rejects a repeated-pattern prefix, and verifies that timeout
rolls back an unfinished shard. All checks passed; see `exact_algo_check.log`.
The checks also reproduce both published seven-row ternary prefix counts
of two and count each of the five completely fixed 100-cell certificates
once. Literal prefixes are loaded directly and can specify all 100 cells;
only the numeric interval mode is limited to 64-bit prefix integers.

The plain exact counter can count a prescribed prefix or a deterministic
interval of prefixes. `--split-cells K` interprets the first K flattened
cells as a base-q integer; `--begin B --end E` selects the disjoint interval
[B,E). For example:

```sh
g++ -O3 -std=c++20 experiments/exact_algo_count.cpp -o /tmp/tboard-count
/tmp/tboard-count --colors 2 --rows 5
/tmp/tboard-count --colors 3 --rows 5 --prefix 000021121
/tmp/tboard-count --colors 3 --rows 5 --split-cells 9 --begin 205 --end 207
```

The second command counts exactly 13,513,876 five-row completions. The third
counts 26,607,192 completions across its two selected prefixes. On timeout,
the tool reports `INCOMPLETE`, discards the unfinished shard's count, and
prints `completed_end` and the exact count for only the completed interval.
No timeout result is extrapolated. The census wrapper also checkpoints
completed orbits every hundred shards and imposes a time budget on each
child count.

For literal `--prefix` mode, the output includes the literal word and uses
the single-item interval `[0,1)`. The original census data were generated
before this reporting change, when short literal prefixes were encoded
as their base-q integers. The searched cell assignments and their counts
are unchanged.

The integer count uses unsigned 128-bit arithmetic. The row-major
parameterization in `exact_math.md` also encodes partial caps after the unused permutation entries are filled
in sorted order and unused boundary digits are set to zero. It bounds every valid
ternary cap by at most 3^19 * 6^27 < 2^100 possibilities, so this suffices
for the full count as well. The 64-bit node counter is diagnostic only.
