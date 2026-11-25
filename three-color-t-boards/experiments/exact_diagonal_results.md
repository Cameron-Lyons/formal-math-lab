# Bottom-up diagonal enumeration

The unrestricted ternary count remains **unevaluated**. This independent
counter explores a substantially different order from row-major enumeration
and colored exact cover. It reaches complete boards in bounded unrestricted
runs, but does not exhaust the unrestricted search.

## Order and exactness

Let the last row index be `d = q²`. For each diagonal index
`j = 0,...,2d`, visit rows `r = d,d-1,...,0` while
`c = j - 2(d-r)` is nonnegative, assigning cell `(r,c)`.
The bottom cell in each diagonal is free. Every other assigned cell is the
top of a T whose three children `(r+1,c)`, `(r+1,c+1)`, `(r+1,c+2)` are already
assigned: the first two occur in preceding diagonals and the third earlier
in this diagonal. Each cell appears exactly once.

For each of the q³ possible lower triples, keep a q-bit mask of unused top
colors. A nonbottom cell can use precisely the colors remaining in its
triple's mask. This prevents repeated ordered T patterns. At a complete
board there are q^4 placements and q^4 patterns, so no repetition implies
that every pattern occurs once. This order has 19 free bottom digits and
81 pattern-completing top choices in the ternary case.

The four role/color histograms are maintained incrementally. In a valid
board every color occurs q³ times in each T role. A color whose quota is
filled is removed from that role's allowed-color mask.

All prescribed cells are fixed **before** traversal, including arbitrary
noncontiguous fixed cells. Their role counts are seeded immediately, and
patterns whose four cells are already fixed are removed before search.
Later traversal processes an already fixed top only when its pattern was
not fully fixed initially. This avoids counting fixed cells or patterns
twice and lets a top prefix constrain a bottom-up scan from the beginning.

The reverse option reflects the traversal order while preserving the
original, unreflected coordinates of prescribed cells.

## Optional endpoint flow

Each lower row is a path of adjacent color pairs. The complete pattern set
has equal indegree and outdegree at every pair, so the multiset of row-start
pairs must equal the multiset of row-end pairs. Fixed endpoint pairs are
seeded before traversal. Each other pair is added when its second unknown
cell is assigned.

If the sum of positive pair imbalances exceeds the number of unassigned
row ends, completion is impossible. The counter checks this necessary
condition only as part of its inexpensive endpoint updates. The reduction
is optional (`--flow 1`).

## Validation

`python experiments/exact_diagonal_check.py` passes:

* Binary complete count **168** in both directions, with and without flow.
* Apex-normalized binary count **84**, multiplied by two to recover 168.
* All sixteen binary first-two-row prefix counts match the independent
  published row enumerator separately.
* Twenty noncontiguous binary fixed masks match that enumerator in both
  directions.
* Both published ternary seven-row prefixes C and P have exactly **two**
  completions in both directions.
* A noncontiguous ternary fixed mask agrees with direct coordinate checking
  of its 81 possible assignments: **four** valid completions.
* A timed-out unrestricted run reports `INCOMPLETE` and `completed_leaves`;
  it does not print an exact total or an unrestricted normalized total.

See `exact_diagonal_check.log`. These are computational checks, not a
kernel-checked Lean proof of the counter.

## Measured search sizes

Every fixed-prefix entry below is exhaustive and returns two boards.

| Region | Direction | Without flow: nodes | With flow: nodes |
|---|---|---:|---:|
| C | Left to right | 90,886,698 | 90,886,692 |
| C | Right to left | 82,006,985 | 82,006,977 |
| P | Left to right | 74,239,729 | 10,588,630 |
| P | Right to left | 47,728,281 | 7,327,140 |

The reverse P run with flow finished in approximately 0.13–0.16 seconds.
C remained around 1.6–2.0 seconds in validation. Endpoint flow helps P
substantially but barely affects C. The existing row-major counter remains
faster on these prescribed regions; this experiment does not show a general
advantage for diagonal order.

Four unrestricted tests fixed only the apex to zero: both traversal
directions, with flow off and on. Each stopped after ten seconds with
`INCOMPLETE`, after approximately 326–488 million nodes and one complete
leaf. That leaf count is a search diagnostic, not a claimed new lower-bound
certificate, and a stopped run supplies no unrestricted exact count.
The full output is recorded in `exact_diagonal_benchmark.json` and
`exact_diagonal_flow_benchmark.json`.

When an apex-normalized unrestricted run actually finishes, global color
permutations biject its q apex-color classes, so the labeled count is q
times the apex-zero count. The counter prints that multiplication only on
completion, and prohibits combining this normalization option with any
other prescribed cells.

## Reproduction

```sh
g++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror experiments/exact_diagonal.cpp -o /tmp/tboard-diagonal
/tmp/tboard-diagonal --colors 2 --normalize-apex 1 --flow 1
/tmp/tboard-diagonal --colors 3 --normalize-apex 1 --flow 1 --seconds 10
python experiments/exact_diagonal_check.py
python experiments/exact_diagonal_benchmark.py --seconds 10
python experiments/exact_diagonal_benchmark.py --seconds 10 --flow 1 --output experiments/exact_diagonal_flow_benchmark.json
```

`--prefix` supplies flattened row-major cell values. `--fixed` supplies a
flattened mask with `.` for unknown cells; either may be shorter than the
board and both may be combined if they agree. `--reverse 1` reverses the
scan. `--seconds 0` requests an unbounded run. Exit status 0 means complete,
1 means timeout, and 2 means invalid input or count overflow.
