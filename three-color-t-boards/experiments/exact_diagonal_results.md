# Bottom-up diagonal enumeration

The unrestricted ternary count is still **open**. This standalone counter fills the board along diagonals from the bottom up, a very different order from row-major search and colored exact cover. It finds valid boards quickly in short unrestricted runs, though it cannot exhaust the full search space.

## Order and exactness

Let `d = q²` be the index of the bottom row. For each diagonal `j = 0, ..., 2d`, visit rows `r = d, d-1, ..., 0` while `c = j - 2(d - r) >= 0`, assigning cell `(r, c)`. The bottom cell of each diagonal is free; every other cell sits on top of a T whose three lower cells `(r+1, c)`, `(r+1, c+1)`, `(r+1, c+2)` are already filled (the first two in earlier diagonals, the third earlier in the same diagonal). Every cell is visited once.

For each of the `q³` lower triples, a `q`-bit mask tracks unused top colors. Any non-bottom cell may only pick colors left in its triple's mask, blocking repeated patterns immediately. On a full board, having `q^4` placements and `q^4` patterns means no repeats forces every pattern to appear once. For three colors, this gives 19 free bottom cells and 81 pattern-completing top choices.

Four role/color histograms update incrementally: every color appears `q³` times in each T role, so once a color hits its quota, it is masked out of that role.

Fixed cells are applied **before** traversal, including noncontiguous masks. Their role counts and any already-complete T patterns are marked up front; later, the loop only consumes a pre-fixed top cell's pattern if its lower triple was not already fixed at startup. That avoids double counting and lets top prefixes prune the bottom-up scan right away.

Reversing the scan reflects the traversal order while keeping all fixed cell coordinates in their original unreflected positions.

## Optional endpoint flow

Each lower row traces a trail of adjacent color pairs. Because every pattern occurs once, every pair has equal in-degree and out-degree overall, so the multiset of row-start pairs equals the multiset of row-end pairs. Fixed endpoint pairs load at startup, and each other pair registers when its second free cell is filled.

Whenever the sum of positive pair imbalances exceeds the number of unfilled row ends, the branch is dead. `--flow 1` enables this cheap check during endpoint updates.

## Validation

`python experiments/exact_diagonal_check.py` passed every check (`exact_diagonal_check.log`):

* Unrestricted binary count **168** in both directions, with and without flow.
* Apex-normalized binary count **84**, multiplying by 2 to give 168.
* All 16 binary two-row prefixes match the published row enumerator.
* 20 noncontiguous binary fixed masks match the enumerator in both directions.
* Published ternary seven-row prefixes C and P each give **2** completions in both directions.
* A noncontiguous ternary mask matches brute-force Cartesian checking over all 81 assignments (**4** valid boards).
* Timed-out unrestricted runs print `INCOMPLETE` and `completed_leaves`, never an exact or normalized total.

These are external computational checks rather than a Lean proof of the counter.

## Measured search sizes

Every fixed-prefix run below was exhaustive and returned 2 boards:

| Region | Direction | Without flow: nodes | With flow: nodes |
|---|---|---:|---:|
| C | Left to right | 90,886,698 | 90,886,692 |
| C | Right to left | 82,006,985 | 82,006,977 |
| P | Left to right | 74,239,729 | 10,588,630 |
| P | Right to left | 47,728,281 | 7,327,140 |

Reverse P with flow took roughly 0.13 to 0.16 seconds, while C stayed around 1.6 to 2.0 seconds. Endpoint flow cuts P dramatically while barely touching C, and the existing row-major counter stays faster overall on these prefixes.

Four 10-second unrestricted runs fixed only the apex to 0 (both directions, flow off and on). All four stopped as `INCOMPLETE` after roughly 326 to 488 million nodes and 1 complete leaf (a search diagnostic, not a lower-bound certificate or count). Full outputs are in `exact_diagonal_benchmark.json` and `exact_diagonal_flow_benchmark.json`.

If an apex-normalized unrestricted run ever finishes, global color symmetry gives `q` times the apex-zero count; the tool prints that scaled total only on `COMPLETE`, and rejects combining `--normalize-apex 1` with other fixed cells.

## Reproduction

```sh
g++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror experiments/exact_diagonal.cpp -o /tmp/tboard-diagonal
/tmp/tboard-diagonal --colors 2 --normalize-apex 1 --flow 1
/tmp/tboard-diagonal --colors 3 --normalize-apex 1 --flow 1 --seconds 10
python experiments/exact_diagonal_check.py
python experiments/exact_diagonal_benchmark.py --seconds 10
python experiments/exact_diagonal_benchmark.py --seconds 10 --flow 1 --output experiments/exact_diagonal_flow_benchmark.json
```

`--prefix` takes flattened row-major digits, `--fixed` takes a flattened mask with `.` for open cells (both may be shorter than the board and can be combined if consistent), `--reverse 1` reverses traversal, and `--seconds 0` disables the time limit. Exit codes: 0 for complete, 1 for timeout, 2 for invalid input or overflow.
