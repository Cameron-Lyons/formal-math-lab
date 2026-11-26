# Independent colored exact-cover approach

The unrestricted ternary count is still **open**. This experiment builds an independent exact-cover solver with adaptive constraints, checks it against known counts, and tests whether its pruning and component splitting beat row-major search.

## Exact model

For `q` colors, there are `q^4` T placements and `q^4` ordered patterns. Each candidate row `(placement, pattern)` covers those two primary columns and sets four cell colors. Two candidates conflict when they share a placement, share a pattern, or assign conflicting colors to the same cell; choosing a candidate deletes every conflicting candidate.

A compatible cover picks one pattern per placement and uses each pattern once. Because every board cell belongs to at least one T, the chosen candidates reconstruct one unique board, and every valid board gives one unique cover. Cover counts therefore equal labeled board counts directly, with no auxiliary multiplicities.

The solver stores all 6,561 ternary candidates in 103-word bitsets and branches on a primary column with the fewest live candidates (with flags to branch only on placements or only on patterns). Singleton columns propagate right away without branching. An initial cell prefix filters the starting candidates and may fix up to all 100 cells.

Optional exact reductions:

* **Cell consistency:** intersect the colors allowed by every live T touching a cell, dropping candidates that use any eliminated color. Because every color appears `q^3` times in each of the four T roles, min/max domain bounds propagate those quotas too.
* **Cell branching:** if a cell has fewer remaining choices than the best primary column, branch on the cell instead (breaking ties toward cells touched by tighter windows).
* **Endpoint flow:** each lower row forms a trail of adjacent color pairs. Because all patterns appear once, the multiset of row-start pairs matches the multiset of row-end pairs; interval bounds on those nine ternary pair counts prune dead endpoint candidates.
* **Hall filtering:** any valid completion gives a perfect matching between open placements and unused patterns. `exact_cover_hall.hpp` tests matching existence and optionally drops edges that lie in no perfect matching (its exhaustive graph tests live in the parent investigation).
* **Exact memoization:** cache the post-propagation active-candidate bitset using the full vector as the key, resolving hash collisions by exact equality.
* **Component multiplication:** link two open placements if they share an available pattern or a free cell. Disjoint components have independent choices whose counts multiply, provided each has equal numbers of placements and patterns. Cell consistency and Hall filtering stay active per component, while global role quotas and endpoint flow turn off inside an isolated component. Any timed-out product is dropped completely.

Branches are disjoint, every reduction is sound, and unsigned 128-bit arithmetic throws on overflow instead of wrapping.

## Independent validation

`python experiments/exact_cover_check.py` passed every check:

* Full binary count **168** across all three primary branching modes and with all optional reductions enabled.
* All 16 binary two-row prefix counts match the published row enumerator.
* Published ternary seven-row prefixes C and P each give **2** completions, including with all reductions enabled.
* A fixed valid ternary board gives 1 completion; changing its apex produces an invalid board with 0 completions.
* A genuine splice fixture exercises component multiplication: two boards differ in four cells, brute-force checking of all 16 assignments finds 4 valid boards, and the solver splits the search into two independent components and multiplies `2 × 2 = 4`.

That last fixture comes from group 6 (0-based index 5) of `splice_witnesses.json`, taking two caps and two tails differing at two cells each (original source and license notices stay in the repo). `--supports-file` restricts each placement to patterns occurring in the given boards for testing only. See `exact_cover_product_fixture.txt` and `exact_cover_check.log`.

## Measured search sizes

Every entry below exhausts its seven-row prefix and returns 2 boards. Work per node varies substantially across modes, so these are node counts rather than direct timings:

| Configuration | Prefix C | Prefix P |
|---|---:|---:|
| Plain adaptive exact cover | 1,310,134 | 4,424,401 |
| Cell consistency and role quotas | 240,219 | 635,457 |
| Plus Hall filtering | 238,157 | 633,501 |
| Cell branching and endpoint flow | 94,470 | 146,231 |
| Cell branching, flow, and Hall | 93,097 | 144,861 |

The strongest settings cut search nodes by about 14x on C and 30x on P, yet still ran slower in wall time than the row-major counter on both prefixes. Hall filtering adds very little pruning here, and strong runs on C and P saw zero component splits and zero cache hits, so caching only added overhead.

Full matrices are in `exact_cover_benchmark.json` and `exact_cover_flow_benchmark.json`, with the all-options runs in `exact_cover_check.log`. Because wall times shift under concurrent load, node counts are the main comparison.

## Bounded unrestricted tests

With cell branching, cell consistency, endpoint flow, component splitting, and a 100,000-entry memo cache, an unrestricted run visited 574,464 nodes in 15.42 seconds with no witness, no component split, and 1 cache hit. Turning on Hall filtering visited 138,240 nodes in 15.03 seconds, again with no witness, no component split, and 1 cache hit. Both ended `INCOMPLETE` (a partial count of 0 proves nothing).

Neither setting exhausted the first published six-row prefix within 15 seconds either (0 partial completions, 0 component splits, 6 cache hits each). Component multiplication works on explicit splice fixtures, though it never triggered during these bounded runs, giving no sign that this solver can finish the full ternary count. See `exact_cover_unrestricted.json` for exact arguments and output.

## Running the counter

```sh
g++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror experiments/exact_cover.cpp -o /tmp/tboard-cover
/tmp/tboard-cover --colors 2 --seconds 30
/tmp/tboard-cover --colors 3 --seconds 15 --branch-cells 1 --flow 1 --hall 81 --components 1 --memo 100000
python experiments/exact_cover_check.py
python experiments/exact_cover_benchmark.py --seconds 15
```

Flags: `--hall K` turns on Hall filtering once at most `K` placements remain (`0` disables it); `--hall-prune 0` checks matching existence without pruning edges; `--cells 1` turns on cell consistency alone; `--branch-cells 1` implies `--cells 1`; `--seconds 0` runs with no time limit. Only `status=COMPLETE` reports an exact total; on timeout, `count` reports only completed subtrees (a lower bound for that region). Exit codes: 0 for complete, 1 for timeout, 2 for invalid arguments or overflow.
