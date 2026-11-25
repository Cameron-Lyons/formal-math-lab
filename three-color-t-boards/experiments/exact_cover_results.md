# Independent colored exact-cover approach

The unrestricted ternary count remains **unevaluated**. This experiment
implements a different exact search with adaptive constraints, verifies it
against independent counts, and measures whether its pruning and component
aggregation improve on row-major enumeration.

## Exact model

For q colors there are q^4 T placements and q^4 ordered patterns. A candidate
row `(placement, pattern)` covers those two primary columns and assigns four
cell colors. Two candidates conflict if they use the same placement, use the
same pattern, or assign different colors to a shared cell. Selecting a
candidate removes all its conflicts.

A full compatible cover selects exactly one pattern at each placement and
uses every pattern once. Every board cell belongs to at least one T, so the
selected candidates reconstruct one board. Conversely every valid board
gives exactly one compatible cover. The model is therefore parsimonious:
cover counts equal labeled board counts without auxiliary multiplicities.

The implementation keeps 6,561 ternary candidates in 103-word bitsets. It
chooses a primary column with the fewest active candidates, with options to
branch only on placements or only on patterns. Singleton columns propagate
without a separate recursive branch. A supplied cell prefix filters the
initial candidates and can contain all 100 cells.

Optional exact reductions are:

* **Cell consistency**: intersect the colors supported by every live T
  incident to a cell. A removed color deletes incompatible candidates.
  Each color must occur q^3 times in each of the four T roles; minimum and
  maximum domain counts propagate these quotas.
* **Cell branching**: when a cell has fewer choices than the selected
  primary column, branch on that cell instead. Ties between cells favor
  pressure from more constrained incident windows.
* **Endpoint flow**: each lower row is a path of adjacent color pairs.
  Since all patterns occur once, the multiset of row-start pairs equals
  the multiset of row-end pairs. Interval bounds on their nine possible
  ternary pair counts remove unsupported endpoint candidates.
* **Hall filtering**: a completion induces a perfect matching between
  remaining placements and patterns. The separate `exact_cover_hall.hpp`
  checks existence and, optionally, removes edges belonging to no perfect
  matching. Its independent exhaustive graph tests are maintained by the
  parent investigation.
* **Exact memoization**: cache the remaining active-candidate bitset after
  propagation. The whole vector is the key; hash collisions are resolved
  by equality, not assumed impossible.
* **Component multiplication**: connect remaining placements if they share
  an available pattern or an unfixed cell. Separate components have
  disjoint choices and multiply. Each must have equally many placement and
  pattern columns. Cell consistency and Hall filtering remain local, while
  the global role quotas and endpoint flow are disabled inside an isolated
  component. A timed-out component product is discarded entirely.

Each branch is disjoint, all pruning is necessary, and memoization and
component multiplication aggregate exact counts. Arithmetic explicitly
throws on unsigned 128-bit overflow rather than silently wrapping.

## Independent validation

`python experiments/exact_cover_check.py` passed:

* The complete binary count is 168 for all three primary branching modes
  and for all optional filters together.
* Each of the sixteen binary first-two-row prefixes agrees separately with
  the independent published row enumerator.
* The two published ternary seven-row prefixes, C and P, each have exactly
  two completions, including with all reductions enabled.
* A fully prescribed valid ternary board has one completion; changing its
  apex yields an independently checked invalid board with zero completions.
* A genuine splice example tests the nontrivial component-product path.
  Two input boards differ in four cells. Direct coordinate enumeration of
  all sixteen assignments finds exactly four valid boards. The solver
  detects two independent components and counts their product, 2 × 2 = 4.

The last fixture is adapted from group 6 (zero-based group 5) in
`splice_witnesses.json`, using its two caps and two tails differing at two
cells each. Their original source and license notices remain in the
repository. `--supports-file` restricts each placement to patterns appearing
there in the given input boards; it is a test-region option, not a claim
about the unrestricted problem. See `exact_cover_product_fixture.txt` and
`exact_cover_check.log`.

## Measured search sizes

All entries below exhaust the same prescribed seven-row region and return
exactly two boards. These are search-node counts; propagation work per node
varies substantially.

| Configuration | Prefix C | Prefix P |
|---|---:|---:|
| Plain adaptive exact cover | 1,310,134 | 4,424,401 |
| Cell consistency and role quotas | 240,219 | 635,457 |
| Plus Hall filtering | 238,157 | 633,501 |
| Cell branching and endpoint flow | 94,470 | 146,231 |
| Cell branching, flow, and Hall | 93,097 | 144,861 |

The strongest reductions cut the node counts by about fourteenfold and
thirtyfold, respectively, but did **not** beat the existing efficient
row-major counter in elapsed time on these two regions. Hall filtering
alone offers little extra pruning here. Strong runs on C and P had no
component splits and no memo hits; a cache therefore adds overhead.

The reproducible fixed-prefix matrix is in `exact_cover_benchmark.json`
and `exact_cover_flow_benchmark.json`; the validation log records the final
all-options runs. Timing varies with concurrent machine load, so the
stable node counts are the main comparison.

## Bounded unrestricted tests

With cell branching, cell consistency, endpoint flow, component detection,
and a 100,000-entry exact memo cache, the unrestricted search visited
574,464 nodes in 15.42 seconds. It found no witness, had no component split,
and had one memo hit. Adding Hall filtering visited 138,240 nodes in
15.03 seconds, also with no witness or component split and one memo hit.
Both runs report `INCOMPLETE`; a zero partial count proves no nonexistence.

The same two configurations did not exhaust the first published six-row
prefix in fifteen seconds either. Their partial counts were zero, they
had no component splits, and each had six memo hits. These observations
provide no evidence that the current implementation can evaluate the
unrestricted count in practical time. Exact component aggregation works
on an explicit splice fixture, but did not arise in these bounded global
runs. Full arguments and results are in `exact_cover_unrestricted.json`.

## Running the counter

```sh
g++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror experiments/exact_cover.cpp -o /tmp/tboard-cover
/tmp/tboard-cover --colors 2 --seconds 30
/tmp/tboard-cover --colors 3 --seconds 15 --branch-cells 1 --flow 1 --hall 81 --components 1 --memo 100000
python experiments/exact_cover_check.py
python experiments/exact_cover_benchmark.py --seconds 15
```

`--hall K` enables Hall filtering when at most K placements remain; zero
turns it off. `--hall-prune 0` checks matching feasibility without removing
unsupported edges. `--cells 1` enables cell consistency without changing the
branch type. `--branch-cells 1` implies cell consistency. `--seconds 0`
requests an unbounded run. `status=COMPLETE` is required for an exact total;
on timeout `count` contains only completed contributions, a lower bound for
that selected search region. The process exits with status 1 for timeout
and status 2 for invalid arguments or arithmetic overflow.
