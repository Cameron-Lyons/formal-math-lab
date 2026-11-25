# Interleaved exact transfer for the final two rows

The recurrence is implemented and independently validated. It consumes
bottom-row patterns while constructing the penultimate row, so impossible
choices can be rejected before a whole penultimate row exists. The measured
benefit is mixed on small fibers. Its integration into the known six-row
138-board fiber did **not** finish within the 90-second wall-time guard.
The unrestricted exact count remains unevaluated.

## Exact recurrence

For ternary boards, fix rows 0 through 7. Write u for the fifteen colors of
row 7 and S for the 32 unused patterns. Let `(a,b)` be the current pair in
row 8 and `(c,d)` the current pair in row 9. At step i, choose new colors
x and y and consume the two distinct patterns

    upper = (u[i], a, b, x)
    lower = (a, c, d, y).

Both must belong to S. Remove them and continue with pairs `(b,x)` and
`(d,y)`. After fifteen such steps, exactly two patterns remain. These are
the last two bottom-row windows, whose top word is `(a,b)` and whose
initial bottom pair is `(c,d)`. Their completion count is obtained directly
from the two remaining pattern masks.

Every middle/bottom-row coloring follows exactly one sequence of choices,
and every complete sequence uses each residual pattern once. The transfer
is therefore an exact count, without restrictions on board shape or colors
beyond those in the original problem. The binary version uses five paired
steps and twelve residual patterns.

## Pruning and exact memoization

The middle row has a prescribed color histogram: the number of residual
patterns with top color t, minus the number of occurrences of t in u.
The counter rejects negative quotas and decrements the remaining quota as
each middle-row cell is selected.

Each residual pattern is also a directed edge from its lower-left pair to
its lower-right pair. Let D be residual outdegree minus indegree. Given
starting pairs v and w, the required multiset of ending pairs is

    E = unit(v) + unit(w) - D.

Every entry of E must be nonnegative; its sum is two. This eliminates
impossible starting-pair choices. The last middle pair must occur in E,
which also restricts the last two middle-cell choices. This last restriction
can be disabled for independent comparison.

The optional memo key contains the actual remaining pattern set, both
current pairs, and the remaining suffix of u. For one fixed u the position
is already determined by the number of remaining patterns. Including the
suffix allows safe reuse across different fixed prefixes. The three fields
occupy 112 bits without overlap; complete-key equality resolves hash
collisions.

Neither the quota nor E needs a separate key field: both are determined by
the residual set, current pairs, and remaining top suffix. In particular,
removing one edge from each path and advancing the two current pairs leaves
E unchanged. This justifies reuse when the same residual state was reached
through different histories.

Counts for a fixed eight-row ternary prefix fit in 64 bits: at most 36 cells
remain, and 3^36 < 2^64. The integrated earlier-prefix counter separately
checks accumulation overflow.

## Independent verification

`python experiments/exact_tworow_check.py` passed:

* All **512 binary three-row prefixes** agree separately with the independent
  published enumerator, including invalid prefixes; their completions sum
  to **168**. This was checked with three memo depths and both settings of
  the final-endpoint pruning.
* Seven ternary eight-row fibers agree with the independent row-major
  counter, with counts ranging from **one to ten**. Their 84 global-color
  and reflection images were tested twice, verifying cross-request reuse,
  again at three memo depths and with endpoint pruning on and off.
* Both complete published seven-row fibers C and P were exhausted by the
  integrated transfer and returned exactly **two** completions each.

See `exact_tworow_check.log`. These are computational checks, not a
kernel-checked theorem about the counting program.

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

These counters do different work per node. The fibers are tiny, so their
microsecond timings should not be generalized into a reliable speed ratio.
They do establish that early bottom-pattern consumption can either reduce
or increase the explored search, depending on the region.

Memoization was slower on these fibers. It found a little multiplicity
sharing—for example, the six-board fiber had twenty hits at full cache
depth—but did not offset lookup and storage costs. The repeated-input
validation intentionally produces more hits; that artificial repetition is
not evidence about a naturally occurring global workload.

`exact_tworow_benchmark.json` records all comparisons.

## Seven-row and six-row integrations

The experimental search copy preserves the original enumeration of earlier
rows and replaces its final-two-row search by this recurrence. No original
source files were edited.

Without memoization, the C fiber made 2,808 transfer requests and explored
2,737,309 interleaved states, finishing in about 0.0477 CPU seconds. The P
fiber made 10,702 requests and explored 1,879,146 states, finishing in about
0.0311–0.0329 CPU seconds. Both counted two boards. Memoization increased
CPU time substantially and found very few reused states. See
`exact_tworow_prefix_benchmark.json` and the validation log.

Because the small-fiber results were mixed and P showed a plausible benefit,
a cache-free integration was then attempted on the established six-row
138-board fiber. It reached the **90-second wall-time limit** and was killed
without an exact count. The previous final-row integration had completed
that fiber, but concurrent machine load changed and the timed-out run's
process CPU was not captured. Therefore this result establishes only that
this integration did not finish within its wall-time allowance; it does
**not** establish a precise CPU slowdown or a numerical speed ratio.

The timeout is explicitly recorded as `INCOMPLETE` in
`exact_tworow_integrated_benchmark.json`. No partial count or new lower bound
is claimed. The recurrence remains correct, but this tested implementation
has not demonstrated a useful improvement for that larger fiber or a path
to the unrestricted total.

## Reproduction

```sh
python experiments/exact_tworow_check.py
python experiments/exact_tworow_benchmark.py
python experiments/exact_tworow_integrated.py
```

The final command compiles the six-row integration and applies a 90-second
wall-time guard. Its current wrapper additionally records child process CPU
for future runs; that measurement was added after the saved timeout and was
not used to infer CPU usage retrospectively.

The standalone transfer reads eight-row ternary prefixes (64 digits), or
three-row binary prefixes (9 digits), one per line:

```sh
g++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror experiments/exact_tworow_count.cpp -o /tmp/tboard-tworow
/tmp/tboard-tworow 3 0 0 90 < eight-row-prefixes.txt
```

Arguments are colors, maximum residual-edge count to memoize, maximum cache
entries, per-prefix time budget, and optionally final-endpoint pruning
(1 by default). Every result carries an explicit `COMPLETE` or `INCOMPLETE`
status. Only `COMPLETE` supplies the exact count of the selected prefix.
The integrated copy defaults to seven prescribed rows; compile with
`-DTWO_START_ROW=6` for six prescribed rows and use an external time guard.
