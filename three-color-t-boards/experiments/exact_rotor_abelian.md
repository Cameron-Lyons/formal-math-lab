# Rotor scheduling: a precise abelian obstruction and an exact bijection

The natural per-triple processor is **not abelian** when its output keeps the
destination cell tag. Even swapping the first two ready updates can turn an
accepted rotor tuple into a rejected one. Still, re-encoding the rotors gives
an exact bijection between accepted tuples for any two valid update orders.
That allows exact search under arbitrary schedules without evaluating the
unrestricted ternary count.

This note builds on [the rotor parametrization](exact_math.md),
[the earlier Euler and last-exit obstructions](exact_structure.md), and
[the sign obstructions](exact_sign_math.md). Here we change the update schedule
while holding the boundary and all rotors fixed.

## Geometry and the failed hypothesis

For `q` colors, a board has `q²+1` rows. Write `U(r,j)` for the update that
fills cell `(r, j+2)` from the already known colors at `(r−1, j)`, `(r, j)`,
and `(r, j+1)`, for `1 ≤ r ≤ q²` and `0 ≤ j ≤ 2r−2`. Initially the apex and the
first two cells of every other row are known, so `U(1,0)` and `U(2,0)` are both
ready at the start and independent of each other. Swapping them in row-major
order produces another valid topological order of the dependency DAG.

In the proposed compressed network, each triple `g = (t, l, m)` is a processor
holding a permutation `σ_g` and a usage counter. When destination cell `v`
requests a color, the processor pops the next color from `σ_g` and sends it to
`v`. For two distinct cells `v, w` and two distinct next colors `a, b`, running
requests `v, w` outputs

```
{(v,a), (w,b)},
```

while running `w, v` outputs

```
{(w,a), (v,b)}.
```

The final counter agrees, but the tagged output multisets differ (whether seen
as distinct letters on a shared port or different colors on separate cell
ports). The processor therefore fails the output-multiset condition in Bond and
Levine's Definition 2.1, so their local-to-global abelian theorem does not
apply here
([Abelian Networks I, §2](https://lionellevine.github.io/abelian-networks-I-foundations.pdf)).

Dropping destination tags would make the local processor unary, but it would
hide which cells get which colors, and those colors choose later input triples.
The concrete boards below show that this changes whether decoding finishes at
all, not just the labeling of interchangeable outputs.

## Two existing boards certify order-dependent acceptance

The checker embeds a known valid binary board and published ternary seed 0 from
`sources/anc/certificates.json`. It checks all patterns from Cartesian
coordinates and extracts their row-major boundary and rotor tables directly,
with no new board search.

In both examples, the first two row-major requests have triple `000`, whose
rotor starts with `0, 1`. Row-major decoding finishes with every triple used
exactly `q` times. Keeping the exact same boundary and rotors and swapping only
the first two updates breaks decoding:

| q | Successful writes in swapped order | First exhausted request |
|---|---|---|
| 2 | `U(2,0):000→0`, `U(1,0):000→1` | `U(2,1)` asks for a third `000` output |
| 3 | `U(2,0):000→0`, `U(1,0):000→1`, `U(2,1):000→2`, `U(2,2):102→2` | `U(3,0)` asks for a fourth `000` output |

Every request is ready when issued, and the swapped schedule is a valid
topological order for any colors. This disproves the hypothesis that **for
fixed boundary colors and fixed local permutations, capacity-respecting
completion is independent of the order of ready updates**. So the existing
rotor decoder cannot be treated as an abelian network with order-independent
completion or odometer data. (This does not rule out a completely different,
richer encoding.)

Full boards, boundary digits, rotor permutations, and failure traces are saved
in [the self-contained audit](exact_rotor_abelian.json). Run or check it with:

```sh
python experiments/exact_rotor_abelian.py
python experiments/exact_rotor_abelian.py --check
```

## Exact positive statement: accepted counts are schedule invariant

Fix **any** topological order `S` of the `q⁴` updates. Given a valid board,
keep its `2q²+1` boundary colors and record each triple's output colors in the
order `S` visits them. Validity ensures every triple's list is a permutation,
and decoding those parameters in order `S` rebuilds the board by induction.

Conversely, if decoding in order `S` finishes without exceeding any triple's
capacity `q`, it makes `q⁴` requests across `q³` triples of capacity `q`, so
every triple is used exactly `q` times. Because each rotor is a permutation,
all `q⁴` patterns appear once, and re-encoding recovers the exact rotors. Thus
accepted parameter tuples for any fixed order `S` are in bijection with valid
boards, keeping the exact unrestricted labeled count `N`.

There is also an explicit local bijection between schedules. Swap two adjacent
incomparable updates; neither changes the other's input triple. If their input
triples differ, keep all rotors unchanged. If both use the same triple `g`,
swap the two matching adjacent entries in `σ_g`. Then both cells get the same
colors as before, leaving every color and counter identical afterward. In the
two examples above, changing only rotor `000` from `01` to `10` (for `q=2`) or
from `012` to `102` (for `q=3`) recovers the original board under the swapped
schedule, as verified by the checker.

The same bijection holds for any deterministic adaptive scheduler that picks
the next ready cell using only the boundary, already filled cell colors, and
already consumed rotor entries and counters. To encode a valid board, run that
scheduler on the board and record the outputs it sees. Because the scheduler
cannot peek at unused rotor entries, encoding is well defined and the inverse
induction still holds. This allows adaptive ready-cell ordering in an
exhaustive search with count multiplier 1, though no runtime gain is proved
here.

## What multivariate inversion would still require

Lagrange-Good inversion is a coefficient formula for an explicit system
`f_i = x_i g_i(f_1, ..., f_m)` whose determinant comes from its Jacobian
([Abdesselam, Theorem 1](https://arxiv.org/pdf/math/0208174)). The rotor
parametrization by itself gives neither such a system nor a coefficient formula
that avoids checking completion.

One clean algebraic limit does follow directly: if a location-based system
follows only the acyclic cell dependency order, so each `g_i` depends only on
earlier `f_j`, then its derivative matrix is strictly triangular and
`det(I−diag(x) Dg) = 1`. Such a system cannot produce a nontrivial determinant
factor for the shared capacities of the 27 rotors. Capturing those shared
capacities would need extra global constraints or a different algebraic system
(which this triangular observation does not rule out).

No 27-type recursive specification, BEST generalization, or tractable
coefficient formula for `N` has been found. The proved results here are the
failure of tagged abelianness and the exact schedule-invariance bijection,
within the scopes stated above.
