# Rotor scheduling: a precise abelian obstruction and an exact bijection

The natural processor for each input triple is **not abelian** when its output
retains the destination cell. Even swapping two initially ready cell updates
can change a fixed rotor tuple from accepted to rejected. However, re-encoding
the rotors gives a bijection between accepted tuples for any two fixed legal
update orders. This distinction permits exact search with different schedules;
it does not evaluate the unrestricted ternary count.

This note follows [the rotor parametrization](exact_math.md),
[the earlier Euler/last-exit obstructions](exact_structure.md), and
[the sign obstructions](exact_sign_math.md). The new test changes the update
order while keeping both the boundary and every rotor fixed.

## Geometry and the precise failed hypothesis

For `q` colors there are `q²+1` rows. Write `U(r,j)` for the update that fills
cell `(r,j+2)` from the already known colors at `(r−1,j),(r,j),(r,j+1)`.
Here `1≤r≤q²` and `0≤j≤2r−2`. Initially the apex and the first two cells of
every other row are known. Thus `U(1,0)` and `U(2,0)` are both initially ready
and neither depends on the other. Interchanging these first two updates in
row-major order produces another topological order of the same dependency DAG.

The proposed compressed network has one processor for each triple `g=(t,l,m)`.
It stores a permutation `σ_g` and a usage counter; a request from destination
cell `v` consumes the next color and sends it to `v`. For different destinations
`v,w` and two different next colors `a,b`, processing requests `v,w` produces

```
{(v,a), (w,b)},
```

whereas processing `w,v` produces

```
{(w,a), (v,b)}.
```

The final local counter agrees, but the tagged output multisets do not. These
are distinct letters if all cells share an output port; alternatively, the
output at each cell's separate port differs. Thus the processor fails the
output-multiset condition in Bond–Levine's Definition 2.1. Their local-to-global
abelian theorem does not apply to this representation.
([Abelian Networks I, §2](https://lionellevine.github.io/abelian-networks-I-foundations.pdf))

Erasing destination tags would make this particular local processor unary,
but would discard which cells receive which colors. Those assignments determine
future input triples. The following actual-board examples demonstrate that the
discarded information affects completion, not just the names of otherwise
interchangeable outputs.

## Two existing boards certify order-dependent acceptance

The checker embeds a previously used valid binary board and published ternary
seed 0 from `sources/anc/certificates.json`. It verifies all patterns by Cartesian
coordinates and derives their row-major boundary and rotor data independently.
No new board search is involved.

In both examples the first two row-major requests have triple `000`, and its
rotor starts with outputs `0,1`. The row-major decoder finishes with every
triple used exactly `q` times. Keep those exact parameters and swap only the
first two scheduled updates:

| q | Successful writes in swapped order | First exhausted request |
|---|---|---|
| 2 | `U(2,0):000→0`, `U(1,0):000→1` | `U(2,1)` asks for a third `000` output |
| 3 | `U(2,0):000→0`, `U(1,0):000→1`, `U(2,1):000→2`, `U(2,2):102→2` | `U(3,0)` asks for a fourth `000` output |

Each request is geometrically ready when made. The complete modified schedule
is topological independently of any colors. Consequently the following precise
hypothesis is false: **for fixed boundary colors and fixed local permutations,
capacity-respecting completion is independent of the order of ready updates.**
This excludes treating the existing rotor decoder as an abelian network with
order-independent completion/odometer data. It does not exclude an entirely
different, richer encoding.

Full boards, boundary digits, all rotor permutations, and the short failure
traces are in [the self-contained audit](exact_rotor_abelian.json). Reproduce or
verify it with:

```sh
python experiments/exact_rotor_abelian.py
python experiments/exact_rotor_abelian.py --check
```

## Exact positive statement: accepted counts are schedule invariant

Fix **any** topological order `S` of the `q⁴` updates. Given a valid board, keep
its `2q²+1` boundary colors and, for every triple, record its output colors in
order `S`. Validity means these are permutations. Decoding these parameters in
order `S` reconstructs the board, by induction through the updates.

Conversely, if a decoder in order `S` finishes without exceeding any triple's
capacity `q`, it performs `q⁴` requests across `q³` capacities of `q`; hence
each triple is used exactly `q` times. Its outputs are a permutation, so all
`q⁴` patterns occur exactly once. Re-encoding recovers every rotor entry.
Thus the accepted parameter tuples for order `S` are in bijection with the
valid boards, and their number is the same unrestricted labeled count `N`.

There is also a local description of the bijection between schedules. Swap
two consecutive incomparable updates. Their input triples are unaffected by
the swap. If different, leave all rotors unchanged. If equal to `g`, swap the
two corresponding consecutive entries of `σ_g`. The cell outputs are then
unchanged; after the pair, all colors and counters agree, so the remaining
decode is identical. In the two fixtures above, changing just rotor `000` from
`01` to `10`, or from `012` to `102`, restores the original board under the
swapped schedule. The checker verifies this exactly.

The board/tuple bijection also holds for a fixed deterministic scheduler that
chooses a ready cell using only the boundary, already revealed cell colors,
and consumed rotor entries/counters. To encode, run that policy on the valid
board and record the observed outputs. It cannot inspect unused rotor entries:
that restriction makes the encoding simulation well defined. The inverse
induction is unchanged. This allows adaptive ready-cell order in an exhaustive
decoder, with no count multiplier. No runtime improvement is established here.

## What multivariate inversion would still require

Lagrange–Good inversion is a coefficient identity for an explicitly established
system `f_i=x_i g_i(f_1,…,f_m)`; the determinant uses its derivative matrix.
A rotor parametrization by itself supplies neither such a system nor a
coefficient whose extraction avoids testing completion.
([Abdesselam, Theorem 1](https://arxiv.org/pdf/math/0208174))

One limited algebraic observation is rigorous: if a proposed location-based
system follows only the acyclic cell dependency order, so each `g_i` depends
only on preceding `f_j`, its derivative matrix is strictly triangular.
Consequently `det(I−diag(x) Dg)=1`. That construction cannot introduce a
nontrivial determinant correction for the shared capacities of the 27 rotors.
Representing those capacities or correlations would require additional global
constraints or a different system; the triangular statement does not rule
such systems out.

No valid 27-type recursive specification, BEST generalization, or tractable
coefficient extraction for `N` has been derived. The new proven conclusions
are the explicit failure of tagged abelianness and the exact scheduling
bijection, with their stated scopes.
