# Complete top-T symmetry decomposition

Let `c_r` be the exact number of valid ten-row boards whose **first two rows**
are the four-digit word `r`, read as `(top,left,middle,right)`. No other cells
are fixed. The unrestricted labeled count is exactly

\[
\boxed{N=\sum_{r\in R}w_r c_r}.
\]

| Representative `r` | Weight `w_r` | Apex-zero weight `w_r/3` | Cap stabilizer order |
|---|---:|---:|---:|
| 0000 | 3 | 1 | 4 |
| 0001 | 12 | 4 | 1 |
| 0010 | 6 | 2 | 2 |
| 0011 | 12 | 4 | 1 |
| 0012 | 12 | 4 | 1 |
| 0101 | 6 | 2 | 2 |
| 0102 | 6 | 2 | 2 |
| 0111 | 6 | 2 | 2 |
| 0112 | 12 | 4 | 1 |
| 0121 | 6 | 2 | 2 |
| **Total** | **81** | **27** | |

Global palette permutations and horizontal reflection form `S₃×C₂`, of order
12. Reflection swaps the cap's left and right entries. Both operations
preserve validity and give bijections between fixed-cap fibers. Therefore
`c_s=c_r` whenever caps `s,r` lie in the same orbit. Partitioning all 81 caps
into their ten orbits proves the displayed sum. **This does not assume that
the group acts freely on caps**: the weights are their actual orbit sizes,
not uniformly twelve.

Let `N₀` count all valid boards with apex color zero. Cyclic palette rotation
gives bijections among the three apex fibers, so

\[
N=3N_0,\qquad N_0=\sum_{r\in R}(w_r/3)c_r.
\]

The residual group fixing color zero has order four. Its ten cap orbits are
exactly the apex-zero parts of the table. Do not multiply the first weighted
sum by another three: that factor is already in `w_r`.

As optional consistency checks, the **full-board** action is free, as proved
by `stabilizer_trivial` in [ExactSymmetry.lean](../ExactSymmetry.lean). Hence
`c_0000` is divisible by four, and each fiber with weight six has even count.
The cap `0102` is fixed by the combination of reflection and the color-1/2
swap; most other order-two stabilizers are plain reflection. These divisibility
checks concern the action on full extensions and are not needed to justify
the weighted sum.

## What the algebraic symmetries add

Let `A` be the full Fourier coordinate algebra over `F_p`, and let `B` be its
apex-one fiber in root-of-unity coordinates (board color zero). Every domain
is `z_v³−1` and every Fourier moment is homogeneous. Write `t=z_apex` and
`y_v=z_v/t=z_v t²`; then `y_apex=1`. Each moment of degree `d` becomes the unit
`t^d` times the corresponding moment in `y`. Consequently there is an actual
algebra isomorphism

\[
A\cong B\otimes_{F_p}F_p[t]/(t^3-1),
\qquad \dim A=3\dim B.
\]

The full ideal is also graded by total degree modulo three; multiplication
by the unit `z_apex` bijects its three graded pieces. This can organize linear
algebra into three equal blocks, but gives precisely the same factor three
as fixing the apex, not another reduction of that fiber.

For `p≡2 mod3`, Frobenius sends every color value `z` to `z²`, exchanging
colors one and two while fixing color zero. It preserves the apex-zero fiber.
A fixed board would be monochromatic, hence invalid, so this involution is
free on valid boards. Over `F_p` the apex coordinate algebra is therefore a
product of quadratic fields; its Frobenius-fixed algebra has half the
dimension. This recovers the already-known remaining palette factor two.
It does not produce an additional color symmetry.

To realize this second quotient by explicit board restrictions, one can
partition the apex-zero fiber by the first cell with nonzero board color,
require that cell to have color one, and multiply the resulting sum by two.
The position of that cell is a genuine case split. A cap already containing
two colors generally fixes the palette, so Frobenius cannot be divided out
again inside each such fiber. Reflection and any remaining combined
stabilizers must likewise be handled explicitly. No independent geometric
factorization or reduction beyond these existing symmetry quotients follows
from homogeneity or Frobenius alone.

## Scope and completion rule

An exact total from the cap decomposition requires **all ten raw fiber counts**
to be complete, with each canonical prefix present exactly once and with no
hidden additional restriction or unaccounted multiplier. A completed standard
basis and complete exact leading-ideal count qualify even if an optional
later Hilbert calculation times out. An incomplete basis, memory exhaustion,
partial enumeration, or missing case does not supply zero for that case.
Complete cases alone provide a lower bound. Alternatively, one completed
apex-zero count suffices via `N=3N₀`; it must not be added to the overlapping
cap sum.

[exact_parity_math_symmetry.py](exact_parity_math_symmetry.py) independently
enumerates all 81 caps, verifies every orbit and stabilizer, and verifies the
27-cap residual partition. Its [results](exact_parity_math_symmetry_results.json)
contain **no evaluated extension counts**. The parallel aggregation
implementation is [exact_symmetry_split.py](exact_symmetry_split.py).

The separately audited apex-zero algebra trial did have exactly the intended
scope: 99 free cells, 99 cubic domains, and all 80 moments, with no additional
multiplier. It exhausted memory before a standard basis, so does not provide
`N₀`. See [the input/status audit](exact_parity_math_apex_audit.json).
