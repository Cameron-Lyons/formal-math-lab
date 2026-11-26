# Complete top-T symmetry decomposition

Let `c_r` be the exact number of valid ten-row boards whose **first two rows**
form the four-digit word `r`, read as `(top, left, middle, right)`, with no
other cells fixed. The unrestricted labeled count is

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

Global color permutations and horizontal reflection form `S₃×C₂` (order 12).
Reflection swaps the cap's left and right cells. Both operations preserve board
validity and map fixed-cap fibers bijectively onto one another, so `c_s = c_r`
whenever caps `s` and `r` lie in the same orbit. Splitting all 81 caps into
their ten orbits proves the formula above. **This does not assume that the group
acts freely on caps**: each weight `w_r` is that cap's actual orbit size, not a
uniform factor of 12.

Let `N₀` be the number of valid boards with apex color 0. Cyclic color rotation
gives bijections among the three apex fibers, so

\[
N=3N_0,\qquad N_0=\sum_{r\in R}(w_r/3)c_r.
\]

The subgroup fixing color 0 has order 4, and its ten cap orbits match the
apex-zero column in the table. Do not multiply the first weighted sum by 3
again; that factor is already inside `w_r`.

As optional consistency checks, the **full-board** symmetry action is free, as
proved by `stabilizer_trivial` in [ExactSymmetry.lean](../ExactSymmetry.lean).
That implies `c_0000` is divisible by 4 and every weight-6 fiber count is even.
The cap `0102` is fixed by reflection combined with swapping colors 1 and 2; the
other order-two stabilizers are plain reflection. These divisibility checks
depend on the full-board action and are not needed to prove the weighted sum.

## What the algebraic symmetries add

Let `A` be the full Fourier coordinate algebra over `F_p`, and let `B` be its
apex-one fiber in root-of-unity coordinates (board color 0). Every domain is
`z_v³−1` and every Fourier moment is homogeneous. Put `t = z_apex` and
`y_v = z_v/t = z_v t²`, so `y_apex = 1`. Every moment of degree `d` pulls out
the unit `t^d` times the same moment in `y`, giving an algebra isomorphism

\[
A\cong B\otimes_{F_p}F_p[t]/(t^3-1),
\qquad \dim A=3\dim B.
\]

The full ideal is also graded by total degree modulo 3, and multiplying by the
unit `z_apex` bijects its three graded pieces. That can split linear algebra
into three equal blocks, yielding the same factor of 3 as fixing the apex rather
than a new reduction inside that fiber.

When `p ≡ 2 (mod 3)`, Frobenius sends each color value `z` to `z²`, swapping
colors 1 and 2 while fixing color 0. It keeps the apex-zero fiber fixed as a
set, and acts freely on valid boards because a fixed board would be
monochromatic and invalid. Over `F_p`, the apex coordinate algebra is therefore
a product of quadratic fields, and its Frobenius-fixed subalgebra has half the
dimension. This recovers the known remaining palette factor of 2 without adding
any new color symmetry.

To turn that factor of 2 into explicit board restrictions, we can split the
apex-zero fiber by the first cell with a nonzero board color, fix that cell to
color 1, and multiply the total by 2. Choosing that cell's position is a real
case split. Once a cap already contains two colors, the palette is fixed, so we
cannot divide by Frobenius again inside that fiber. Reflection and combined
stabilizers also have to be handled case by case. Neither homogeneity nor
Frobenius alone yields any extra geometric factorization beyond these symmetry
quotients.

## Scope and completion rule

Computing the exact total from the cap split requires **all ten raw fiber
counts** to finish, with each canonical prefix counted once and no extra
restriction or unaccounted multiplier. A finished standard basis and exact
leading-ideal count qualify even if an optional Hilbert check later times out.
An incomplete basis, out-of-memory failure, partial enumeration, or missing
case never counts as zero; completed cases by themselves give only a lower
bound. Alternatively, a single completed apex-zero count gives `N = 3N₀`, which
must not be added to the overlapping cap sum.

[exact_parity_math_symmetry.py](exact_parity_math_symmetry.py) independently
enumerates all 81 caps, checks every orbit and stabilizer, and checks the
27-cap residual partition. Its [results](exact_parity_math_symmetry_results.json)
contain **no evaluated extension counts**. The parallel aggregation script is
[exact_symmetry_split.py](exact_symmetry_split.py).

The separately audited apex-zero algebra run matched the intended scope: 99
free cells, 99 cubic domains, and all 80 moments, with no extra multiplier. It
ran out of memory before finishing a standard basis, so it does not give `N₀`.
See [the input/status audit](exact_parity_math_apex_audit.json).
