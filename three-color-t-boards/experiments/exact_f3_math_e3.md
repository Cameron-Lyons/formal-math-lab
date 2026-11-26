# Four sparse cubic histogram consequences for the natural F₃ model

Four redundant cubic equations add just **574 terms** to the [frozen natural-field model](exact_f3_math.md), with no extra variables or domain equations. They are stored separately so the base model and its bytes stay untouched.

Augmentation file: [exact_f3_math_e3_constraints.json](exact_f3_math_e3_constraints.json), SHA256 `6cef0fb4e6b3ccb80f17f7aebadfd02fd777d082e1dedb84cdf5d9786d408392`, pinned to base JSON SHA256 `fe1321842be3bf5bdb8ff91cd5b9c38017d542968fe27a8d5a8952e344564cc4`.

| Label | Original-cell polynomial | Terms in the 96 prefix variables |
|---|---|---:|
| `e3:T` | `e3(T)` | 158 |
| `e3:T:M` | `e3(T\M) - e3(M\T)` | 180 |
| `e3:M:L` | `e3(M\L) - e3(L\M)` | 86 |
| `e3:M:R` | `e3(M\R) - e3(R\M)` | 150 |

Every exported term has degree 3 and coefficient 1 or 2 in `F₃`. Because cubing is the identity on `F₃`, there are no Frobenius partners.

## Validity and the available quadratic conditions

In every role of a valid board, each color `0, 1, 2` appears 27 times. Over `F₃`, the elementary generating polynomial is

```
∏_cells (1 + z*t) = ((1 + t)(1 - t))^27 = (1 - t²)^27 = 1 - t^54,
```

so `e3 = 0`.

The base model already contains `p1 = Σz = 0` and `p2 = Σz² = 0` for each role. Newton's identity `2e2 = p1² - p2` reduces modulo `p1 = 0` to **`e2 = p2` in F₃**, so all four role `e2` equations are already built into the base model (nothing is borrowed from characteristic 2).

## Exact role-difference certificate

For two role sets `A` and `B`, write `C = A ∩ B`, `D = A\B`, `E = B\A`, and `s = e1(C)`. From the unary equations, `e1(D) = e1(E) = -s`, and expanding disjoint unions gives

```
e3(A) - e3(B) - e3(D) + e3(E) = s * (e2(A) - e2(B)).
```

The generator verifies this as an ordinary polynomial identity in the signed prefix coordinates. Because the right-hand side is already a combination of base quadratic moments, the three boundary differences in the table together with `e3(T)` enforce all four role `e3` equations.

## Why the top equation is local

The first 81 cells in Gray order are the top role. Writing `z_i = p_i - p_(i-1)` with `p_0 = p_81 = 0` gives the identity

```
e3(z_1, ..., z_81)
 = Σ_(i=1..79) (p_i² * p_(i+1) - p_i * p_(i+1)²).
```

To prove it without dividing by 3 in `F₃`, work first over the integers: because `Σz_i = 0`, Newton's identity gives `3e3 = Σz_i³`, expanding `(p_i - p_(i-1))³` telescopes the pure cubes to leave 3 times the sum above, and only after canceling 3 over the integers do we reduce mod 3.

All 80 interior prefix variables remain distinct after the other unary eliminations, so the 79 adjacent pairs give 158 cubic terms. The code also expands `e3` directly from the generating product and matches every term.

## Strength and scope of the extra equations

For any nonnegative color-count triple summing to 81, `e1 = e2 = 0` forces all three counts to be multiples of 3 (`3m_c`). Then `e3 = m_1 - m_2 (mod 3)`, so `e3 = 0` forces all three counts to share the same residue **0, 3, or 6 modulo 9** (not necessarily 0). Checking all 3,403 triples confirms 406 pass `e1 = e2 = 0` and 136 also pass `e3 = 0`.

After field reduction, the 26 base moment generators of degree at most 3 have `F₃`-linear rank 26, and adding these four cubics raises that rank to 30 (a linear-span check only, saying nothing about higher-degree cancellations).

Because the base quotient is a radical product of copies of `F₃` indexing all valid boards, and every cubic here vanishes on all valid boards, all four cubics already belong to the base ideal. Adding them leaves the ideal, quotient dimension, and unrestricted labeled count unchanged, with no prefix or symmetry normalization.

[exact_f3_math_e3.py](exact_f3_math_e3.py) also checks all 161 existing valid boards, and [exact_f3_math_e3_audit.json](exact_f3_math_e3_audit.json) stores all identities, degree counts, rank checks, histogram counts, and hashes. Reproduce without a solver:

```sh
python experiments/exact_f3_math_e3.py --check
```

No basis computation or unrestricted count is claimed here.
