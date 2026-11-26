# An exact remaining-sign factor in the native F₃ model

A 17-term degree-5 polynomial picks one representative from each global-negation pair in the apex-zero native `F₃` model, expanding to 180 terms in nine prefix variables. Keeping a separate two-valued sign variable alongside the three-valued shift keeps the quotient dimension equal to the **full labeled count N** directly (multiplier and divisor 1). Both the unrestricted count and any runtime impact remain unknown.

## A checked, degree-optimal sign selector

Let `K = F₃[t]/(t⁵ + t⁴ + 2t³ + 2t² + 1)`. The script verifies irreducibility by checking divisibility against every monic polynomial of degrees 1 and 2, then checks all 243 field elements and all 81 inputs to the linear embedding

```
L(T,L,M,R) = T*t + L*(1+t²) + M*(1+t+t²+t³) + R.
```

These four basis vectors are linearly independent. Define

```
h(T,L,M,R) = Norm(K/F₃)(L(T,L,M,R)).
```

As the product of five conjugate linear forms, this norm is a homogeneous quintic (and equals the 121st power on `K`), vanishing on `F₃⁴` only at the origin and obeying `h(-Δ) = -h(Δ)`. Reducing exponents by `x³ = x` leaves 17 monomials of degrees 1, 3, and 5 (the exact coefficients, 38-term homogeneous norm, and embedding vectors live in the model JSON). The checker confirms the exact function-ring identity

```
h(Δ)² = 1 - ∏_(i=0..3) (1 - Δ_i²).
```

Across `F₃⁴`, `h` takes value `1` on 40 inputs, `-1` on 40 inputs, and `0` at the origin. The search tested 240 bases across all 48 irreducible monic degree-5 moduli followed by deterministic shear descents from 24 starting bases, without claiming global minimum sparsity.

No odd selector on `F₃⁴` can have degree below 5. If one had degree at most 4, antisymmetrizing would drop its degree to at most 3, so its square would have degree at most 6. Summing any monomial of degree at most 6 over `F₃⁴` gives 0 (a nonzero sum needs a positive even exponent on all four variables, requiring degree at least 8). Yet the square of any selector equals 1 on 80 points and 0 at the origin, summing to `80 = 2 (mod 3)`, a contradiction.

## Canonical board, independent offset, and independent sign

Take the two T placements with cell indices

```
P0 = (0,1,2,3),   P3 = (3,6,7,8),
Δ(D) = pattern(P0, D) - pattern(P3, D),   in T,L,M,R order.
```

Because a valid board has distinct patterns at `P0` and `P3`, `Δ` is nonzero, so `h(Δ)` is always `1` or `-1`. Given any valid board `z`, set

```
a = z_apex,
D = z - a,
s = h(Δ(D)),
d = s*D.
```

Then `d` is valid with apex 0 and `h(Δ(d)) = 1`. Conversely, any canonical `d` together with `a ∈ F₃` and `s ∈ {1, -1}` reconstructs a unique board via

```
z_cell = a + s*d_cell.
```

Because `h` is odd and `s² = 1`, `s` is recovered uniquely, so every original board appears once. Both finite factors stay inside this export, so multiplying its quotient dimension by 2, 3, or 6 would overcount.

Global negation preserves the native moment ideal because each moment scales by `s` to its total degree and the lone nonzero target (`M_2222`) has even degree 8; the `e3` zero equations are also preserved. After field reduction, every coupled source polynomial has uniform degree parity, which the script verifies directly.

Since every variable keeps its field equation, each quotient is a finite product of copies of `F₃` and remains radical, turning this bijection into the algebra isomorphism

```
A_full ≅ F₃[a]/(a³ - a) ⊗ F₃[s]/(s² - 1) ⊗ A_canonical.
```

We also export the redundant `s³ - s = s(s² - 1)` so every variable visibly has a field cubic. The two independent factors have dimensions 3 and 2 and introduce neither extension fields nor repeated roots.

## Complete separate inputs and reconstruction

Both the natural-order input ([exact_f3_sign_model.ms](exact_f3_sign_model.ms)) and minimum-fill input ([exact_f3_sign_minfill.ms](exact_f3_sign_minfill.ms)) have 97 variables and 179 generators: the 176 frozen translated-plus-`e3` generators followed by `s³ - s`, `s² - 1`, and `h(Δ(d)) - 1`. In zero-based indexing, `0..94` are the normalized prefix coordinates of `d`, `95` is `a`, and `96` is `s`.

The paired JSON files record source hashes, coefficients, forward and inverse maps, and **bilinear original-color polynomials** (replacing the older linear metadata). Any original-color prefix fix must use `a + s*d_cell = color` (for example `a - 1 = 0` for apex 1), and original Gray prefixes rebuild as `Y_j = s*u_j + (j + 1)*a` over `F₃`.

We optimized the selector expansion over signed role permutations across eight low-support placement-pair shapes (covering all pairs whose four difference forms have at most 12 nonzero coefficients, up to ascending-variable relabeling). The winning pair gives 179 terms in `h` and 180 in `h - 1`, supported on 9 variables (support and degree histogram are in the audit). Minimum-fill renaming keeps every term count and degree unchanged and is verified by full inverse permutation.

This adds a nonzero constant term at degree 5 (compared to degree 8 in the source moments), which may help earlier propagation alongside halving the coupled solutions, though an extra quintic can also grow intermediate matrices. No runtime performance is claimed here.

## Reproduction and scope

Run `python experiments/exact_f3_sign.py --check` to rerun the finite-field arithmetic, exports, and [audit](exact_f3_sign_audit.json) without invoking any solver. The check verifies all 81 selector outputs, the square identity, all 243 elements of `K`, verbatim retention of the 176 source equations, all 97 field domains, and `s³ - s = s(s² - 1)`. It also validates 161 known boards geometrically, round-trips their canonical coordinates, checks all six affine-palette reconstructions per board, and evaluates all 179 polynomials on five complete canonical fixtures.

No backend or earlier frozen model was changed, no fixed-prefix solver run was started here, and the unrestricted count remains open.
