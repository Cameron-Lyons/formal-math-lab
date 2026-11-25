# An exact remaining-sign factor in the native F₃ model

A 17-term polynomial of degree five selects one board from each global-negation
pair in the apex-zero native model. Its equation expands to 180 terms in nine
of the current prefix variables. Retaining a separate two-valued sign variable
and the existing three-valued offset gives the **full labeled count N** as the
quotient dimension, with multiplier and divisor one. This is an exact change
of representation; the count and any runtime benefit remain unevaluated.

## A checked, degree-optimal sign selector

Let K=F₃[t]/(t⁵+t⁴+2t³+2t²+1). The generator checks irreducibility by division
by every monic polynomial of degrees one and two: every reducible degree-five
polynomial has such a factor. It also checks all 243 field elements and the
81 inputs to the following injection:

```
L(T,L,M,R) = T*t + L*(1+t²) + M*(1+t+t²+t³) + R.
```

The four displayed basis vectors are linearly independent. Define

```
h(T,L,M,R) = Norm(K/F₃)(L(T,L,M,R)).
```

The norm is the product of five conjugate linear forms, hence an ordinary
homogeneous quintic. It equals the 121st power on field elements. Its only
zero on F₃⁴ is the origin, and h(−Δ)=−h(Δ). Reducing powers by x³=x gives
17 monomials, with degrees one, three and five. The exact coefficients,
38-term homogeneous norm, and four embedding vectors are in the model JSON.
The checker verifies the full function-ring identity

```
h(Δ)² = 1 − ∏_(i=0..3) (1−Δ_i²).
```

There are exactly 40 inputs with value one, 40 with value minus one, and one
zero. The norm search examined 240 coordinate bases across all 48 irreducible
monic degree-five moduli, then made deterministic elementary-shear descents
from 24 starting bases. This is not a global sparsity optimum.

Degree five is optimal for any odd selector on all of F₃⁴. If such a function
had a polynomial representation of degree at most four, antisymmetrizing it
would give one of degree at most three. Its square would have degree at most
six. Summing each monomial over F₃⁴ gives zero: a nonzero sum needs a positive
even exponent in every variable, requiring total degree at least eight.
But the square of a selector is one on 80 inputs and zero at the origin, so
its sum is 80=2 in F₃, a contradiction.

## Canonical board, independent offset and independent sign

Use the two geometric T placements with original cell indices

```
P0 = (0,1,2,3),   P3 = (3,6,7,8),
Δ(D) = pattern(P0,D) − pattern(P3,D),   in T,L,M,R order.
```

Every valid board has distinct patterns at these two placements. Thus Δ is
nonzero, and h(Δ) is always one or minus one. For an original board z, set

```
a = z_apex,
D = z−a,
s = h(Δ(D)),
d = s*D.
```

Then d has apex zero, is valid, and h(Δ(d))=1. Conversely, from any canonical
d and independent a∈F₃, s∈{1,−1}, recover exactly one original board by

```
z_cell = a + s*d_cell.
```

The sign is recovered uniquely because h is odd and s²=1. Every original
board is therefore represented exactly once. In particular, this export
retains both finite factors; multiplying its quotient dimension by two,
three, or six would be incorrect.

Global negation preserves the native moment ideal: each moment scales by
s raised to its total exponent, and the sole nonzero target has even degree
eight. The existing elementary-cubic equations also preserve their zero sets.
After field reduction every term in each source coupled polynomial still has
the same degree parity; the generator checks this directly.

All individual field equations are retained. Every quotient is consequently
a finite product of F₃'s, and every added ideal remains radical. The explicit
bijection therefore gives an algebra isomorphism

```
A_full ≅ F₃[a]/(a³−a) ⊗ F₃[s]/(s²−1) ⊗ A_canonical.
```

The redundant ordinary identity s³−s=s(s²−1) justifies also exporting s³−s,
so the input visibly contains a field equation for every variable. The two
independent factors have dimensions three and two; neither is an extension
field or a multiplicity caused by repeated roots.

## Complete separate inputs and reconstruction

The natural-order and minimum-fill inputs each contain 97 variables and
179 generators: all 176 frozen translated-plus-e3 generators, followed by
s³−s, s²−1, and h(Δ(d))−1. The independent offset remains index 95 and the
new independent sign is index 96 (zero-based). The first 95 variables are the
existing normalized prefix coordinates of the **canonical** d.

The complete inputs are [natural order](exact_f3_sign_model.ms) and
[minimum-fill order](exact_f3_sign_minfill.ms). Their adjacent JSON files
record source hashes, coefficients, coordinate maps, inverse maps, and
**bilinear original-color polynomials**. They do not reuse the old linear
original-color metadata. An original-color prefix fix must be imposed as
`a+s*d_cell=color`; for example an original apex-one fix is `a−1=0`.
Original Gray prefixes reconstruct as `Y_j=s*u_j+(j+1)*a` in F₃.

The selector expansion was optimized over signed role permutations for eight
low-support placement-pair shapes. These represent all pairs whose four
current difference forms have at most 12 nonzero coefficients, modulo an
ascending-variable relabeling. The selected pair gives 179 terms in h and
180 in h−1. Its nine-variable support and degree histogram are recorded in
the audit. Minimum-fill renaming changes no term count or polynomial degree;
its complete inverse permutation is checked for every generator.

This adds a nonzero constant at degree five. In the source native moments,
the only nonzero target occurs at degree eight. That may improve propagation
before a degree-eight step, in addition to selecting half the coupled
solutions. An extra quintic can also increase intermediate basis growth;
these files provide no runtime evidence either way.

## Reproduction and scope

Run `python experiments/exact_f3_sign.py --check` to reproduce the finite
arithmetic, symbolic exports and hash audit. The generator never invokes a
solver. The audit checks all 81 selector values, the square identity, all 243
extension-field elements, exact retention of the source equations, all 97
field domains, and the ordinary redundancy identity for the sign domain.
It independently checks the geometric validity of 161 existing boards,
round-trips their canonical coordinates, and checks all six affine-palette
reconstructions for each. All 179 exported polynomials are additionally
evaluated on five complete canonical fixtures.

The saved [audit](exact_f3_sign_audit.json) contains every export hash. No
backend or frozen earlier model is modified, no fixed-prefix trial is run,
and no unrestricted solution count is claimed.
