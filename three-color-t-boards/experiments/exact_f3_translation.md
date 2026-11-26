# Exact translation factorization of the natural F₃ ideal

The unrestricted native-field quotient factors as

```
F₃[a]/(a³ - a) ⊗_(F₃) A₀,
```

where `A₀` is the quotient for valid boards with apex color 0. Because the frozen exports keep the independent offset variable `a` in the ring, their quotient dimension equals the **full labeled count N** directly (multiplier and divisor 1), with 95 coupled variables and 1 independent variable. The unrestricted dimension is not computed here. A separate [bounded fixed-prefix run](exact_f3_translation_six.md) finished and reproduced the known 6 completions, keeping all 96 variables and pinning `a` via the original apex color.

## The moment ideal separates from the offset

Write `a = z_apex` and `d_v = z_v - a`, so `d_apex = 0`. This maps the 100 cell colors invertibly to `a` and the 99 normalized colors. For each exponent tuple `e ∈ {0, 1, 2}⁴`, binomial expansion gives

```
M_e(a + d) = Σ_(f ≤ e) binom(e, f) a^(|e - f|) M_f(d).
```

The target `t_e` equals 1 only at the maximal vector `2222` and 0 everywhere else, so the `f = 2222` term appears only when `e = 2222` (with coefficient 1), giving

```
M_e(a + d) - t_e
 = Σ_(f ≤ e) binom(e, f) a^(|e - f|) (M_f(d) - t_f).
```

With `M_0000 = 81 = 0`, the remaining 80 equations transform by a unitriangular matrix whose inverse shifts by `-a`. Thus the translated and normalized moment ideals are equal over the polynomial ring itself, even though individual moments shift.

The field domains separate too:

```
(a + d_v)³ - (a + d_v) = (a³ - a) + (d_v³ - d_v).
```

The apex domain gives `a³ - a`, and subtracting it from every other cell's domain gives `d_v³ - d_v`. The four unary role sums ignore `a` because each role has 81 cells and `81a = 0` in `F₃`.

Applying the invertible signed prefix map and four unary eliminations to `d` turns the coupled part into the normalized moment ideal in 95 free prefix variables with their field cubics, giving the tensor factorization above. Since `F₃[a]/(a³ - a)` has dimension 3, `N = 3 * dim(A₀)`. Because `a` stays in the exported ring, **do not multiply its quotient dimension by 3 again**.

## Exact coordinates and the independent variable

Using the same Gray cell order and signed prefixes as [exact_f3_math.md](exact_f3_math.md),

```
u_j = Σ_(k ≤ j) d_order[k],
d_order[j] = u_j - u_(j-1).
```

Because the apex sits at index 8 in Gray order, `d_apex = 0` means `u8 = u7`. Removing index 8 from the native model's 96 free indices leaves 95 free variables in ascending order, and the four unary eliminations become

```
u80 = 0,
u16 = u97,
u81 = -u7 + u72 + u98,
u99 = -u7 + u9 - u65 + u82.
```

Variables `x1, ..., x95` are those normalized free prefixes, and `x96` is `a`. Original colors rebuild as `a + d_v`, and original prefixes rebuild as `u_j + (j + 1)*a` (so the original apex equals `a`, not 0). The script checks both inverse maps symbolically.

All 96 field cubics stay in the file, including `x96³ - x96`, while every moment and optional `e3` cubic uses only `x1, ..., x95`. Here `x96` is a three-valued `F₃` factor, not an extension-field generator or repeated root.

## Native cubic consequences separate as well

For any 81 colors over `F₃`,

```
e3(z + a) = e3(z) + a*e2(z) + a²*e1(z),
```

since `binomial(81, 3) = 0`, `binomial(80, 2) = 1`, and `79 = 1 (mod 3)`. Because the base unary equations already force `e1 = e2 = 0`, the four role `e3` equations and their boundary differences are shift-invariant modulo the base ideal, preserving the same tensor factorization in the separate cubic export.

## Symbolic comparison

| Quantity | Native prefix model | Translation-separated model |
|---|---:|---:|
| Coupled variables | 96 | 95 |
| Independent offset variables | 0 | 1 |
| Field-domain terms | 192 | 192 |
| Retained moment terms | 96050 | 95490 |
| Four optional `e3` terms | 574 | 566 |
| Degree-at-most-three moment span rank | 26 | 26 |
| That rank with `e3` added | 30 | 30 |

Both base files have 172 generators (176 with `e3`), normalized cubic supports are `156, 174, 86, 150`, and moment degrees still run from 2 to 8. The term reduction is small, with no claimed basis speedup.

## Frozen artifacts and verification

- [Model JSON](exact_f3_translation_model.json), SHA256 `1e2dc884f8996c6bd1b5093f24fa6fe7d7f1002e97b69762baadfda5adf94a7f`.
- [Base polynomial input](exact_f3_translation_model.ms), SHA256 `339f10f7632c231f4e79a0b5c1e99700798fe7726c3b359ab097611ee650d3b1`.
- [Separate cubic augmentation](exact_f3_translation_e3_constraints.json) and [augmented input](exact_f3_translation_e3.ms).
- [Generator and checker](exact_f3_translation.py) and [audit with all hashes](exact_f3_translation_audit.json).

The script rebuilds normalized moments from scratch and matches setting `y8 = y7` in the native model, verifies all 80 binomial shift identities directly on `a + d` (including `M_2222 - 1`), checks the field-domain and `e3` shift identities as ordinary polynomials, tests 12 arbitrary normalized assignments across all three shifts, and round-trips 161 valid boards.

No backend or older model was altered, and the unrestricted count stays open.
