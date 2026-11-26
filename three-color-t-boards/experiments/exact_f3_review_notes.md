# Independent natural-characteristic-three review

The frozen natural-`F3` base model and its separate four-cubic augmentation pass independent source and emitted-input checks. Both encode the exact labeled ternary count with divisor and multiplier equal to 1. This review computes no unrestricted count.

## Exact count semantics

Colors are the three elements `0, 1, 2` of `F3`. The Vandermonde matrix evaluating `1, z, z²` at `0, 1, 2` has determinant 2 in `F3` and is invertible, so its fourth tensor power maps the 81 pattern counts mod 3 bijectively to the 81 power moments. Setting every pattern count to 1 gives target moment 0 for every exponent tuple except `(2, 2, 2, 2)`, where the target is 1. Because the constant moment `81 = 0 (mod 3)` holds automatically, the 80 nonconstant equations force every nonnegative pattern count to be `1 (mod 3)`. Each count is therefore at least 1, and summing to 81 forces every count to equal 1.

Before elimination, the signed prefix map is an invertible `F3`-linear transformation. The four unary role equations have rank 4, yielding the four substitutions and a bijection between their solution space and the 96 free prefix coordinates. Over `F3`, every linear form `L = sum(c_i * x_i)` satisfies the ordinary polynomial identity

`L³ - L = sum(c_i * (x_i³ - x_i))`.

The forward and inverse linear maps therefore match the original field-domain ideal to the prefix-coordinate field-domain ideal. Once the four linear equations are solved, the 96 free cubics `x_i³ - x_i` imply all original-cell and eliminated-variable domains, with no nonzero-color restriction (unlike the earlier `F4` root-of-unity model).

Modulo those 96 cubics, the ring splits as a product of copies of `F3`, one per point in `F3^96`. Any ideal in that product is radical and selects a subset of points, so the quotient dimension equals the exact number of valid labeled boards with no hidden multiplicity, scalar-extension factor, or symmetry multiplier. Reducing positive powers via `x³ = x` preserves this ideal because positive exponents map to 1 or 2, never 0.

## Independent base checks

`exact_f3_review.py` rebuilds all 81 T windows from triangular row indices, solves the signed unary equations from scratch, and expands every moment using ordinary tuple monomials before reducing modulo the field cubics (completely separate from the generator's packed-integer code). All 172 exported polynomials and 96,050 moment terms match, including subtraction of the `2222` target.

It also verifies 200 ordinary field-ideal identities, 12 arbitrary free assignments, all 161 witness round trips, the invertible color transform, and rejection of the uniform-triple counterexample (which fails `moment:1,1,1,1`). The backend input matches frozen SHA256 `e9e1163bd047fdca4000333d917a26e37dbf711abebca29d27fae6d49a2c34ba`.

## Four redundant histogram cubics

Every role on a valid board holds 27 copies of each color, giving generating polynomial

`(1 + t)^27 * (1 - t)^27 = (1 - t²)^27 = 1 - t^54` in `F3`,

so `e3 = 0`. For any two role sets `A` and `B`, write `C = A ∩ B`, `D = A\B`, `E = B\A`. From the unary equations, `e1(D) = e1(E) = -e1(C)`, and expanding products gives

`e3(A) - e3(B) - e3(D) + e3(E) = e1(C) * (e2(A) - e2(B))`.

Under `e1 = 0`, Newton's identity in `F3` gives `e2(role) = sum(z²)`, which is already in the base model's quadratic moments. Thus the three boundary differences plus `e3(T)` enforce all four role `e3` equations modulo the base equations. Because they vanish at every valid board in the radical quotient, adding them leaves both the ideal and the quotient dimension unchanged.

`exact_f3_e3_review.py` builds elementary polynomials with an independent truncated product tree and verifies the three exact correction identities, four quadratic identities, 79-pair formula for `e3(T)`, all four emitted cubics, and all 161 witnesses. It also checks all 3,403 role histograms with integer binomial coefficients: `e1 = e2 = 0` leaves 406 histograms, and adding `e3 = 0` leaves 136 (forcing a shared residue of 0, 3, or 6 mod 9, **not** exact balance on its own). The linear span of degree-at-most-3 polynomials rises from rank 26 to rank 30, without implying anything about full-ideal rank.

`exact_f3_e3_adapter_review.py` audits the backend definitions and fresh prepare-only output: the 172 base polynomials stay verbatim, followed by the 4 cubics totaling 574 terms, producing a 96-variable, 176-generator input with SHA256 `cb2497554585e51166b747cee0221efc3cf7f130f46b9084d7f2e9d3b760c105`. It rejects 12 conflicting flag combinations and 6 malformed metadata inputs. None of these three audits runs a solver.

## Explicit translation factor

The translation model writes `z_c = a + d_c`, where `a = z_0` is the apex color and `d_0 = 0`. In signed prefix coordinates, `u_j = y_j - (j + 1)*a`, and `d_0 = 0` becomes `u_8 = u_7`. Solving that along with the four role equations leaves 95 normalized free coordinates, while `a` stays in the ring as `x96` with domain `x96³ - x96`.

For each multi-index `e` and target `t_e`, binomial expansion yields

`M_e(a + d) - t_e = sum_(f <= e) binom(e, f) * a^(|e - f|) * (M_f(d) - t_f)`.

Because the only nonzero target sits at the top index `2222` and `M_0000 = 0`, ordering by total degree gives a unitriangular invertible matrix over `F3[a]`, proving the translated and normalized moment ideals are identical. The field domains stay equivalent under this linear change, and `e3(d + a) = e3(d) + a*e2(d) + a²*e1(d)` preserves the optional `e3` equations modulo the unary conditions.

All normalized moments and cubics avoid `x96`, so the quotient factors as

`normalized quotient tensor_F3 F3[a]/(a³ - a)`.

Its dimension is 3 times the apex-normalized dimension and **already equals the full labeled count**. Divisor and multiplier must both stay 1 (multiplying by 3 again would overcount). Here `a` is an ordinary `F3` variable, not an extension-field generator, and no cell is fixed in the full model.

`exact_f3_translation_review.py` solves all five linear equations independently from geometry, verifies the forward/inverse maps, checks 100 ordinary field identities and all 80 binomial moment identities with tuple polynomials, and matches all 95,490 moment terms and both full exports. The four translated cubics have 156, 174, 86, and 150 terms; their shift identities and all 161 witness round trips pass.

`exact_f3_translation_adapter_review.py` checks both backend prepare-only modes (348 polynomials total), verifies `x96` appears only in its own field cubic, and rejects 24 invalid flag combos plus 4 non-Boolean augmentation flags. Base input SHA256: `339f10f7632c231f4e79a0b5c1e99700798fe7726c3b359ab097611ee650d3b1`; augmented input SHA256: `44e74446e0971a06a40d89fc18446d33e3355d3ef6e42b4197e3ac0686defee5`. Neither audit invokes a solver.

The completed nine-row prefix run is audited independently in `exact_f3_translation_six_review.py` and `exact_f3_translation_six_review_results.json` without re-running the solver. Its 257 generators combine the 176 augmented equations with 81 original-color equations `z_c = a + d_c` (coefficient and augmented rank 80). Since the apex is 1, its equation `2 + x96` pins `a = 1`, collapsing the 3-color factor. The exported basis has 101 leading monomials, and both Python counters give dimension 6 and board count 6 (divisor and multiplier 1). Input SHA256: `3781763a4a35be2f5dc3f2e0da2ea0cecca805e84ccf38a07f6913fafa0f5b1c`; basis SHA256: `7a4362f04fd6df02d469349e7e471b1ea58b5d2f4386261978fc1d0cc3bf6f87`. This checks a fixed fiber only.

## Separate variable-order candidate

`exact_f3_order_review.py` and `exact_f3_order_review_results.json` confirm that `exact_f3_order_selected.ms` is a pure bijective renaming of the translated augmented input. All 176 polynomials and 96,248 terms match, inverse renaming restores the source text byte for byte, all 100 original-color forms verify, and all 161 witnesses round-trip. The independent offset variable stays last in its own field cubic, leaving divisor and multiplier at 1. Input SHA256: `b73bf1f74eb55a2f7e5d2663471021bc8fa3e3250f208d955d8d97bdfa9190bd`; mapping SHA256: `387d85417ffb7823ceef2984b506b39f6913169491d7ada2d75343ec1829bc3e`.

Graph metrics were rebuilt independently using explicit sets: the full polynomial-support graph is `K95` (4,465 edges, width 94 under every order), while the weaker monomial-cooccurrence graph has 868 edges, with width 51 and 2,384 fill edges in natural order and width 37 and 1,077 fill edges under deterministic minimum-fill (matching reverse and minimum-degree figures as well). These metrics describe specific orders on the weaker graph and say nothing about optimal treewidth or Gröbner runtime. No solver ran.

`exact_f3_order_adapter_review.py` and `exact_f3_order_adapter_review_results.json` verify `--native-order minimum-fill` across backend definitions and a fresh prepare-only output, checking all 176 polynomials, all 100 original and normalized color maps, all 95 free-coordinate slots, and all 96 domain labels, while confirming rejection of 17 conflicting option combos, 8 malformed metadata values, and a tampered source input. The prepared command requests a unique completion marker; no solver was launched.
