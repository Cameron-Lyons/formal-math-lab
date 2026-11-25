# Independent natural-characteristic-three review

The frozen natural-F3 base and its separate four-cubic augmentation pass independent source and emitted-input checks. They encode the full labeled ternary count with divisor and multiplier both one. No full count was computed by this review.

## Exact count semantics

The colors are the three elements 0, 1, 2 of F3. The matrix evaluating `1,z,z²` at those colors has determinant 2 in F3 and is invertible. Its fourth tensor power therefore determines all 81 pattern counts modulo three from the 81 power moments. For the table whose counts are all one, the target moment is zero except for exponent vector `(2,2,2,2)`, whose target is one. The constant moment is automatically `81=0` in F3. Thus the 80 nonconstant equations force every nonnegative integer pattern count to be congruent to one modulo three. Each count is at least one; their sum is exactly 81, so every count equals one.

The signed prefix transformation is an invertible F3-linear map before elimination. The four unary role equations have rank four. Solving them gives the stated four substitutions and a bijection between their solution subspace and 96 free prefix coordinates. For every F3-linear form `L=sum(c_i*x_i)`, the ordinary-polynomial identity

`L³-L = sum(c_i*(x_i³-x_i))`

holds. The forward and inverse linear maps therefore identify the original field-domain ideal with the coordinate field-domain ideal. After solving the four linears, the 96 free equations `x_i³-x_i` imply all original-cell and eliminated-coordinate domains. No nonzero-coordinate condition is needed. This differs from the earlier F4 encoding, where original colors were nonzero roots of unity.

The ring modulo the 96 field-domain equations is a product of copies of F3, one for each free-coordinate assignment. Every further ideal in that product is radical and selects a subset of those assignments. The quotient dimension is therefore the number of valid labeled boards, with no hidden multiplicity, scalar-extension factor, symmetry division, or normalization factor. Reducing positive powers by `x³=x` preserves this ideal; a positive exponent always reduces to one or two, never to zero.

## Independent base checks

`exact_f3_review.py` reconstructs all 81 windows directly from triangular row indices, solves the signed unary relations afresh, and expands each complete moment with tuple monomials before reducing by the field domains. This is independent of the source generator's packed-integer multiplication and intermediate reductions. All 172 exported polynomials and 96,050 moment terms match, including the subtraction of the unique nonzero target.

The review also checks 200 ordinary field-ideal identities, twelve arbitrary free assignments, all 161 existing witness coordinate roundtrips, the invertible color transform, and the uniform-triple counterexample. That counterexample fails `moment:1,1,1,1`. Actual backend input matches the frozen input SHA256 `e9e1163bd047fdca4000333d917a26e37dbf711abebca29d27fae6d49a2c34ba`.

## Four redundant histogram cubics

A valid board uses each color 27 times in each role. Its elementary generating polynomial is

`(1+t)^27*(1-t)^27 = (1-t²)^27 = 1-t^54` in F3.

In particular its third elementary symmetric polynomial vanishes. For role sets `A,B`, put `C=A∩B`, `D=A\B`, `E=B\A`. The enforced unary equations give `e1(D)=e1(E)=-e1(C)`. Ordinary product expansion then gives

`e3(A)-e3(B)-e3(D)+e3(E) = e1(C)*(e2(A)-e2(B))`.

Under the unary equations, Newton's identity in characteristic three gives `e2(role)=sum(z²)`. Those four quadratic power moments are already retained in the base model. Consequently the three exported boundary differences, together with `e3(T)`, are equivalent to the four role `e3` conditions modulo the base equations. Since these polynomials vanish at every valid point of the radical finite-field quotient, adding them leaves the quotient, and hence the exact count, unchanged.

`exact_f3_e3_review.py` reconstructs elementary polynomials with an independent truncated product tree. It checks the three exact ordinary correction identities, four quadratic identities, the 79-edge expression for the top role, all four emitted cubics and all 161 witnesses. It also checks all 3,403 possible role histograms using integer binomial coefficients. The unary first and second elementary conditions leave 406 histograms; adding the third leaves 136. This forces a common residue 0, 3 or 6 modulo nine, **not** exact balance by itself. The low-degree polynomial linear span rises from rank 26 to 30; this is not a claim about the rank of the full ideal.

`exact_f3_e3_adapter_review.py` checks the actual backend definitions and a fresh prepare-only output. The 172 base polynomials remain verbatim, followed by exactly four cubics with 574 terms. The resulting 96-variable, 176-generator input has SHA256 `cb2497554585e51166b747cee0221efc3cf7f130f46b9084d7f2e9d3b760c105`. Twelve conflicting model-option combinations and six malformed base metadata cases are rejected. No solver was invoked by any of these three audits.

## Explicit translation factor

The separate translation model writes each original color as `z_c=a+d_c`, where `a=z_0` is the original apex color and `d_0=0`. In signed prefix coordinates, normalization is `u_j=y_j-(j+1)*a`; the condition `d_0=0` is `u_8=u_7`. Solving that condition together with the four role linears leaves 95 normalized free coordinates. The additional independent variable `a` remains in the input as `x96`, with its own field equation `x96³-x96`.

For a multi-index `e` and the corresponding target `t_e`, binomial expansion gives

`M_e(a+d)-t_e = sum_(f<=e) binom(e,f)*a^(|e-f|)*(M_f(d)-t_f)`.

The only nonzero target occurs at the maximal index `2222`, so target subtraction respects this identity. The constant moment is zero. Ordered by total degree, this transformation is triangular with diagonal one, hence invertible over the polynomial ring in `a`; it identifies the original and normalized moment ideals. The field-domain transformation is linear and preserves the field ideal as established above. For each 81-cell role, ordinary elementary expansion also gives `e3(d+a)=e3(d)+a*e2(d)+a²*e1(d)`, so the optional e3 augmentation is preserved modulo the already retained unary conditions.

All normalized moments and optional cubics avoid `x96`. The quotient is exactly

`normalized quotient tensor_F3 F3[a]/(a³-a)`.

Its dimension is three times the apex-normalized dimension and **already equals the full labeled count**. The backend must keep divisor and multiplier one; applying another factor of three would overcount. The parameter is an ordinary F3 color, not an extension-field generator, and no original board cell is fixed in this full input.

`exact_f3_translation_review.py` independently solves all five linear relations from geometry, reconstructs the maps and symbolic inverse, checks 100 ordinary field identities, and verifies all 80 binomial moment identities using tuple polynomials. It matches all 95,490 normalized moment terms and both full exported inputs. The four translated cubics have 156/174/86/150 terms; their ordinary shift identities and all 161 witness roundtrips and evaluations pass.

`exact_f3_translation_adapter_review.py` verifies both actual backend/prepare-only modes, totaling 348 compared polynomials. The 96th variable appears in exactly its own field equation. It rejects 24 conflicting flag combinations and four non-Boolean augmentation options. The base input SHA256 is `339f10f7632c231f4e79a0b5c1e99700798fe7726c3b359ab097611ee650d3b1`; the augmented input is `44e74446e0971a06a40d89fc18446d33e3355d3ef6e42b4197e3ac0686defee5`. No solver was run by these reviews.

The subsequently completed fixed nine-row fixture is independently audited in `exact_f3_translation_six_review.py/results.json`, without repeating its solver run. Its 257 polynomials are exactly the 176 augmented base equations plus 81 original-color fixes using `z_c=a+d_c`. The apex equation is `2+x96`, so the original apex color is fixed to one and the independent three-color factor disappears. The 81 fixes have coefficient and augmented rank 80. The completed marked basis contains 101 leading monomials; both arbitrary-precision counters independently return quotient dimension six and board count six, with divisor and multiplier one. Input SHA256 is `3781763a4a35be2f5dc3f2e0da2ea0cecca805e84ccf38a07f6913fafa0f5b1c`; basis SHA256 is `7a4362f04fd6df02d469349e7e471b1ea58b5d2f4386261978fc1d0cc3bf6f87`. This verifies a fixed fiber and supplies no unrestricted count.

## Separate variable-order candidate

`exact_f3_order_review.py/results.json` independently verifies that `exact_f3_order_selected.ms` is a bijective renaming of the translated augmented input. It checks all 176 polynomials and 96,248 coefficient terms, restores the source text byte for byte under the inverse map, verifies all 100 original-color forms, and roundtrips all 161 existing witnesses. The independent apex variable remains last and appears only in its own field equation. The quotient and the full-count divisor/multiplier of one are unchanged. Input SHA256 is `b73bf1f74eb55a2f7e5d2663471021bc8fa3e3250f208d955d8d97bdfa9190bd`; mapping SHA256 is `387d85417ffb7823ceef2984b506b39f6913169491d7ada2d75343ec1829bc3e`.

The graph metrics were also reconstructed independently with sets and explicit elimination. The full polynomial-support graph is the complete graph on 95 variables, with 4,465 edges and induced width 94 for every order. The weaker graph that connects variables only within individual monomials has 868 edges. Its specified natural order has width 51 and 2,384 fill edges; the deterministic minimum-fill order has width 37 and 1,077 fill edges. Reverse and minimum-degree metrics also match the owner report. These are metrics of particular elimination orders on the weaker graph; they provide no small full factor-graph decomposition, proof of optimal treewidth, or Gröbner-runtime guarantee. No solver was run by this audit.

The implemented `--native-order minimum-fill` path is independently checked in `exact_f3_order_adapter_review.py/results.json`. Actual backend definitions and a fresh prepare-only file match the frozen reordered input. All 176 polynomials, 100 original-color maps, 100 normalized-color maps, 95 free-coordinate positions and 96 field-equation labels are checked against the permutation. The independent offset domain, full labeled scope and divisor/multiplier one are preserved. Seventeen conflicting option combinations, eight malformed required metadata values and a changed source input are rejected. The prepared exact export command requests a unique completion marker; this review starts no solver and computes no full count.
