# Independent prefix-coordinate audit

The frozen prefix model, exporter, and all eight backend preparation modes pass
review. This audit runs no solver and produces no full count. Results and fresh
prepared inputs are saved in `exact_pivot_review_prefix_results.json` and
`exact_pivot_review_prefix_prepared/`.

Frozen model SHA256:
`7f8251ab52e8d6869c19cc861dc98b0c1e66904313b0d87920d9f95659700092`.

## Quotient isomorphism

The recorded cell order permutes all 100 original cells. Define
`y_j = sum_(k<=j) z_order[k]` over F2; its inverse is
`z_order[j] = y_j + y_(j-1)` with `y_-1 = 0`. These triangular linear maps are
inverse polynomial-ring isomorphisms (not a quotient or symmetry reduction),
and the audit verifies their composition on all 100 coordinate basis vectors.

Rebuilding the 81 placements from row indices gives transformed unary supports
`[80]`, `[16, 97]`, `[8, 72, 81, 98]`, and `[7, 9, 65, 82, 99]`. Independent
Gaussian elimination gives

```
y80 = 0
y16 = y97
y81 = y8 + y72 + y98
y99 = y7 + y9 + y65 + y82.
```

Eliminating these four variables leaves 96 free prefix coordinates. Every
original domain and Fourier equation is rewritten through this map, so the
resulting quotient is isomorphic to the original full quotient. Its dimension
stays equal to the unrestricted labeled count, with divisor 1 and multiplier 1.

## Domain and Frobenius semantics

The kept domains are all 100 polynomials `L_cell(y)^3+1`, where `L_cell` is the
linear form for an original cell color. They are not 96 blanket equations
`y_i^3+1`, because prefix coordinates can equal zero: the five published boards
have `24, 23, 24, 24, 21` zero free prefix coordinates while satisfying every
exported equation. Two original color forms happen to be single-variable, so
their transformed domains are single-variable cubics and are kept as valid
original-color constraints.

The audit uses ordinary tuple-monomial arithmetic, without reducing exponents
modulo 3 or assuming Boolean variables in the prefix ring. It rebuilds all 100
domain polynomials, all 72 nonzero Fourier moments, and all eight elementary
constraints from scratch. Exactly the eight unary moments vanish under the
linear substitutions. Elementary Frobenius partners are ordinary squares with
fourth powers kept. The representative convention still holds because missing
partners follow by squaring and applying the transformed original color
domains, without assuming any prefix variable is nonzero.

The 96 optional field equations `y_i^4+y_i` remain valid even when `y_i = 0`.
Before linear elimination, each is an explicit ideal consequence:

```
y_j^4+y_j = sum_(k<=j) z_order[k] * (z_order[k]^3+1).
```

The audit verifies this polynomial identity symbolically after substitution for
all 100 prefix indices, including the four eliminated ones, instead of just
testing finite-field points. Adding these equations therefore preserves the
ideal, its multiplicities, and its quotient dimension. No field-extension
variable is needed in the unrestricted model.

## Export and adapter checks

`exact_pivot_review_prefix.py` derives the global-`y` forms first and then maps
them to the ascending `free_prefix_variables` list. Keeping those indices
distinct matters because `original_color_linear_forms` uses global prefix
indices, while solver variables `x1` through `x96` index the free list. Every
packed source polynomial and every emitted solver polynomial is verified
against the rebuilt ordinary expression.

All eight combinations of representative/all moments, optional elementary
equations, and optional quartic field equations were checked through both the
standalone exporter and `exact_msolve_backend.definitions` and prepare-only
paths. Every input keeps all 100 transformed original domains plus 36 or 72
moments; the optional groups add 8 or 96 equations, giving generator counts
136, 144, 232, 240 and 172, 180, 268, 276. The backend keeps unrestricted scope
and divisor 1, marks every run `PREPARED_NOT_RUN` with no basis or count, and
rejects seven invalid scope/option combinations. The subprocess entry point is
mocked to fail immediately if any preparation tries to launch a solver.

Independent checks cover 276 source-polynomial comparisons, 100 inverse
coordinate basis checks, 100 symbolic optional-field identities, 20 arbitrary
F4 coordinate assignments, and all five published valid witnesses. The owner
also ran small complete coordinate fixtures separately; those solver runs are
not claimed as independent runs of this audit.

## Completed transformed nine-row fiber

The owner ran the known fixed nine-row fiber once with all moments, the
elementary equations, and the optional quartics. That input has 97 variables:
the 96 free prefix coordinates plus a coefficient-extension variable `a`. It
keeps all 276 full transformed generators, adds 81 original-color equations,
and adds `a²+a+1` (358 generators total). This fixes original cells 0 through
80, not the first 81 prefix coordinates.

`exact_pivot_review_six_fiber.py` independently rebuilds and verifies all 358
input polynomials, the variable order, input and basis hashes, provenance,
normal solver exit, the unique completion marker, and absence of solver errors.
The raw leading export uses `x1` through `x96` and `a`. After checking that
header verbatim, the auditor aliases `a → x97` for the shared strict parser.
Both independent integer staircase counters count its 108 leading monomials as
quotient dimension 12. Dividing by the separable quadratic coefficient-extension
degree 2 gives exactly 6 fixed-prefix boards. This validates a fixed fiber, not
the unrestricted count.

The original outer script raised a parser error because the shared parser
expected `x97` instead of `a`, after the solver had already finished. The raw
outer log is preserved, and the owner recovered the finished export without
rerunning the solver. Stale inherited fixed-cell and equation-label metadata
were fixed and documented without altering the input or basis. Because exact
child CPU and wall times were not saved before that exception, only the
solver's rounded 3.14 CPU and 3.17 wall seconds remain; they should not be
cited as measured subprocess resource usage.

The exporter later added a separate `prefix_model_source_sha256` metadata field
so `run()` can log the emitted input hash without overwriting the model JSON
hash. All eight current backend definitions were rechecked against the audited
input bytes and match exactly. Current exporter hash:
`e09e337b2510690b4ace326771c915cd5d58d8a0a0ec15c7b67ae9efb3662fe8`. The read
and recount report is `exact_pivot_review_six_fiber_results.json`; it launched
no solver process.
