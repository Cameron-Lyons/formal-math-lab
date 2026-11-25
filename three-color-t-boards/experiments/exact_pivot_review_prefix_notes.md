# Independent prefix-coordinate audit

The frozen model, exporter, and all eight backend preparation modes pass.
This audit starts no solver and establishes no full count. Results and fresh
inputs are in `exact_pivot_review_prefix_results.json` and
`exact_pivot_review_prefix_prepared/`.

Frozen model SHA256:
`7f8251ab52e8d6869c19cc861dc98b0c1e66904313b0d87920d9f95659700092`.

## Quotient isomorphism

The recorded cell order is a permutation of all 100 original cells. Define
`y_j = sum_(k<=j) z_order[k]` over F2. Its inverse is
`z_order[j] = y_j + y_(j-1)`, with `y_-1=0`. These triangular linear maps
are inverse polynomial-ring isomorphisms, rather than a quotient or symmetry
normalization. The audit composes them on all 100 coordinate basis vectors.

Reconstructing the 81 placements from row indices gives transformed unary
supports `[80]`, `[16,97]`, `[8,72,81,98]`, `[7,9,65,82,99]`. Independent
Gaussian elimination yields

```
y80 = 0
y16 = y97
y81 = y8 + y72 + y98
y99 = y7 + y9 + y65 + y82.
```

Eliminating these four linear equations leaves 96 free prefix coordinates.
Every original domain and Fourier equation is substituted through this map.
Thus the resulting quotient is isomorphic to the original full ideal's
quotient. Its dimension is still the unrestricted labeled count, with divisor
one and multiplier one.

## Domain and Frobenius semantics

The retained domains are all 100 polynomials `L_cell(y)^3+1`, where L_cell is
the transformed original color variable. They are not 96 blanket equations
`y_i^3+1`. The new coordinates can vanish. The five published boards have
24,23,24,24,21 zero free prefix coordinates, respectively, while satisfying
every exported constraint. Some transformed original domains happen to be
single-variable cubics because two color forms have one term; those are
valid original-color constraints and are retained.

The audit uses ordinary tuple-monomial arithmetic. No exponent is reduced
modulo three or made Boolean in the prefix ring. It independently rebuilds
all 100 domain polynomials, all 72 nonzero Fourier moments, and all eight
elementary constraints. Exactly the eight unary moments vanish under the
linear substitutions. Elementary partners are ordinary squares, with fourth
powers retained. The existing Fourier representative convention still works:
missing partners follow by squaring and using the transformed original color
domains, without assuming an individual prefix coordinate is nonzero.

The 96 optional equations `y_i^4+y_i` are valid even when y_i=0. They are
explicit ideal consequences, since before eliminating the four linears

```
y_j^4+y_j = sum_(k<=j) z_order[k] * (z_order[k]^3+1).
```

The audit checks this identity symbolically after substitution for every
prefix index, including the four eliminated indices. It does not infer
redundancy merely by testing finite-field assignments. Adding these equations
therefore preserves the ideal and the quotient dimension, including its
multiplicities. No new field-extension variable is involved in this full
unrestricted model.

## Export and adapter checks

`exact_pivot_review_prefix.py` independently derives the global-y forms and
then maps them to the ascending `free_prefix_variables` list. This distinction
matters: `original_color_linear_forms` uses global prefix indices, while
solver variables x1 through x96 index that free list. Every packed source
polynomial and every emitted polynomial is checked against the reconstructed
ordinary expression.

All eight combinations of representative/all moments, optional elementary
constraints, and optional quartic field equations were checked through both
the standalone exporter and actual `exact_msolve_backend.definitions` and
prepare-only paths. Every input has exactly 100 transformed original domains
and 36 or 72 retained moments; the two optional groups add eight or 96 equations.
Thus the generator counts are 136/144/232/240 and 172/180/268/276. The backend
preserves unrestricted scope and divisor one, and every preparation has
`PREPARED_NOT_RUN`, no completed basis, and no count. Seven incompatible
scope/option combinations are rejected. The subprocess entry point is mocked
to raise immediately if any preparation attempts to run a solver.

Independent evidence comprises 276 source-polynomial comparisons, 100 inverse
coordinate basis checks, 100 explicit optional-field ideal identities, 20
arbitrary F4 coordinate assignments, and all five published valid witnesses.
The owner separately ran small complete coordinate fixtures; those solver
results are not independent solver runs claimed by this audit.

## Completed transformed nine-row fiber

The owner ran the known fixed nine-row fiber once with all moments, the
elementary constraints, and the optional quartics. The actual input has 97
variables: the 96 free prefix coordinates plus a coefficient-extension
variable a. It retains the 276 full transformed generators, adds 81 original
color constraints, and adds a²+a+1, for 358 generators. This fixes original
cells 0 through 80; it does not fix the first 81 prefix coordinates.

`exact_pivot_review_six_fiber.py` independently reconstructs and checks all
358 actual input polynomials, the exact named variable order, input/basis
hashes and provenance, successful solver exit, the unique completed-export
marker, and absence of solver diagnostics. The original raw leading export
uses x1 through x96 and a. After checking that exact header, the auditor
applies only the identifier alias a→x97 for the shared strict parser.
Both independent integer staircase counters recount its 108 leading
monomials as quotient dimension12. Dividing by the separable quadratic
coefficient-extension degree2 gives exactly six fixed-prefix boards.
This is a fixed-fiber validation, not an unrestricted count.

The original outer run stopped at a parser exception because the shared
parser expected x97 instead of a. The solver had already completed. Its raw
outer log remains preserved, and the owner recovered the completed export
without rerunning the solver. Stale inherited fixed-cell and equation-label
metadata were corrected and documented; the input and basis did not change.
Precise child CPU/wall measurements were not persisted before the initial
exception. Only the solver's rounded 3.14 CPU / 3.17 wall seconds are retained;
they must not be presented as measured subprocess resource usage.

The exporter subsequently added a separate `prefix_model_source_sha256`
metadata field so run() can record the emitted input hash without losing the
model JSON hash. All eight current backend definitions were rechecked against
the previously audited input bytes and are unchanged. Current exporter hash:
`e09e337b2510690b4ace326771c915cd5d58d8a0a0ec15c7b67ae9efb3662fe8`.
The read/recount report is `exact_pivot_review_six_fiber_results.json`; it ran
no solver process.
