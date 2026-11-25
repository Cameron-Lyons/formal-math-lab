# Independent sign-selector model review

The frozen natural and minimum-fill inputs pass the independent audit in
`exact_algorithms_sign_review.py`; detailed results are in
`exact_algorithms_sign_review.json`. This review runs no solver and establishes
no unrestricted count.

The reviewer does not import the exporter. It implements arithmetic in
F3[t]/(t^5+t^4+2t^3+2t^2+1), checks all 12 possible monic linear/quadratic
divisors and all 243 field elements, reconstructs the ordinary 38-term norm,
and reduces it using the four explicit F3 field relations. All 81 inputs agree
with the exported 17-term selector: its only zero is the origin, and its
remaining values are forty 1s and forty 2s. It is odd and its square is the
indicator of a nonzero input.

For a valid board, the ordered patterns at placements 0 and 3 differ. Their
rolewise difference Delta therefore has h(Delta) in {1,2}. Given a board z,
set a=z_0, D=z-a, s=h(Delta(D)), and d=sD. Then h(Delta(d))=1 and
z=a+s*d. Conversely every solution of the canonical equations, with any
a in F3 and s in {1,2}, reconstructs a valid board. These constructions are
mutual inverses. The independent offset and sign variables are already in
the input; its quotient dimension is the full labeled count, with divisor
and multiplier both 1. The argument relies on the previously audited
translated/e3 source ideal, whose bytes and explicit 96 field domains are
checked here. Finite field domains split into distinct F3 roots, so equality
of these finite solution sets gives the asserted product-algebra isomorphism.

The audit independently reconstructs all 100 bilinear original-color forms
and all 180 terms of the expanded selector constraint. It checks every one
of the 179 actual input polynomials in both orders, including the unchanged
176 source generators, s^3-s, s^2-1, and the selector. No Boolean identities
or implicit normalization are introduced. It also checks 161 known-board
round trips, 966 affine palette reconstructions, and all equations on five
boards; these are supplementary tests, not the basis of the general proof.

Both `exact_msolve_backend.definitions` sign variants emit the frozen input
bytes and correct scope metadata. Fifteen incompatible argument combinations
are rejected. Actual original-color prefix constraints must be bilinear
`a+s*d_cell-color`; reusing the older linear `a+d_cell` forms would change
the fiber. The separately bounded six-completion fixture checks this
specialization through the exact backend.

The one authorized fixture is now terminal and **COMPLETE**. Run
`python experiments/exact_algorithms_sign_six.py` only in a fresh artifact
location: it deliberately refuses to overwrite the saved run. The actual
97-variable input contains the 179 original generators followed by 81
bilinear color equations, with SHA-256
`8f222a6e28a9fc2d814e30abab5338d22af8c23ed46aa033dfd418d71ff9adff`.
The reviewed seventh executable returned exit 0, exactly one completion
marker, no error diagnostics, and 102 leading monomials. Both independent
integer staircase counters give dimension **6**, directly the number of
completions of this prefix. Measured child CPU time was 0.878748 seconds
and wall time 0.993181 seconds; the whole guarded worker took 3.182028
seconds. Limits were 30 seconds for the solver, 60 seconds for the worker,
and 2 GiB address space. See `exact_algorithms_sign_six.json`, its adjacent
leading export and logs, and `exact_algorithms_sign_six.fixes.json` for
all original-cell/color constraints. This is not a count of unrestricted
boards or a new lower-bound claim.
