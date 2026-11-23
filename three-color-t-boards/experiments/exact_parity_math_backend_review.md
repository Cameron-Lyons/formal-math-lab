# Independent review of the algebra backend

The reviewed versions of `exact_algebra_backend.py` and
`exact_standard_monomials.py` correctly compute quotient dimensions under their
explicit prerequisite that Singular has completed a standard basis. No full
board problem was run during this review. Source hashes and finite checks are
saved in [exact_parity_math_backend_review.json](exact_parity_math_backend_review.json).

One concrete correctness defect was found and fixed by the owning agent:
`normalize_apex` initially multiplied every model's completed dimension by
three, although the constraint `z_apex=1` was added only for `ternary-original`.
Unsupported normalization is now rejected, and multiplication uses metadata
attesting that normalization was imposed. For the supported model the factor
three is correct: global multiplication by `F₄×` acts freely, and exactly one
member of each orbit has apex one.

The field handling is correct. Original/reduced Fourier ideals use ordinary
F₂ polynomial rings with cubic domains, with no Boolean field equations.
Their F₂ dimensions equal geometric solution counts over F₄ by scalar
extension and separability of the domains. Fixed prefixes correctly use F₄,
with colors `1,a,a+1`, `a²+a+1=0`, and XOR coefficient accumulation. A fully
fixed valid board gives quotient dimension one; an independently invalid
one-cell mutation gives zero. The dummy variable used when no free board
cells remain is constrained to zero and introduces multiplicity one.

Both standard-monomial algorithms use Python arbitrary-precision integers.
Their recurrences are sound: condition on a variable's exponent, retain the
leading generators that can divide at that exponent, project away the fixed
coordinate, and sum. Interval grouping is valid between consecutive exponent
thresholds. Pure-power bounds give finite boxes; disconnected supports factor;
componentwise-dominated generators can be removed. Both counters matched
direct enumeration on 300 additional deterministic random finite boxes.

The standard-basis prerequisite is essential. The independent counter's
completion flag is an attestation, not a Buchberger test. The backend checks
its own completion markers, Singular's `isSB` attribute, diagnostic output,
and the number of exported leading rows. This review trusts Singular's
completed exact `std`/`slimgb` call; it does not independently verify the basis
polynomials or their ideal membership. Agreement between two monomial
counters verifies the staircase count, not the preceding basis computation.

A completed standard basis and complete leading export are sufficient for an
exact quotient dimension once the staircase is counted correctly. The later
Singular Hilbert calculation is redundant. Therefore
`COMPLETE_FROM_LEADING_IDEAL` is justified when Hilbert alone times out and
both counters finish and agree. Synthetic log tests confirmed that this case
returns the exact dimension, while an incomplete leading export, a diagnostic,
or a missing leading row produces no dimension. The Hilbert cross-check also
correctly omits the last auxiliary entry of Singular's returned vector.

The remaining limitation is operational: `--timeout` is not a hard wall-time
bound for the entire Python pipeline. It bounds the Singular child; the first
Python counter checks its own deadline only every 256 new states, and the
second has a state limit. Expensive normalization can occur between checks.
An outer wall-time/memory guard is appropriate for a future large pipeline
run. A timeout must never be interpreted as a zero count; the tested error
paths do not do so.
