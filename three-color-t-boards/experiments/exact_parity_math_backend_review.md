# Independent review of the algebra backend

The reviewed versions of `exact_algebra_backend.py` and
`exact_standard_monomials.py` compute quotient dimensions accurately whenever
Singular finishes a standard basis. No full board problem was run for this
review. Source hashes and finite test results are saved in
[exact_parity_math_backend_review.json](exact_parity_math_backend_review.json).

The review caught one correctness bug, which the owning agent fixed:
`normalize_apex` used to multiply every model's finished dimension by 3, even
though `z_apex=1` was only added for `ternary-original`. Unsupported models are
now rejected, and the factor of 3 is applied only when metadata confirms that
normalization was actually imposed. For `ternary-original`, multiplying by 3 is
valid because global multiplication by `F₄×` acts freely and puts exactly one
board in each orbit at apex 1.

Field handling is sound. The original and reduced Fourier ideals use ordinary
F₂ polynomial rings with cubic domains and no Boolean field equations. Their F₂
dimensions match the geometric solution counts over F₄ by scalar extension and
separability of the cubic domains. Fixed prefixes work over F₄ using colors
`1, a, a+1` with `a²+a+1=0` and XOR coefficient accumulation. A fully fixed
valid board gives quotient dimension 1, while an invalid one-cell mutation
gives 0. When no free board cells remain, the dummy variable is constrained to
zero and contributes multiplicity 1.

Both standard-monomial counters use Python arbitrary-precision integers and
sound recurrences: fix a variable's exponent, keep only leading generators that
can divide at that exponent, project out the fixed coordinate, and sum. Grouping
exponents into intervals between consecutive generator thresholds is valid. Pure
powers bound the box, disconnected variable supports factor, and dominated
generators can be dropped. Both counters matched direct enumeration on 300 extra
deterministic random finite boxes.

The standard-basis prerequisite is critical. The independent counter's
completion flag is an attestation from the caller, not a Buchberger check. The
backend checks its own completion markers, Singular's `isSB` attribute, solver
diagnostics, and the count of exported leading rows. This review trusts
Singular's completed exact `std` or `slimgb` run and does not re-verify the
basis polynomials or their ideal membership. Agreement between the two monomial
counters confirms the staircase count, not the basis computation ahead of it.

Once Singular finishes a standard basis and exports every leading monomial, the
staircase count already determines the exact quotient dimension, so Singular's
later Hilbert calculation is redundant. Marking a run
`COMPLETE_FROM_LEADING_IDEAL` is therefore justified if Hilbert times out after
both counters finish and agree. Synthetic log tests verified that this case
returns the exact dimension, while an incomplete export, a diagnostic message,
or a missing leading row returns no dimension. The Hilbert cross-check also
drops the trailing auxiliary entry of Singular's returned vector as required.

One operational limit remains: `--timeout` limits the Singular subprocess, not
the entire Python pipeline. The first Python counter checks its deadline only
every 256 new states, and the second uses a state cap, so expensive
normalization can run between checks. A future large run should add an outer
wall-time and memory guard. A timeout must never be read as a zero count, and
the tested error paths enforce that rule.
