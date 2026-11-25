# Complete cap split with the msolve backend

No full ternary total has been computed. Before this continuation there were no
four-cell cap solver artifacts. The root agent then ran the first one,
`exact_msolve_cap0000_prime2`: its terminal status is `INCOMPLETE_TIMEOUT` at
180 seconds, with no completed basis or count. None of the ten required raw
cap completion counts is currently available from msolve. Existing completed
nine-row fibers do not fill a cap case.

`exact_msolve_cap_split.py` supplies a separate audited msolve path into the
existing `exact_symmetry_split.aggregate`. The existing command-line auditor
in `exact_symmetry_split.py` is specific to Singular and cannot directly ingest
msolve result JSON. The new adapter does not change that implementation or the
solver backend, and never launches a solver.

## Exact factors and complete scope

The cap is the first two rows, flattened as top/left/middle/right. The following
table applies to both tested characteristics 2 and 29. Every model has all 96
remaining board variables with ordinary cubic domains and all 80 Fourier
moments. The nine cases requiring an additional coefficient-field variable
also retain its quadratic domain.

| Cap | Cap orbit weight | Variables | Generators | Quotient divisor | Raw-count divisibility |
| --- | ---: | ---: | ---: | ---: | ---: |
| 0000 | 3 | 96 | 176 | 1 | 4 |
| 0001 | 12 | 97 | 177 | 2 | 1 |
| 0010 | 6 | 97 | 177 | 2 | 2 |
| 0011 | 12 | 97 | 177 | 2 | 1 |
| 0012 | 12 | 97 | 177 | 2 | 1 |
| 0101 | 6 | 97 | 177 | 2 | 2 |
| 0102 | 6 | 97 | 177 | 2 | 2 |
| 0111 | 6 | 97 | 177 | 2 | 2 |
| 0112 | 12 | 97 | 177 | 2 | 1 |
| 0121 | 6 | 97 | 177 | 2 | 2 |

The weights sum to 81. For each cap let D be the completed ordinary prime-field
quotient dimension and d the divisor in the table. Its raw completion count is
c = D/d, and the full labeled count is the sum of orbit_weight * c over all ten
caps. No extra apex, palette, reflection, or field factor is applied.

For cap 0000 every substituted color equals 1 in the prime field. Scalar
extension preserves the quotient dimension, which therefore equals c. For the
other caps the adapter represents the coefficient field by an ordinary
variable a with a^2+a+1 = 0. This quadratic is irreducible and separable for the
tested primes, and restriction of scalars doubles dimension: D = 2c. The two
geometric coefficient embeddings are interchanged by Frobenius, which swaps
colors 1 and 2. Dividing by two removes the coefficient extension; it does not
take a symmetry quotient of the board fiber.

The raw-count divisibility column is a further necessary consistency check.
The full-board action is free by `ExactSymmetry.lean`, so the stabilizer of a
cap acts freely on that cap's completion set. Its order is 12/orbit_weight.
This does not make the cap orbit weights uniformly 12.

## Input and result audit

`exact_msolve_cap_split_check.py` independently reconstructs all 81 placements
in centered coordinates through `exact_msolve_review.expected_polynomials`,
then compares every ordinary polynomial with the emitted model. It does not
reuse the backend's generator term lists as an oracle. All twenty cap models
(ten caps, two primes) pass. The root's actual cap0000 input also passes:

- Input SHA256: `4aa5a5354dd1596d4240992c8a078604beecee72808a2b66f9106aafea602900`.
- Variable-to-original-cell order: 81, 90, 99, then 4 through 98 excluding 81
  and 90. Cells 0 through 3 are fixed to color 0.
- 96 variables, 96 ordinary cubic domains, 80 moments, divisor 1.

The result auditor requires literal COMPLETE status, normal process exit,
completed basis, a unique patched export-completion marker in the actual log,
absence of error diagnostics, the expected exact sparse command, a reviewed
executable hash and unchanged local libraries, exact input geometry and scope,
matching basis and leading-export provenance, and an independent arbitrary
precision staircase recount. It checks the field divisor before constructing
a raw `VerifiedCount`. Aggregation then requires each canonical cap exactly
once and checks the stabilizer divisibilities. No aggregate is emitted with
even one missing cap.

A completed standard basis remains a trusted exact backend result, rather
than a separately checked Buchberger certificate. This matches the existing
backend trust boundary. The new code independently checks its input scope and
exact staircase arithmetic; it cannot manufacture an attestation for a
partial computation. New executable builds must be reviewed before adding
their hashes to the auditor's explicit allowlist.

Checks retained in `exact_msolve_cap_split_checks.json`: 20 geometry/model
checks, 31 metadata rejection cases, three log rejection cases, and seven
aggregation/scope rejection cases. A retained completed nine-row artifact was
recounted as quotient dimension 12 / divisor 2 = six boards, then correctly
refused as a cap contribution. Its solver was not rerun. Synthetic complete
and zero aggregates only test aggregation mechanics; they are explicitly not
board counts. The prior exhaustive binary cap audit still gives 168 using
the same unchanged partition/aggregation core.

Example once all ten results exist:

```sh
python experiments/exact_msolve_cap_split.py --prime 2 \
  --result 0000=experiments/cap0000.json \
  --result 0001=experiments/cap0001.json \
  --result 0010=experiments/cap0010.json \
  --result 0011=experiments/cap0011.json \
  --result 0012=experiments/cap0012.json \
  --result 0101=experiments/cap0101.json \
  --result 0102=experiments/cap0102.json \
  --result 0111=experiments/cap0111.json \
  --result 0112=experiments/cap0112.json \
  --result 0121=experiments/cap0121.json \
  --output experiments/cap_total.json
```

The example names are placeholders, not completed results. Output creation is
exclusive and refuses an existing destination.

## Safe necessary constraints for an early zero proof

A larger fixed prefix is impossible if it already repeats a complete T
pattern; if a fixed ordered k-role pattern occurs more than 3^(4-k) times
(27, 9, 3, 1 for k=1,2,3,4); or if too few remaining compatible placements can
reach one of these required totals. These are integer marginal constraints,
not merely characteristic-two congruences. Any valid completed board has all
of them. A checked contradiction in this necessary system proves zero.

Each two-row cap fixes only one entire T. No cap violates these immediate
upper bounds. The selected cap pattern is already used once, so it must be
forbidden at every other placement; these local exclusions are valid
redundant constraints for a future encoding. We have not implemented or
benchmarked them, and do not claim that they make an algebraic solve easier.

The existing saved witnesses cover 0000, 0001, 0011, 0111, and 0112. No saved
witness covers 0010, 0012, 0101, 0102, or 0121. Absence from these artifacts
does not prove any cap impossible. A unit ideal from a completed exact basis,
or a separately checked complete contradiction, would establish a zero case;
a timeout or memory failure does not.
