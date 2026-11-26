# Complete cap split with the msolve backend

No full ternary board count has been computed yet. Before this work, there were no four-cell cap solver artifacts. The first cap run, `exact_msolve_cap0000_prime2`, stopped with status `INCOMPLETE_TIMEOUT` at 180 seconds and produced no basis or count. None of the 10 required raw cap completion counts is available from msolve, and the completed nine-row fibers cannot stand in for a cap case.

`exact_msolve_cap_split.py` provides a separate audited path from msolve results into the existing `exact_symmetry_split.aggregate` function. The existing CLI auditor in `exact_symmetry_split.py` is built for Singular and cannot read msolve result JSON directly. This new adapter leaves `exact_symmetry_split.py` and the solver backend untouched, and it never launches a solver.

## Exact factors and complete scope

A cap consists of the first two rows, flattened in order as top, left, middle, and right. The table below holds for both tested characteristics, 2 and 29. Every model keeps all 96 remaining board variables with ordinary cubic domains and all 80 Fourier moments. The 9 caps that need a coefficient-field variable also keep its quadratic domain.

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

The orbit weights sum to 81. For each cap, let `D` be the completed prime-field quotient dimension and `d` the divisor in the table. The raw completion count is `c = D / d`, and the full labeled board count is the sum of `orbit_weight * c` across all 10 caps. No extra apex, palette, reflection, or field factor applies.

For cap `0000`, every substituted color equals 1 in the prime field. Scalar extension leaves the quotient dimension unchanged, so `D = c`. For the other 9 caps, the adapter encodes the coefficient field using an ordinary variable `a` with `a^2 + a + 1 = 0`. That quadratic is irreducible and separable for both tested primes, so restriction of scalars doubles the dimension: `D = 2c`. Frobenius swaps the two coefficient embeddings (which swaps colors 1 and 2). Dividing by 2 removes that field extension; it is not a symmetry quotient on the boards.

The raw-count divisibility column adds an extra consistency check. Because the full-board symmetry action is free (`ExactSymmetry.lean`), the stabilizer of a cap acts freely on its completions and has order `12 / orbit_weight`. Even so, the cap orbit weights themselves are not all 12.

## Input and result audit

`exact_msolve_cap_split_check.py` rebuilds all 81 placements from centered coordinates via `exact_msolve_review.expected_polynomials` and compares every polynomial against the emitted model, without reusing the backend's generator term lists. All 20 cap models (10 caps across 2 primes) pass, along with the actual `cap0000` input:

- Input SHA-256: `4aa5a5354dd1596d4240992c8a078604beecee72808a2b66f9106aafea602900`
- Variable-to-original-cell order: 81, 90, 99, then 4 to 98 excluding 81 and 90 (cells 0 to 3 are fixed to color 0)
- Model size: 96 variables, 96 ordinary cubic domains, 80 moments, divisor 1

Before creating a raw `VerifiedCount`, the result auditor requires all of the following:

- Literal `COMPLETE` status, normal process exit, and a completed basis
- Exactly one patched export-completion marker in the log and no error diagnostics
- The expected exact sparse command, an allowlisted reviewed executable hash, and unchanged local libraries
- Exact input geometry, scope, and matching basis and leading-export provenance
- An independent arbitrary-precision staircase recount and a matching field divisor

Aggregation then checks that each of the 10 canonical caps appears once and satisfies its stabilizer divisibility. If even one cap is missing, no aggregate is written.

As in the rest of the backend, a completed standard basis is a trusted exact solver output rather than an independently checked Buchberger certificate. The auditor independently checks input scope and exact staircase arithmetic, and it refuses to certify partial runs. Any new solver executable must pass review before its hash is added to the allowlist.

Checks saved in `exact_msolve_cap_split_checks.json` cover 20 geometry/model checks, 31 metadata rejections, 3 log rejections, and 7 aggregation/scope rejections. A saved completed nine-row artifact was recounted as quotient dimension `12 / 2 = 6` boards and properly rejected as a cap input without rerunning the solver. Synthetic complete and zero aggregates only test aggregation code and are not board counts. The earlier exhaustive binary cap audit still produces 168 using the same unchanged partition and aggregation code.

Example command once all 10 cap results exist (these filenames are placeholders):

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

Output creation is exclusive and fails if the destination file already exists.

## Safe necessary constraints for an early zero proof

A larger fixed prefix has zero completions if any of these hold:

- It already repeats a complete T pattern.
- A fixed ordered `k`-role pattern appears more than `3^(4-k)` times (27, 9, 3, 1 for `k = 1, 2, 3, 4`).
- Too few remaining compatible placements can reach one of those required totals.

These are exact integer marginal constraints that every valid board satisfies, stronger than characteristic-2 congruences alone. A verified contradiction in these constraints proves a prefix has zero completions.

Each two-row cap fixes only one full T, so none breaks these immediate upper bounds. Because the cap's own T pattern is already used once, forbidding that pattern at all other placements is a valid redundant constraint for future encodings. We have not implemented or benchmarked those exclusions and make no claim that they speed up the algebra.

In fact, none of the 10 cap counts can be zero:

- The 1,557 valid boards in `exact_symmetry_split_coverage.json` already give witnesses for `0000`, `0001`, `0011`, `0111`, and `0112`.
- The splice certificates give valid boards for the other five: `0010` (`../splice_extension.json`), `0012` (`../splice_next.json`), `0101` (`../splice_further.json`), `0102` (`../splice_transfer.json`), and `0121` (`../splice_sixth.json`).

Any completed computation reporting zero for a cap would therefore indicate an error. A timeout or memory failure gives no count at all.
