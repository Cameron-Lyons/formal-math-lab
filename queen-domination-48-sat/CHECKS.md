# Checks made on this project

This log records the automated sanity checks, negative controls, and proof audits run on the `queen-domination-48-sat` proof of $\gamma(Q_{48}) = i(Q_{48}) = 25$.

> **Authorship and review disclosure:** All checks below were run by AI agents instructed to look for errors; **no human has reviewed the project**. The work took place on 24-25 November 2026 inside a clone of Jason Davies' repository and was moved here on 25 November. Detailed audit logs are not stored in the repo, though the recorded certificate check run lives in `data/frame/lean_check_48_24.*`. (Paths inside those logs are relative to the original clone, while the hashed sources `lean-sat/` and `lean-check/` are unchanged here.)

## 1. Repeated certificate runs (before moving the files)

All 47,580 LRAT certificates were verified **five times** across three versions of `qdcheck` differing only in output handling:
- three runs of the first version (from three separately built, bit-identical binaries),
- one run of the second version, and
- one run of the current version (the recorded run).

Every single run exited with status `0`, printed `s ALL VERIFIED n=48 k=24 cases=47580`, and agreed across all five logs on every individual case in verdict, clauses, lemmas, hints, steps, and byte counts.

## 2. Integrity of stored certificates and the case list

- **Hash check:** Recomputing the SHA-256 digest of all 47,580 stored LRAT files matched the recorded hashes completely.
- **Solver reproducibility sample:** Re-running CaDiCaL and `drat-trim` on a sample of 66 small and medium cases (0.5% of total LRAT bytes) reproduced the stored LRAT files byte for byte.
- **Independent C checker cross-check:** The C verifier `lrat-check` accepted 43 of 43 sampled certificates (0.5% of total bytes) against DIMACS files emitted by the Lean encoder, and rejected 42 of 42 certificates swapped in from other cases.
- **Upstream case-list audit:** Running `final_check40.py 48 24` from Davies' repository passed (`data/frame/final_check_48_24.json`), independently verifying the case list with Burnside counts, confirming one refuting record per case, and rebuilding hashes of all 47,580 formulas.

## 3. Negative controls (testing that invalid inputs fail)

Using the first version of `qdcheck`:
- **Known unsatisfiable boards ($\gamma > k$):** Printed `ALL VERIFIED` for `(8, 4)`, `(14, 7)`, `(16, 8)`, `(20, 10)`, and `(15, 8)`.
- **Known satisfiable boards ($\gamma = k$):** Printed `NOT VERIFIED` for `(4, 2)`, `(6, 3)`, `(10, 5)`, `(12, 6)`, `(18, 9)`, and `(13, 7)`.
- **Corrupted / mismatched certificates:**
  - Feeding satisfiable cases a certificate from another case or a degenerate certificate failed all **5,430** times.
  - Rotating certificates across 120 cases of `(48, 24)` failed every single time.
  - All **900** mutated certificates for satisfiable cases were rejected.

## 4. Proof and specification audit

- **Layer 2 simplification check:** On 25 November, Layer 2 was simplified from 3,072 lines down to 1,186 lines (including the $n = 48$ statements). Comparing all 17 statements from both versions and the 187 constants they unfold to expression by expression showed exact agreement—except that `q48i_independent` is now stated as `Independent q48i`, one auto-generated auxiliary proof has a different name, and a few unused corollaries were removed.
- **Standalone restatement on `Fin 48 × Fin 48`:** The final statements were restated directly on `Fin 48 × Fin 48` (writing out queen attack and domination without library definitions) and derived in Lean from our theorems.
- **Non-vacuousness check:** For `(6, 3)`, where a 3-queen dominating set exists, the hypothesis `H` (that all case formulas are unsatisfiable) was proved *false* in Lean, confirming that the encoded case formulas are not trivially unsatisfiable.

## 5. Checks run after moving to this repository

From `queen-domination-48-sat/`, every check below passed:
- `lake build --wfail`
- `Axioms48.lean` (`AXIOMS48.txt`): checked 46 named theorems and mechanically scanned all 1,611 declarations of `Queens48.*` and `QueenDomSat.*`, finding no non-standard axioms.
- `Certified48.lean`
- `Replay48.lean` (`REPLAY48.txt`): replayed 2,336 constants (1,780 of them theorems) through Lean's kernel on top of Mathlib, and confirmed as negative controls that both an ill-typed proof of `False` and a `rfl` proof of `gamma 48 = 24` are rejected.
- **Binary reproducibility and re-run:** Rebuilding `qdcheck` produced the bit-identical binary (SHA-256 prefix `4388f9e4`), and re-running it over all 47,580 certificates returned `ALL VERIFIED` with the exact same per-case counts as the recorded run.

## 6. Checks not done

- `leanchecker` passed on `lean-sat` and on an earlier version of `lean-check`, but was not completed on the Mathlib-based modules.
- `gamma_48_eq_25_of_lrat_check` was not instantiated.
- The literature search was brief.
