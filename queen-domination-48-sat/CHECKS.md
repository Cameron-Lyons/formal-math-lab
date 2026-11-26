# Checks made on this project

These checks were run by AI agents instructed to look for errors; no human has reviewed the project. The work took place on 24-25 November 2026 in a clone of Jason Davies' repository and was moved here on 25 November. Logs of the checks are not stored, though the recorded certificate run is in `data/frame/lean_check_48_24.*`. Paths in those files are relative to the original clone, while the hashed sources `lean-sat/` and `lean-check/` are unchanged here.

## Certificate runs before the move

All 47,580 certificates were checked five times across three versions of `qdcheck` that differ only in output handling: three runs of the first version (from three separately built, bit-identical binaries), one of the second, and one of the current version (the recorded run). Every run printed `s ALL VERIFIED n=48 k=24 cases=47580` with exit status 0, and all five logs match on every case in verdict, clauses, lemmas, hints, steps, and bytes.

## Stored certificates and case list

The SHA-256 digest of all 47,580 stored LRAT files was recomputed and matches the records. On samples of small and medium cases, re-running CaDiCaL and drat-trim on 66 cases (0.5% of total LRAT bytes) reproduced the stored files byte for byte. The C checker `lrat-check` accepted 43 of 43 certificates (0.5% of total bytes) against the DIMACS file written by the Lean encoder and rejected 42 of 42 certificates from other cases.

`final_check40.py 48 24` from Davies' repository passed (`data/frame/final_check_48_24.json`), checking an independent case list with Burnside counts, one refuting record per case, and rebuilt hashes of all 47,580 formulas.

## Negative controls

Using the first version of `qdcheck`, the checker printed `ALL VERIFIED` for `(8, 4)`, `(14, 7)`, `(16, 8)`, `(20, 10)`, and `(15, 8)`, and `NOT VERIFIED` for `(4, 2)`, `(6, 3)`, `(10, 5)`, `(12, 6)`, `(18, 9)`, and `(13, 7)` (where γ = k). Giving satisfiable cases a certificate from another case or a degenerate certificate failed all 5,430 times. Rotating certificates across 120 cases of `(48, 24)` failed every time, and 900 mutated certificates for satisfiable cases were all rejected.

## Proof audit

Layer 2 was rewritten in a simpler form on 25 November, dropping from 3,072 lines to 1,186 lines (including the n = 48 statements). All 17 statements from both versions and the 187 constants they unfold to were compared expression by expression. They matched, except that `q48i_independent` is now stated as `Independent q48i` and one auto-generated auxiliary proof has a different name; a few unused corollaries were dropped.

The final statements were also restated directly on `Fin 48 × Fin 48` (writing out attack and domination without library definitions) and derived in Lean. For `(6, 3)`, where a dominating set exists, the hypothesis `H` is proved false, confirming that the case formulas are not trivially unsatisfiable.

## Checks after the move

From this directory, the following passed:

- `lake build --wfail`
- `Axioms48.lean` (`AXIOMS48.txt`): checked 46 named theorems and mechanically checked all 1,611 declarations of `Queens48.*` and `QueenDomSat.*`, finding no axioms.
- `Certified48.lean`
- `Replay48.lean` (`REPLAY48.txt`): replayed 2,336 constants (1,780 of them theorems) through the kernel on top of Mathlib, verifying that both an ill-typed proof of `False` and a `rfl` proof of `gamma 48 = 24` are rejected.
- Rebuilding `qdcheck` produced the same binary (SHA-256 prefix `4388f9e4`) and re-running it on all 47,580 certificates returned `ALL VERIFIED` with the same per-case counts as the recorded run.

## Not done

- `leanchecker` passed on `lean-sat` and on an earlier version of `lean-check`, but was not completed on the Mathlib-based modules.
- `gamma_48_eq_25_of_lrat_check` was not instantiated.
- The literature search was brief.
