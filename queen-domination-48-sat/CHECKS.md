# Checks made on this project

By AI agents instructed to look for errors; no human has reviewed it. The work was done on 24–25 November 2026 in a
clone of Jason Davies' repository and moved here on 25 November. The logs of the checks are not stored; the recorded
certificate run is in `data/frame/lean_check_48_24.*` (paths in those files are relative to that clone; the hashed
sources `lean-sat/` and `lean-check/` are here, unchanged).

- **The certificate check, five times before the move** on all 47,580 certificates, with three versions of the program that
  differ only in output handling: three runs of the first version (from three separately built, bit-identical
  binaries), one of the second, one of the present one (the recorded run). Result every time:
  `s ALL VERIFIED n=48 k=24 cases=47580`, exit status 0; the five logs agree on every case in verdict and in the
  numbers of clauses, lemmas, hints, steps and bytes.
- **The certificates.** The SHA-256 of all 47,580 stored LRAT files was recomputed and equals the records. On samples
  of small and medium cases: re-running CaDiCaL and drat-trim on 66 cases (0.5 % of the LRAT bytes) reproduced the
  stored files byte for byte; the C checker `lrat-check` accepted 43 of 43 certificates (0.5 % of the bytes) against
  the DIMACS file written by the Lean encoder and rejected 42 of 42 certificates of other cases.
- **The case list.** `final_check40.py 48 24` of Davies' repository passed (`data/frame/final_check_48_24.json`):
  independent case list with Burnside count, one refuting record per case, all 47,580 formulas rebuilt and hashed.
- **Negative controls** (first version of the program). `qdcheck` ends with ALL VERIFIED for (8,4), (14,7), (16,8),
  (20,10), (15,8) and with NOT VERIFIED for (4,2), (6,3), (10,5), (12,6), (18,9), (13,7), where γ = k. Offering
  satisfiable cases the certificate of another case, or a degenerate one, 5,430 times: rejected every time. 120 cases
  of (48, 24) with rotated certificates: all rejected. 900 mutated certificates for satisfiable cases: none accepted.
- **The proofs.** Layer 2 was rewritten in a simpler form on 25 November (3,072 to 1,186 lines, the n = 48 statements
  included). 17 statements of both versions and the 187 constants of the development that they unfold to were compared
  expression by expression: equal, except that `q48i_independent` is now stated as `Independent q48i` and one
  automatically generated auxiliary proof has another name. Some corollaries nothing used were dropped. The final
  statements were also restated without the library's definitions (attack and domination written out on
  `Fin 48 × Fin 48`) and derived in Lean; and for (6, 3), where a dominating set exists, the hypothesis `H` is
  proved false, so the formulas are not unsatisfiable for a trivial reason.
- **After the move**, from this directory: `lake build --wfail`; `Axioms48.lean` (`AXIOMS48.txt`: 46 named theorems, and
  mechanically all 1,611 declarations of `Queens48.*` and `QueenDomSat.*`, none of them an axiom);
  `Certified48.lean`; `Replay48.lean` (`REPLAY48.txt`: 2,336 constants, 1,780 of them theorems, sent to the kernel again on top
  of Mathlib; an ill-typed proof of `False` and a `rfl` proof of `gamma 48 = 24` are rejected); the checker rebuilt
  (same binary, sha256 `4388f9e4…`) and run again on all 47,580 certificates: ALL VERIFIED, with the same numbers for
  every case as the recorded run.
- **Not done.** `leanchecker` passed on the modules of `lean-sat` and `lean-check` (an earlier version of the program)
  and was not completed on the Mathlib-based modules. `gamma_48_eq_25_of_lrat_check` was not instantiated. The
  literature search was brief.
