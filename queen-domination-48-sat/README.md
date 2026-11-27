# Queen domination on the 48 × 48 board by SAT certificates: γ(Q₄₈) = i(Q₄₈) = 25

No placement of 24 queens can occupy or attack every square of the 48 × 48 board, while 25 pairwise non-attacking queens can. Both the domination number γ(Q₄₈) and the independent domination number i(Q₄₈) are therefore 25.

This gives a second proof of γ(Q₄₈) = 25, independent of the enumeration in [queen-domination-48](../queen-domination-48/), and adds i(Q₄₈) = 25. It uses the frame method and SAT encoding from Jason Davies' [queen-domination](https://github.com/jasondavies/queen-domination). Lean's kernel proves the reduction to 47,580 explicit CNF formulas, including soundness of the CNF encoding for every board size. The unsatisfiability of those formulas is checked by certified computation outside the kernel.

| Field | Summary |
| --- | --- |
| Problem & identifiers | `gamma(Q_48)` and `i(Q_48)`, queen's graph Q₄₈; Östergård and Weakley (Electron. J. Combin. 8 (2001) #R29) showed both lie in {24, 25}; Davies §9 (`hexagonmath.org/pdf/2611.00830v1`) |
| Kernel-checked | `gamma_48_le`, `igamma_48_le` (≤ 25, unconditional); `gamma_48_eq_25_of_formulas_unsat`, `igamma_48_eq_25_of_formulas_unsat` (= 25 assuming the 47,580 formulas are unsatisfiable). Axioms: `propext`, `Classical.choice`, `Quot.sound`. |
| Outside the kernel | Unsatisfiability of all 47,580 formulas, refuted by CaDiCaL + drat-trim and verified from LRAT certificates by a compiled Lean checker ([lean-check](lean-check/)). |
| Closed statement | `gamma_48 : gamma 48 = 25` in [Certified48.lean](Certified48.lean), assuming one named axiom for the certificate check. |
| Prior art | Re-audited 26 November 2026: Aleksej Đukić proved $\gamma(Q_{48}) = 25$ on 22 November 2026 (OEIS A075458, `10.5281/zenodo.24537292`) using the same 47,580-case Davies frame split, which together with Östergård and Weakley's (2001) independent 25-queen set implied $i(Q_{48}) = 25$. This folder adds Lean kernel soundness for the CNF encoding, compiled Lean LRAT verification, and an explicit proof of $i(Q_{48}) = 25$. See [PRIOR_ART.md](../PRIOR_ART.md). |
| Review | Produced and re-checked by AI agents ([CHECKS.md](CHECKS.md)); no human has reviewed it. |

## The statements

```lean
theorem igamma_48_le : igamma 48 ≤ 25

theorem gamma_48_eq_25_of_formulas_unsat
    (H : ∀ cs ∈ QueenDomSat.enumCases 48 24, (QueenDomSat.caseFormula 48 24 cs).Unsat) : gamma 48 = 25

theorem igamma_48_eq_25_of_formulas_unsat
    (H : ∀ cs ∈ QueenDomSat.enumCases 48 24, (QueenDomSat.caseFormula 48 24 cs).Unsat) : igamma 48 = 25
```

Here `gamma n` is the least size of a dominating set of the queen's graph on `Fin n × Fin n`, `igamma n` is the least size of an independent dominating set, and `QueenDomSat.caseFormula n k cs : Std.Sat.CNF Nat` is the CNF formula for a case, defined in [lean-sat](lean-sat/QueenDomSat/Formula.lean). For every n and k ≤ n - 2, `lt_gamma_of_formulas_unsat` proves that if all case formulas are unsatisfiable, then γ(Qₙ) > k.

## The proof

| Step | Statement | Checked by |
| --- | --- | --- |
| Upper bound | The 25 squares of `data/frame/q48_25_indep.json` dominate Q₄₈ and do not attack each other | Kernel (`decide +kernel`) |
| Layer 1 (Davies) | Any dominating set of 24 queens satisfies, up to board symmetry, the constraints `CaseSat` of one of 47,580 cases | Kernel (pinned dependency) |
| Layer 2 (here) | If `CaseSat n k cs D`, then the CNF formula for that case is satisfiable | Kernel (`Queens48/`) |
| Certificates | Each of the 47,580 formulas is unsatisfiable | CaDiCaL + drat-trim; compiled Lean checker |

Layer 2 spans five files totaling 1,093 lines, meant to be read in this order; `Gamma48.lean` applies it to the 48 × 48 board.

1. [Framework.lean](Queens48/Framework.lean): the encoder emits groups of clauses. A group starting at variable counter `nv` uses fresh variables `nv + 1, ..., nv + m`. The key notion is `Sound A nv m P`: whenever variables up to `nv` satisfy A, the fresh variables can be assigned to satisfy P. Groups compose via `Sound.append`. For the sequential counter, let C(i) count the true literals among the first i and let s[i][j] mean j < C(i + 1); every clause follows from C(0) = 0, C(i) ≤ C(i + 1) ≤ C(i) + 1, and C ≤ k.
2. [Base.lean](Queens48/Base.lean): a dominating set D makes the variables for its squares and the lines through them true. Squares, rows, columns, and both diagonal directions are five instances of one structure, `Kind`.
3. [Waste.lean](Queens48/Waste.lean): on the border of the frame, the true waste literals count the three waste terms in identities (F), (V), and (H) (`count_wasteValues`).
4. [Extra.lean](Queens48/Extra.lean): those identities are part of `CaseSat`, so the bounds (F), (V), and (H) hold.
5. [Sound.lean](Queens48/Sound.lean): combining all groups gives a satisfying assignment.

## Trust boundary

- Lean's kernel checks the reduction, the CNF encoding, the case list, and the 25-queen upper bound.
- CaDiCaL 3.1.0 refuted all 47,580 formulas with DRAT proofs verified by drat-trim. Independently of both, `qdcheck` builds every formula with the Lean encoder and replays its LRAT certificate using the verified step functions of Lean's `Std.Tactic.BVDecide.LRAT`. It can report success only by constructing a value of type `PLift (∀ cs ∈ enumCases 48 24, (caseFormula 48 24 cs).Unsat)`, which is the hypothesis `H` above. The recorded run reported `s ALL VERIFIED n=48 k=24 cases=47580` in 810 s on 5 threads.
- Accepting that run requires trusting the Lean compiler and runtime, including the `implemented_by` and `extern` replacements in core and Std, just as with `native_decide`. Because the certificates total 148 GB of LRAT text, they are too large for the kernel, so the closed statement uses one named axiom.
- The certificates (25 GB compressed) are not in this repository; `data/frame/d_48_24.jsonl.xz` records the SHA-256 hash of every formula and certificate.
- Layer 2 covers the plain encoding only, not the symmetry-breaking clauses and cubes used upstream for part of the n = 35 run. The value of γ(Q₄₇) ∈ {24, 25} stays open.

## Reproduce

With Lean 4.36.0 via `elan`, run from this directory:

```sh
lake exe cache get && lake build        # the kernel-checked part
lake env lean Axioms48.lean             # axiom report (AXIOMS48.txt)
lake env lean Certified48.lean          # the closed statements, modulo the named axiom
lake env lean Replay48.lean             # kernel replay of the compiled modules (several minutes; REPLAY48.txt)
```

Reproducing the SAT computation needs `zstd`, CaDiCaL, and drat-trim (`scripts/get_tools.sh`):

```sh
# about 10 CPU hours, 25 GB
python3 -I code/frame/run_cases48.py 48 24 --jobs 6 --tl 1800 --out runs/d_48_24.jsonl
# about 55 CPU minutes
cd lean-sat && lake build && cd ../lean-check && lake build
python3 -I scripts/run_check.py 48 24 ../runs/d_48_24.jsonl.lrat --jobs 5 \
    --log LOG.jsonl --summary SUMMARY.json --out STDOUT.txt
```

| Case class | Cases | CaDiCaL (CPU s) | drat-trim (CPU s) | LRAT text (GB) |
| --- | ---: | ---: | ---: | ---: |
| square box, deficit vector 0 | 819 | 14,584 | 7,214 | 64.39 |
| square box, positive deficit | 6,279 | 3,204 | 1,879 | 21.59 |
| non-square box, deficit vector 0 | 13,546 | 2,327 | 2,570 | 27.34 |
| non-square box, positive deficit | 26,936 | 1,669 | 3,493 | 35.14 |
| total | 47,580 | 21,784 | 15,156 | 148.46 |

## Files

- `Queens48/`: Layer 2 and the main theorems. `Cases48*.lean` (generated by `scripts/gen_cases.py 48 24 data/frame Queens48 data/frame the`) also proves that the table of 47,580 recorded cases equals the case list, though the theorems above do not use it.
- `lean-sat/` and `lean-check/`: the Lean CNF encoder and the certificate checker (no Mathlib).
- `code/frame/` and `data/frame/`: the run driver, the search for 25-queen sets, Davies' unmodified `enc.py` and `geom.py`, the 25-queen sets, and records of the SAT run, its final check, and the certificate check.
- `lean-sat/scripts/compare_enc.py` checks the Lean encoder against `enc.py`. Comparing it with the n = 26, 32, 46 records requires the data files from Davies' repository, as does the independent case-list check `code/frame/final_check40.py` (which lives in that repository).

## Source and license

Davies' Lean development (Layer 1) is a Lake dependency pinned at commit `bc37cb0`. The files `enc.py`, `geom.py`, `scripts/get_tools.sh`, and `scripts/runlog.py` are taken from his repository unmodified. `scripts/gen_cases.py` and `code/frame/run_cases48.py` are modified from his versions, and `lean-sat` transcribes his encoder and case list into Lean. His repository uses the Apache-2.0 license, and this directory keeps that license (see [LICENSE](LICENSE)).
