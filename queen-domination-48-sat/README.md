# Queen domination on the 48 × 48 board by SAT certificates: γ(Q₄₈) = i(Q₄₈) = 25

24 queens cannot occupy or attack every square of the 48 × 48 board, and 25 can, even 25 pairwise
non-attacking ones. So the domination number γ(Q₄₈) and the independent domination number i(Q₄₈) are both 25.

This is a second proof of γ(Q₄₈) = 25, independent of the enumeration in
[queen-domination-48](../queen-domination-48/), and it adds i(Q₄₈) = 25. It uses the frame method and the
formulas of Jason Davies' [queen-domination](https://github.com/jasondavies/queen-domination). The reduction
to 47,580 explicit CNF formulas, including the soundness of the CNF encoding for every board size, is proved
in Lean's kernel. The unsatisfiability of the formulas is a certified computation outside the kernel.

| Field | Summary |
| --- | --- |
| **Problem & identifiers** | `gamma(Q_48)` and `i(Q_48)`, queen's graph Q₄₈; Östergård–Weakley (Electron. J. Combin. 8 (2001) #R29): both in {24, 25}; Davies §9 (`hexagonmath.org/pdf/2611.00830v1`) |
| **Kernel-checked** | `gamma_48_le`, `igamma_48_le` (≤ 25, unconditional); `gamma_48_eq_25_of_formulas_unsat`, `igamma_48_eq_25_of_formulas_unsat` (= 25 if the 47,580 formulas are unsatisfiable). Axioms: `propext`, `Classical.choice`, `Quot.sound` |
| **Outside the kernel** | the 47,580 formulas are unsatisfiable: CaDiCaL + drat-trim, and an LRAT certificate of every formula checked by a compiled Lean program ([lean-check](lean-check/)) |
| **Closed statement** | `gamma_48 : gamma 48 = 25` in [Certified48.lean](Certified48.lean), modulo one named axiom for the certificate check |
| **Prior art** | Checked **24 November 2026**; see [PRIOR_ART.md](../PRIOR_ART.md) |
| **Review** | Produced and re-checked by AI agents ([CHECKS.md](CHECKS.md)); no human has reviewed it |

## The statements

```lean
theorem igamma_48_le : igamma 48 ≤ 25

theorem gamma_48_eq_25_of_formulas_unsat
    (H : ∀ cs ∈ QueenDomSat.enumCases 48 24, (QueenDomSat.caseFormula 48 24 cs).Unsat) : gamma 48 = 25

theorem igamma_48_eq_25_of_formulas_unsat
    (H : ∀ cs ∈ QueenDomSat.enumCases 48 24, (QueenDomSat.caseFormula 48 24 cs).Unsat) : igamma 48 = 25
```

`gamma n` is the least size of a dominating set of the queen's graph on `Fin n × Fin n`, `igamma n` the least
size of an independent one, and `QueenDomSat.caseFormula n k cs : Std.Sat.CNF Nat` is the formula of a case,
defined in [lean-sat](lean-sat/QueenDomSat/Formula.lean). For every n and k ≤ n − 2, `lt_gamma_of_formulas_unsat`
says: if the formulas of all cases are unsatisfiable, then γ(Qₙ) > k.

## The proof

| step | statement | checked by |
| --- | --- | --- |
| upper bound | the 25 squares of `data/frame/q48_25_indep.json` dominate Q₄₈ and do not attack each other | kernel (`decide +kernel`) |
| Layer 1 (Davies) | a dominating set of 24 queens satisfies, after a board symmetry, the constraints `CaseSat` of one of 47,580 cases | kernel; pinned dependency |
| Layer 2 (here) | if `CaseSat n k cs D`, the formula of the case is satisfiable | kernel; `Queens48/` |
| certificates | each of the 47,580 formulas is unsatisfiable | CaDiCaL + drat-trim; compiled Lean checker |

Layer 2 is five files of 1,093 lines, to be read in this order; `Gamma48.lean` applies it to the board.

1. [Framework.lean](Queens48/Framework.lean). The encoder emits groups of clauses; a group started at the
   variable counter `nv` uses the fresh variables `nv + 1, ..., nv + m`. The one notion needed is `Sound A nv m P`:
   if the variables up to `nv` guarantee A, the fresh ones can be given values that guarantee P. Groups are
   chained by `Sound.append`. *Sequential counter*: let C(i) be the number of true literals among the first i
   and let s[i][j] mean j < C(i + 1); every clause follows from C(0) = 0, C(i) ≤ C(i + 1) ≤ C(i) + 1 and C ≤ k.
2. [Base.lean](Queens48/Base.lean). D makes the variables of its squares and of the lines through them true.
   Squares, rows, columns and the two sorts of diagonals are five instances of one structure, `Kind`.
3. [Waste.lean](Queens48/Waste.lean). On the border of the frame, the true waste literals count the three waste
   terms of the identities (F), (V), (H): `count_wasteValues`.
4. [Extra.lean](Queens48/Extra.lean). The identities are part of `CaseSat`, so the bounds (F), (V), (H) hold.
5. [Sound.lean](Queens48/Sound.lean). Together the groups give a satisfying assignment.

## Trust boundary

- The kernel checks the reduction, the encoding, the case list and the upper bound.
- The formulas were refuted by CaDiCaL 3.1.0 with DRAT proofs verified by drat-trim. Independently of both,
  `qdcheck` builds every formula with the Lean encoder and replays its LRAT certificate with the verified step
  functions of Lean's `Std.Tactic.BVDecide.LRAT`; it can report success only by holding a value of type
  `PLift (∀ cs ∈ enumCases 48 24, (caseFormula 48 24 cs).Unsat)`, the hypothesis `H` above. Recorded run:
  `s ALL VERIFIED n=48 k=24 cases=47580`, 810 s, 5 threads.
- Accepting that run means trusting the Lean compiler and runtime, including the `implemented_by` / `extern`
  replacements of core and Std, as `native_decide` does. The certificates are 148 GB of LRAT text, too much for
  the kernel, so there is no closed theorem without the named axiom.
- The certificates (25 GB compressed) are not in the repository; `data/frame/d_48_24.jsonl.xz` has the SHA-256 of
  every formula and certificate.
- Layer 2 covers the plain encoding, not the symmetry-breaking clauses and cubes used upstream for part of the
  n = 35 run. γ(Q₄₇) ∈ {24, 25} stays open.

## Reproduce

Lean 4.36.0 via `elan`; from this directory:

```sh
lake exe cache get && lake build        # the kernel-checked part
lake env lean Axioms48.lean             # axiom report (AXIOMS48.txt)
lake env lean Certified48.lean          # the closed statements, modulo the named axiom
lake env lean Replay48.lean             # kernel replay of the compiled modules (several minutes; REPLAY48.txt)
```

The computation needs `zstd`, CaDiCaL and drat-trim (`scripts/get_tools.sh`):

```sh
# about 10 CPU hours, 25 GB
python3 -I code/frame/run_cases48.py 48 24 --jobs 6 --tl 1800 --out runs/d_48_24.jsonl
# about 55 CPU minutes
cd lean-sat && lake build && cd ../lean-check && lake build
python3 -I scripts/run_check.py 48 24 ../runs/d_48_24.jsonl.lrat --jobs 5 \
    --log LOG.jsonl --summary SUMMARY.json --out STDOUT.txt
```

| case class | cases | CaDiCaL (CPU s) | drat-trim (CPU s) | LRAT text (GB) |
| --- | ---: | ---: | ---: | ---: |
| square box, deficit vector 0 | 819 | 14,584 | 7,214 | 64.39 |
| square box, positive deficit | 6,279 | 3,204 | 1,879 | 21.59 |
| non-square box, deficit vector 0 | 13,546 | 2,327 | 2,570 | 27.34 |
| non-square box, positive deficit | 26,936 | 1,669 | 3,493 | 35.14 |
| total | 47,580 | 21,784 | 15,156 | 148.46 |

## Files

- `Queens48/`: Layer 2 and the theorems. `Cases48*.lean` (generated by `scripts/gen_cases.py 48 24 data/frame
  Queens48 data/frame the`) additionally proves that the table of the 47,580 recorded cases is the case list; the
  theorems above do not use it.
- `lean-sat/`, `lean-check/`: the Lean encoder and the certificate checker (no Mathlib).
- `code/frame/`: the run driver, the search for the 25-queen sets, and Davies' unmodified `enc.py` and `geom.py`.
  `data/frame/`: records of the run, of its final check and of the certificate check, and the sets.
- `lean-sat/scripts/compare_enc.py` compares the Lean encoder with `enc.py`; its comparison with the records for
  n = 26, 32, 46 needs the data files of Davies' repository. So does the independent case-list check
  `code/frame/final_check40.py`, which is in that repository.

## Source and license

Davies' Lean development (Layer 1) is a Lake dependency pinned at commit `bc37cb0`. `enc.py`, `geom.py`,
`scripts/get_tools.sh` and `scripts/runlog.py` are his files, unmodified; `scripts/gen_cases.py` and
`code/frame/run_cases48.py` are modified from his, and `lean-sat` transcribes his encoder and case list into
Lean. His repository is licensed under Apache-2.0, and this directory keeps that license: see [LICENSE](LICENSE).
