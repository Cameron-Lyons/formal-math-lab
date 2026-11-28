# Queen domination on the $48 \times 48$ board by SAT certificates: $\gamma(Q_{48}) = i(Q_{48}) = 25$

Place chess queens on a $48 \times 48$ board so that every square is either occupied or attacked:
- The **domination number** $\gamma(Q_{48})$ is the fewest queens needed to cover all 2,304 squares.
- The **independent domination number** $i(Q_{48})$ is the fewest **pairwise non-attacking** queens needed to cover all 2,304 squares (always $\gamma \le i$).

We prove that no 24 queens can dominate the $48 \times 48$ board (even if allowed to attack each other), whereas 25 mutually non-attacking queens can—settling both values at once: **$\gamma(Q_{48}) = i(Q_{48}) = 25$**.

This provides a second proof of $\gamma(Q_{48}) = 25$, independent of the non-SAT enumeration in [queen-domination-48](../queen-domination-48/), and adds an explicit formal proof of $i(Q_{48}) = 25$. It builds on Jason Davies' [queen-domination](https://github.com/jasondavies/queen-domination) **frame method** and Boolean satisfiability (SAT) encoding:
1. **Lean's kernel** proves the complete reduction from a 24-queen dominating set to **47,580** explicit Conjunctive Normal Form (CNF) formulas, including full soundness of the CNF encoding for *every* board size.
2. **Certified computation outside the kernel** refutes all 47,580 formulas: a SAT solver (CaDiCaL) and proof trimmer (`drat-trim`) emit **LRAT certificates** (step-by-step refutation logs with clause hints), which are then replayed and verified by a proof-carrying compiled Lean checker ([lean-check](lean-check/)).

| Field | Summary |
| --- | --- |
| Problem & identifiers | `gamma(Q_48)` and `i(Q_48)`, queen's graph $Q_{48}$; Östergård and Weakley (Electron. J. Combin. 8 (2001) #R29) showed both lie in $\{24, 25\}$; Davies §9 (`hexagonmath.org/pdf/2611.00830v1`) |
| Kernel-checked | `gamma_48_le`, `igamma_48_le` ($\le 25$, unconditional); `gamma_48_eq_25_of_formulas_unsat`, `igamma_48_eq_25_of_formulas_unsat` ($= 25$ assuming the 47,580 formulas are unsatisfiable). Axioms: `propext`, `Classical.choice`, `Quot.sound`. |
| Outside the kernel | Unsatisfiability of all 47,580 formulas, refuted by CaDiCaL + `drat-trim` and verified from LRAT certificates by a compiled Lean checker ([lean-check](lean-check/)). |
| Closed statement | `gamma_48 : gamma 48 = 25` in [Certified48.lean](Certified48.lean), assuming one named axiom for the certificate check. |
| Prior art | Re-audited 26 November 2026: Aleksej Đukić proved $\gamma(Q_{48}) = 25$ on 22 November 2026 (OEIS A075458, `10.5281/zenodo.24537292`) using the same 47,580-case Davies frame split, which together with Östergård and Weakley's (2001) independent 25-queen set implied $i(Q_{48}) = 25$. This folder adds Lean kernel soundness for the CNF encoding, compiled Lean LRAT verification, and an explicit proof of $i(Q_{48}) = 25$. |
| Review | Produced and re-checked by AI agents; no human has reviewed it. |

## The Lean statements

```lean
theorem igamma_48_le : igamma 48 ≤ 25

theorem gamma_48_eq_25_of_formulas_unsat
    (H : ∀ cs ∈ QueenDomSat.enumCases 48 24, (QueenDomSat.caseFormula 48 24 cs).Unsat) : gamma 48 = 25

theorem igamma_48_eq_25_of_formulas_unsat
    (H : ∀ cs ∈ QueenDomSat.enumCases 48 24, (QueenDomSat.caseFormula 48 24 cs).Unsat) : igamma 48 = 25
```

Here:
- `gamma n` is the minimum size of a dominating set of the queen's graph on `Fin n × Fin n`,
- `igamma n` is the minimum size of an independent (pairwise non-attacking) dominating set, and
- `QueenDomSat.caseFormula n k cs : Std.Sat.CNF Nat` is the CNF formula for case `cs`, defined in [lean-sat](lean-sat/QueenDomSat/Formula.lean).

In full generality, for every board size $n$ and every $k \le n - 2$, `lt_gamma_of_formulas_unsat` proves that if all case formulas are unsatisfiable, then $\gamma(Q_n) > k$.

## Proof architecture

Instead of asking a SAT solver to handle one giant $48 \times 48$ formula directly, Davies' **frame method** classifies any hypothetical 24-queen placement by the margins of its bounding box and its row/column/diagonal deficits, breaking the search into 47,580 small cases. The formal proof stacks four clean layers:

| Step | Statement | Checked by |
| --- | --- | --- |
| Upper bound | The 25 squares of `q48i` in [Gamma48.lean](Queens48/Gamma48.lean) dominate $Q_{48}$ and do not attack each other | Kernel (`decide +kernel`) |
| Layer 1 (Davies) | Any dominating set of 24 queens satisfies, up to board symmetry, the geometric constraints `CaseSat` of one of 47,580 cases | Kernel (pinned dependency) |
| Layer 2 (here) | If a dominating set `D` satisfies `CaseSat n k cs D`, then `caseFormula n k cs` is satisfiable | Kernel (`Queens48/`) |
| Certificates | Each of the 47,580 formulas is unsatisfiable | CaDiCaL + `drat-trim`; compiled Lean checker |

### Reading guide for Layer 2 (`Queens48/`)

Layer 2 spans five short modules totaling 1,093 lines (intended to be read in order), after which `Gamma48.lean` specializes the theorem to the $48 \times 48$ board:

1. [Framework.lean](Queens48/Framework.lean) — **Compositional clause-group soundness and sequential counters:** The CNF encoder emits clauses in modular groups. A group starting at variable counter `nv` introduces fresh variables `nv + 1, ..., nv + m`. The central invariant is `Sound A nv m P`: whenever variables up to `nv` satisfy precondition `A`, the fresh variables can be assigned to satisfy postcondition `P`. Groups compose cleanly via `Sound.append`. For cardinality constraints encoded via a sequential counter, letting $C(i)$ count the true literals among the first $i$ inputs and interpreting auxiliary variable `s[i][j]` as $j < C(i + 1)$, every counter clause follows from $C(0) = 0$, $C(i) \le C(i + 1) \le C(i) + 1$, and $C \le k$.
2. [Base.lean](Queens48/Base.lean) — **Base queen-domination encoding:** A dominating set `D` assigns `true` to the variables for its occupied squares and the lines passing through them. Squares, rows, columns, and both diagonal directions are handled uniformly as five instances of one structure, `Kind`.
3. [Waste.lean](Queens48/Waste.lean) — **Border waste accounting:** Along the border of the bounding frame, the true waste literals exactly count the three waste terms appearing in Davies' geometric identities (F), (V), and (H) (`count_wasteValues`).
4. [Extra.lean](Queens48/Extra.lean) — **Case-specific constraints:** Those identities are guaranteed by `CaseSat`, so the cardinality bounds (F), (V), and (H) are satisfied.
5. [Sound.lean](Queens48/Sound.lean) — **Assembly:** Composing all clause groups produces a complete satisfying assignment for `caseFormula n k cs`.

## Trust boundary

- **Verified by Lean's kernel:** The 25-queen independent upper bound, Layer 1's case split (`enumCases 48 24`), Layer 2's CNF encoding soundness, and the conditional main theorems (using only `propext`, `Classical.choice`, `Quot.sound`).
- **Verified by compiled Lean code (`qdcheck`):** CaDiCaL 3.1.0 refuted all 47,580 formulas with DRAT proofs trimmed into LRAT by `drat-trim`. Independently of both tools, `qdcheck` builds every formula with the verified Lean encoder and replays its LRAT certificate using the verified step functions of Lean's `Std.Tactic.BVDecide.LRAT`. By type-checking, `qdcheck` can print success *only* by constructing a value of type `PLift (∀ cs ∈ enumCases 48 24, (caseFormula 48 24 cs).Unsat)`—the exact hypothesis `H` above. The recorded run printed `s ALL VERIFIED n=48 k=24 cases=47580` in 810 s on 5 threads.
- **Compiler/runtime trust and named axiom:** Accepting that run trusts the Lean compiler and runtime, including `implemented_by` and `extern` replacements in Lean core and Std (the same trust model as `native_decide`). Because the 47,580 LRAT certificates total **148 GB** of text—far too large for Lean's kernel to replay—the closed theorem `gamma_48 : gamma 48 = 25` in [Certified48.lean](Certified48.lean) isolates that certificate check as one named axiom.
- **Certificate storage:** The 25 GB of compressed certificates are not stored in this repository.
- **Scope note:** Layer 2 covers the plain encoding only (not the symmetry-breaking clauses and cubes used upstream for part of the $n = 35$ run). The value of $\gamma(Q_{47}) \in \{24, 25\}$ remains open.

## Reproduce

### 1. Kernel-checked Lean proofs

With Lean 4.36.0 via `elan`, run from this directory:

```sh
lake exe cache get && lake build        # the kernel-checked part
lake env lean Certified48.lean          # the closed statements, modulo the named axiom
```

### 2. Full SAT solving and Lean LRAT verification

Reproducing the SAT refutations and certificate checks requires `zstd`, CaDiCaL, and `drat-trim` (`scripts/get_tools.sh`):

```sh
# about 10 CPU hours, 25 GB
python3 -I code/frame/run_cases48.py 48 24 --jobs 6 --tl 1800 --out runs/d_48_24.jsonl
# about 55 CPU minutes
cd lean-sat && lake build && cd ../lean-check && lake build
python3 -I scripts/run_check.py 48 24 ../runs/d_48_24.jsonl.lrat --jobs 5 \
    --log LOG.jsonl --summary SUMMARY.json --out STDOUT.txt
```

Breakdown of the 47,580 cases in the recorded SAT run:

| Case class | Cases | CaDiCaL (CPU s) | drat-trim (CPU s) | LRAT text (GB) |
| --- | ---: | ---: | ---: | ---: |
| square box, deficit vector 0 | 819 | 14,584 | 7,214 | 64.39 |
| square box, positive deficit | 6,279 | 3,204 | 1,879 | 21.59 |
| non-square box, deficit vector 0 | 13,546 | 2,327 | 2,570 | 27.34 |
| non-square box, positive deficit | 26,936 | 1,669 | 3,493 | 35.14 |
| total | 47,580 | 21,784 | 15,156 | 148.46 |

## Files

- `Queens48/`: Layer 2 and the main theorems.
- `lean-sat/` and `lean-check/`: the Mathlib-free Lean CNF encoder and proof-carrying LRAT certificate checker.
- `code/frame/`: the run driver (`run_cases48.py`) and Davies' unmodified `enc.py` and `geom.py`.

## Source and license

Davies' Lean development (Layer 1) is a Lake dependency pinned at commit `bc37cb0`. The files `enc.py`, `geom.py`, and `scripts/get_tools.sh` are taken from his repository unmodified. `code/frame/run_cases48.py` is modified from his version, and `lean-sat` transcribes his encoder and case list into Lean. His repository uses the Apache-2.0 license, and this directory keeps that license (see [LICENSE](LICENSE)).
