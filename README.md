# Formal Math Lab — Lean 4 proofs and mathematical experiments

Formal proofs and reproducible computations in combinatorics, Ramsey theory,
finite algebra, and discrete geometry. Each project gives an exact mathematical
statement, Lean theorem names, build instructions, and original problem references.
The collection includes candidate new results and formalizations of known theorems.

## Proofs and results

The [prior-art audit](PRIOR_ART.md), checked on **22 November 2026**, distinguishes
these categories. “No earlier proof located” describes the sources searched;
it does not establish historical priority or imply that every lemma is new.

| Problem and identifiers | Result in this collection | Prior-art status |
| --- | --- | --- |
| [E1486, order 15: finite magma spectrum](E1486-order-15/) | No 15-element binary operation satisfies `(y*x)*(x*(z*z)) = x`. | No earlier proof located; order 15 remains open in the inspected Equational Theories catalogue. |
| [26 unit fractions: reciprocal Rado number f₂(26)](26-unit-fractions/) | `f₂(26) = 2028 = 3·26²`, with repeated denominators allowed; Gaiser–Ramezanpour Conjecture 1.3 at 26. | No earlier proof of this exact case located. The lower bound and some proof ingredients were already published. |
| [R₃²(C₇) = 11: seven-cycle Ramsey threshold](seven-cycle/) | Every 3-edge-coloring of `K₁₁` has a `C₇` with at most two cyclic color changes; a coloring of `K₁₀` avoids one. | No earlier proof of this exact threshold located. This is one finite case of Allen et al., Problem 22. |
| [Three-color prismatic T-tetromino ziggurats](three-color-t-boards/) | At least **45,083,592** labeled boards; also a small independent proof of **more than 60**. | No earlier proof of these stronger bounds located. Ma already proved existence of 60 boards. The unrestricted exact count remains unknown here. |
| [Nonattacking kings, Parks puzzles, OEIS A387098](nonattacking-kings/) | For positive row/column quota `k`, a nontrivial square board needs side at least `4k`; exactly two labeled arrangements attain equality. | **Known theorem:** the square case of Minevich et al., *Parks* (2024), Theorem 3. This project provides a Lean formalization. |

## Find and check a theorem

Each proof project below is an independent Lake project pinned to Lean **4.36.0** and
using Lean's standard library. With Lean's toolchain manager installed, run the
command in the corresponding directory. E1486's SAT checks and the large T-board
families can require substantial computation.

| Directory | Build command | Main Lean declaration |
| --- | --- | --- |
| `E1486-order-15` | `lake build +Simple.NoTable` | `E1486.Simple.noTable` |
| `26-unit-fractions` | `lake build` | `UnitFractions.forces_iff` |
| `seven-cycle` | `lake build` | `SevenCycle.exact_threshold` |
| `three-color-t-boards` | `lake build SplicePalCertificates` | `TBoards.at_least_45083592` |
| `three-color-t-boards` (small proof) | `lake build SimpleProof` | `TBoards.Simple.problem_solved` |
| `nonattacking-kings` | `lake build` | `Kings.lowerBound`, `Kings.exactlyTwo` |

The E1486 proof uses Lean's native certificate-checking machinery; see its
[trust and reproduction notes](E1486-order-15/README.md#reproduce).
Project documentation distinguishes mathematical proofs, verified finite
certificates, and exploratory searches. A timed-out search is not a proof.

## Research targets without a supplied proof

- [Width-12 snake polyominoes / OEIS A397153](width12-grid-snake/): the
  conjectured recurrence `s(n+6) = s(n) + 44` for `n ≥ 13`, for the maximum
  number of cells in an induced path in a `12 × n` grid. **No proof supplied.**
- **E670 on ten elements:** whether a 10-element magma satisfies
  `y*(x*((x*y)*y)) = x`. This is a research lead from the original shortlist;
  there is no local proof project. See the
  [Equational Theories spectrum catalogue](https://ohaithe.re/equational_theories/spectrum/?eq=670).

## Supporting tools and attribution

[lake-compat](https://github.com/Cameron-Lyons/lake-compat) is a separate
repository for explaining and testing Lean dependency upgrades. Its local
checkout may sit beside these projects; it is not a mathematical result.

Original problem references, known proofs, and the literature-search scope
are recorded in [PRIOR_ART.md](PRIOR_ART.md). The T-board project's
[source attribution](three-color-t-boards/README.md#source-and-attribution)
preserves Qiyuan Ma's licenses and credits. Existing component license notices
remain applicable; no collection-wide license replaces them.

For each added result, record its assumptions, named proof endpoint,
reproduction command, source problem identifier, and dated prior-art search.
Check general theorems and equivalent terminology as well as the exact title;
a conjecture label in a catalogue can be stale.
