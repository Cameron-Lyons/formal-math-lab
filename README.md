# Formal Math Lab — Lean 4 proofs and mathematical experiments

Formal proofs and reproducible computations in combinatorics, Ramsey theory,
finite algebra, and discrete geometry. Each project gives an exact mathematical
statement, Lean theorem names, build instructions, and original problem references.
The collection focuses on precisely stated results with dated prior-art checks.

## Proofs and results

The [prior-art audit](PRIOR_ART.md), updated **23 November 2026**, records
the evidence for each result. “No earlier proof located” describes the sources searched;
it does not establish historical priority or imply that every lemma is new.

| Problem and identifiers | Result in this collection | Prior-art status |
| --- | --- | --- |
| [E1486, order 15: finite magma spectrum](E1486-order-15/) | No 15-element binary operation satisfies `(y*x)*(x*(z*z)) = x`. | No earlier proof located; order 15 remains open in the inspected Equational Theories catalogue. |
| [E17260: partial finite-model obstructions](E17260-partial-results/) | Any model with surjective squaring, an idempotent, either cancellation law, or an affine operation is trivial. | Finite nontrivial existence remains open. Infinite models and finite linear obstructions are prior work; novelty of the other partial results is unverified. |
| [26 unit fractions: reciprocal Rado number f₂(26)](26-unit-fractions/) | `f₂(26) = 2028 = 3·26²`, with repeated denominators allowed; Gaiser–Ramezanpour Conjecture 1.3 at 26. | No earlier proof of this exact case located. The lower bound and some proof ingredients were already published. |
| [R₃²(C₇) = 11: seven-cycle Ramsey threshold](seven-cycle/) | Every 3-edge-coloring of `K₁₁` has a `C₇` with at most two cyclic color changes; a coloring of `K₁₀` avoids one. | No earlier proof of this exact threshold located. This is one finite case of Allen et al., Problem 22. |
| [Three-color prismatic T-tetromino ziggurats](three-color-t-boards/) | At least **45,083,592** labeled boards; also a small independent proof of **more than 60**. | No earlier proof of these stronger bounds located. Ma already proved existence of 60 boards. The unrestricted exact count remains unknown here. |
| [Three-column binary matrices (OEIS A401159)](three-column-matrices/) | The number of labeled `n × 3` binary matrices with at most two ones per row and per column is `H³ − n⁴ + C(n,2)`, where `H = 1 + n + C(n,2)`. | Confirms Mathar’s stated polynomial. An inclusion–exclusion formula published in 2001 implies this case. |
| [Manabe’s subtraction game with moves 3, 8, and 11k+7](manabe-residue-seven/) | For every `k ≥ 1`, exactly one heap has Grundy value 3, at size `11k+10`. | No earlier proof of the singleton statement for all positive `k` was located. REUF working notes anticipate the repeating block. |
| [Binomial recurrence (OEIS A026019)](a026019-binomial-recurrence/) | Mathar’s three-term polynomial recurrence holds for `a(n) = C(3n,n) − C(3n,n−3)` at every `n ≥ 2`, with negative lower binomial indices interpreted as zero. | No earlier explicit proof located; a first-order recurrence implemented in jOEIS on 6 November 2026 implies it. Historical priority is unverified. |
| [Nonlinear-to-linear recurrence (OEIS A176755)](a176755-linear-recurrence/) | Mathar’s five-term polynomial recurrence holds for every `n ≥ 4`, starting from `a₀ = 1`, `a₁ = 3`, and the nonlinear convolution recurrence. | Covered by Georg Fischer’s January 2020 general recurrence. This project supplies a Lean proof; first-formalization status is unverified. |

## Find and check a theorem

Each proof project below is an independent Lake project pinned to Lean **4.36.0**.
The E17260, three-column matrix, A026019, and A176755 projects also use mathlib **v4.36.0**.
With Lean's toolchain manager installed, run the command in the corresponding directory.
E1486's SAT checks and the large T-board
families can require substantial computation.

| Directory | Build command | Main Lean declaration |
| --- | --- | --- |
| `E1486-order-15` | `lake build +Simple.NoTable` | `E1486.Simple.noTable` |
| `E17260-partial-results` | `lake build` | `Equation17260.subsingleton_of_surjective_square` |
| `26-unit-fractions` | `lake build` | `UnitFractions.forces_iff` |
| `seven-cycle` | `lake build` | `SevenCycle.exact_threshold` |
| `three-color-t-boards` | `lake build SplicePalCertificates` | `TBoards.at_least_45083592` |
| `three-color-t-boards` (small proof) | `lake build SimpleProof` | `TBoards.Simple.problem_solved` |
| `three-column-matrices` | `lake build` | `ThreeColumnMatrices.card_validMatrices` |
| `manabe-residue-seven` | `lake build` | `SubtractionGame.grundy_eq_three_iff` |
| `a026019-binomial-recurrence` | `lake build` | `A026019.recurrence` |
| `a176755-linear-recurrence` | `lake build` | `A176755.mathar` |

The E1486 proof uses Lean's native certificate-checking machinery; see its
[trust and reproduction notes](E1486-order-15/README.md#reproduce).
Project documentation distinguishes mathematical proofs, verified finite
certificates, and exploratory searches. A timed-out search is not a proof.

## Research targets without a supplied proof

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
preserves Qiyuan Ma's licenses and credits. See [License](#license) for the
collection's MIT license and the components with separate license notices.

For each added result, record its assumptions, named proof endpoint,
reproduction command, source problem identifier, and dated prior-art search.
Check general theorems and equivalent terminology as well as the exact title;
a conjecture label in a catalogue can be stale.

## License

Original collection material is licensed under the [MIT License](LICENSE),
except material carrying separate license or attribution notices:

- [E1486-order-15](E1486-order-15/LICENSE) retains its Apache-2.0 license and
  the copyright notice of the Equational Theories Project contributors.
- Qiyuan Ma's manuscript, certificate data, documentation, and recorded
  outputs in [three-color-t-boards/sources](three-color-t-boards/sources/LICENSE_SCOPE.txt)
  retain CC-BY-4.0. The supplied Python programs retain their MIT license
  and original copyright notice.
- Ma's attribution also applies to the first five representatives and their
  symmetry images reused in the T-board data; see
  [source and attribution](three-color-t-boards/README.md#source-and-attribution).

The root MIT license does not replace these notices or relicense third-party
material.
