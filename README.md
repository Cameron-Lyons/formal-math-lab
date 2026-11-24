# Formal Math Lab — Lean 4 proofs and mathematical experiments

Formal proofs and reproducible computations in combinatorics, Ramsey theory,
finite algebra, number theory, and discrete geometry. Each project gives an exact mathematical
statement, Lean theorem names, build instructions, and original problem references.
The collection focuses on precisely stated results with dated prior-art checks.

## Proofs and results

The [prior-art audit](PRIOR_ART.md), updated **24 November 2026**, records
the evidence for each result. “No earlier proof located” describes the sources searched;
it does not establish historical priority or imply that every lemma is new.

| Problem and identifiers | Result in this collection | Prior-art status |
| --- | --- | --- |
| [Nine-bit snake-in-the-box](nine-bit-snake/) | Keep the first 156 steps of any published 191-step snake, read from either end. Every 191-step completion belongs to a published class, and none reaches 192 steps. | Orland et al. published the 131 classes. The unrestricted 192-step question remains open. |
| [42 consecutive-size squares, Friedman problem 10](consecutive-squares-21/) | With two squares of each side from 1 through 21, the only possible rectangle is 77 × 86, up to rotation. | Friedman lists this case as open. The search found no earlier proof excluding 43 × 154. |
| [Five 30-sided Go First Dice](five-30-sided-dice/) | For all 120 rankings to have equal odds, each die must have a face at which two opponents’ counts of higher labels differ modulo four. Lean also excludes fifteen mirrored permutation blocks. | The unrestricted problem remains open. An earlier search excluded all column-grouped labelings, including the mirrored blocks. Priority of the modulo-four condition is unconfirmed. |
| [Triple covering design $C(61,25,3)$](covering-61-25-3/) | Any 26-group cover can retain at most 20 groups from the published construction. Lean checks all 296,010 choices of 21 retained groups. | Caleb Ashton published the 27-group construction. The unrestricted 26-group question remains open in this project. |
| [E677 implies E255 at order 9](E677-E255-order-9/) | Every nine-element magma satisfying E677 also satisfies E255. | José Brox reported the order-nine exclusion in December 2024. |
| [E670, order 10: finite magma spectrum](E670-order-10/) | No 10-element binary operation satisfies `y*(x*((x*y)*y)) = x`. | No earlier proof located; order 10 remains open in the inspected Equational Theories catalogue. |
| [E1486, order 15: finite magma spectrum](E1486-order-15/) | No 12-element or 15-element binary operation satisfies `(y*x)*(x*(z*z)) = x`. A 17-element one and a 26-element one do. | No earlier proof of any of the four located; orders 12, 15, 17 and 26 remain open in the inspected Equational Theories catalogue. |
| [E17260: partial finite-model obstructions](E17260-partial-results/) | Any model with surjective squaring, an idempotent, either cancellation law, or an affine operation is trivial. | Finite nontrivial existence remains open. Infinite models and finite linear obstructions are prior work; novelty of the other partial results is unverified. |
| [Integer cubic $z^2+y^2z+x^3=2$](integer-cubic/) | A nonconstant rational polynomial family passing through an integer triple must have degree at least six in $x$. An explicit infinite family has integral $x,z$ and $y$ of reduced denominator 13. A rational quartic substitution on $u^2-3v^2=1$ with nonconstant $x$ and one integral seed would prove infinitude. | Infinitude of integer triples remains open in Grechuk’s Table 6. |
| [Three integer cubes summing to 114](three-cubes-114/) | Arbitrarily large moduli admit a cube root of 114 and lie outside the full norm family. | Booker–Sutherland and Grantham–Walsh give earlier search methods. The local searches found no triple. |
| [26 unit fractions: reciprocal Rado number f₂(26)](26-unit-fractions/) | `f₂(26) = 2028 = 3·26²`, with repeated denominators allowed; Gaiser–Ramezanpour Conjecture 1.3 at 26. | No earlier proof of this exact case located. The lower bound and some proof ingredients were already published. |
| [Erdős #556, three-color nine-cycle Ramsey number](erdos-556-cycle-ramsey/) | Any three-coloring of $K_{33}$ with a 15-vertex set missing one color contains a monochromatic $C_9$. | The lower bound of 33 is known. The unrestricted upper bound remains open. |
| [Erdős #617, missing colors in cliques](erdos-617-missing-colors/) | The missing-color conclusion holds for $3\le r\le 10$, and for every $r\ge3$ if one color contains $r-2$ disjoint copies of $K_r$. | Erdős and Gyárfás posed the conjecture. The unrestricted case remains open. |
| [Erdős #677, equal LCMs of three, four and six consecutive integers](erdos-677-equal-lcms/) | At lengths three and four the only equal-LCM pairs have parameters $(2,3)$ and $(1,2)$ respectively, proved entirely in Lean. At length six they are $(3,4)$, $(5,6)$ and $(13,15)$: Lean checks the reduction and finite cases, and external elliptic-curve arithmetic proves completeness. All these pairs overlap. | The classifications at lengths three and four, the three length-six overlaps and the four-cubic reduction were recorded previously. No earlier Lean proof of lengths three or four located. The arbitrary-length problem remains open. |
| [Erdős #708, interval products for six integers](erdos-708-six/) | $g(6)=8$. For every six-element set $A$ of integers at least two, at most eight entries from any block of $\max A$ consecutive integers suffice for a product divisible by $\prod_{a\in A}a$. Some blocks require eight. | C. Bergström previously proved the value eight. The local Lean proof uses John Tripodo’s formalized bounds for four and five integers. |
| [Erdős #835, coloring subsets](erdos-835-coloring-subsets/) | At $k=16$, any point involution preserving a rainbow coloring must move at least 30 of the 32 points. Lean also excludes symmetries of order 11 or 13 and regular abelian groups of order 32. | Earlier work excludes other symmetry classes. The existence of a coloring remains open. |
| [Written on the Wall II #133, floored formulation](written-on-the-wall-133/) | The inequality holds for all connected graphs on at most 29 vertices, at every order when $\lfloor l(G)\rfloor\le4$, and for all connected bipartite or regular graphs. | Chen previously treated floors through two. The general floored inequality remains unresolved here. |
| [R₃²(C₇) = 11: seven-cycle Ramsey threshold](seven-cycle/) | Every 3-edge-coloring of `K₁₁` has a `C₇` with at most two cyclic color changes; a coloring of `K₁₀` avoids one. | No earlier proof of this exact threshold located. This is one finite case of Allen et al., Problem 22. |
| [Book Ramsey number $R(B_{63},B_{64})$](book-ramsey/) | $253 \le R(B_{63},B_{64}) \le 255$. The 252-vertex witness has at most 62 pages on every spine in either color. | The bounds follow from Dai–Lin and Rousseau–Sheehan. Chung and Wesley list the 254-vertex construction as open. |
| [Ramsey number $R(3,10)$](ramsey-3-10/) | Exoo’s 39-vertex graph gives $R(3,10) \ge 40$. Every one-vertex extension contains a triangle or an independent ten-set. | Exoo proved the lower bound. Angeltveit proved $R(3,10) \le 41$. The exact value remains open. |
| [No three in line on the 75 × 75 grid](no-three-in-line-75/) | The maximum is 148, 149, or 150. Any 150-point solution must omit two points of the checked 148-point configuration whose row indices differ by at least 32. | The 148 points come from Prellberg’s 74 × 74 configuration. The existence of 150 points remains open here. |
| [Three-color prismatic T-tetromino ziggurats](three-color-t-boards/) | At least **45,083,592** labeled boards; also a small independent proof of **more than 60**. | No earlier proof of these stronger bounds located. Ma already proved existence of 60 boards. The unrestricted exact count remains unknown here. |
| [Three-column binary matrices (OEIS A401159)](three-column-matrices/) | The number of labeled `n × 3` binary matrices with at most two ones per row and per column is `H³ − n⁴ + C(n,2)`, where `H = 1 + n + C(n,2)`. | Confirms Mathar’s stated polynomial. An inclusion–exclusion formula published in 2001 implies this case. |
| [Manabe’s subtraction game with moves 3, 8, and 11k+7](manabe-residue-seven/) | For every `k ≥ 1`, exactly one heap has Grundy value 3, at size `11k+10`. | No earlier proof of the singleton statement for all positive `k` was located. REUF working notes anticipate the repeating block. |
| [Binomial recurrence (OEIS A026019)](a026019-binomial-recurrence/) | Mathar’s three-term polynomial recurrence holds for `a(n) = C(3n,n) − C(3n,n−3)` at every `n ≥ 2`, with negative lower binomial indices interpreted as zero. | No earlier explicit proof located; a first-order recurrence implemented in jOEIS on 6 November 2026 implies it. Historical priority is unverified. |
| [Nonlinear-to-linear recurrence (OEIS A176755)](a176755-linear-recurrence/) | Mathar’s five-term polynomial recurrence holds for every `n ≥ 4`, starting from `a₀ = 1`, `a₁ = 3`, and the nonlinear convolution recurrence. | Covered by Georg Fischer’s January 2020 general recurrence. This project supplies a Lean proof; first-formalization status is unverified. |
| [Arctangent-sum conjecture (arXiv:2607.05739)](arctangent-sum/) | The number of integer-valued indices through $N$ is $O((\log N)^{3/4})$. Through $10^6$, only $n=1,2,3,4$ give integer values at positive indices. | Ono proved $O(\log N)$. Formal Conjectures lists the exclusion of every $n \geq 5$ as open. |

## Find and check a theorem

Each proof has its own Lake project. The Erdős #617, #677, #708, and #835 projects use Lean **4.35.0-rc2**.
The Written on the Wall II #133 project uses Lean and mathlib **4.33.1**.
The #708 project includes Tripodo’s pinned development. The other projects use Lean **4.36.0**.
The E17260, integer cubic, three cubes, three-column matrix, A026019, A176755, and arctangent-sum projects also use mathlib **v4.36.0**.
With Lean's toolchain manager installed, run the command in the corresponding directory.
The E670 and E1486 SAT checks and the large T-board
families can require substantial computation.

| Directory | Build command | Main Lean declaration |
| --- | --- | --- |
| `nine-bit-snake` | `lake build` | `Snake.bank_no_192`, `Snake.bank_no_new_191`, `Snake.outside_bank_of_end_profiles` |
| `consecutive-squares-21` | `lake build` | `Squares42.exists_tiling_iff_77_by_86` |
| `five-30-sided-dice` | `lake build` | `FiveDice.EqualCuts.needs_distinct_residues`, `FiveDice.Mirrored.no_fifteen_mirrored` |
| `covering-61-25-3` | `lake build` | `Covering61.RepairSearch.published_six_for_five_screen` |
| `E677-E255-order-9` | `lake build` | `Nine.eq677_implies_eq255` |
| `E670-order-10` | `lake build` | `E670.no_model_of_order_ten` |
| `E1486-order-15` | `lake build +Simple.NoTable` | `E1486.Simple.noTable` |
| `E1486-order-15` (order 12) | `lake build Simple.Order12.NoTable` | `E1486.Order12.noTable` |
| `E1486-order-15` (order 17) | `lake build Simple.Order17` | `E1486.Order17.exists_table` |
| `E1486-order-15` (order 26) | `lake build Simple.Order26` | `E1486.Order26.exists_table` |
| `E17260-partial-results` | `lake build` | `Equation17260.subsingleton_of_surjective_square` |
| `integer-cubic` | `lake build` then `lake exe boundedSearch` | `IntegerCubic.infinitely_many_with_two_integer_coordinates` |
| `integer-cubic` (Pell substitutions) | `lake build SmallCubic` | `SmallCubic.MixedPell.infinite_of_nonconstant_quartic_chart`, `SmallCubic.QuinticSquareObstruction.no_negative_square_lift` |
| `three-cubes-114` | `lake build` | `ThreeCubes114.TernaryNorm.unbounded_normalized_moduli` |
| `26-unit-fractions` | `lake build` | `UnitFractions.forces_iff` |
| `erdos-556-cycle-ramsey` | `lake build` | `Ramsey556.monoC9_of_independent15`, `Ramsey556.k33_iff_final_two_cases` |
| `erdos-617-missing-colors` | `lake exe cache get` then `lake build` | `Erdos617.missing_of_at_most_ten_colors`, `Erdos617.missing_of_all_but_two_parallel_rows` |
| `erdos-677-equal-lcms` | `lake exe cache get` then `lake build`. [Arithmetic checks](erdos-677-equal-lcms/cubic/LengthSix.md#reproduction) | `Erdos677.three_collision_iff`, `Erdos677.four_collision_iff`, `Erdos677.six_collision_iff_three_of_affine_cover` |
| `erdos-708-six` | `lake exe cache get` then `lake build` | `Erdos708.isLeast_six`, `IntervalSix.six_integer` |
| `erdos-835-coloring-subsets` | `lake exe cache get` then `lake build` | `Erdos835.involution_moves_at_least_thirty`, `Erdos835.no_regular_abelian_symmetry` |
| `written-on-the-wall-133` | `lake exe cache get` then `lake build` | `Wall133.floored_of_order_le_29`, `Wall133.floored_of_floor_le_four` |
| `seven-cycle` | `lake build` | `SevenCycle.exact_threshold` |
| `book-ramsey` | `lake build` | `BookRamsey.Lower252.exists_252`, `BookRamsey.Upper255.upper` |
| `ramsey-3-10` | `lake build` | `Ramsey310.ramsey_lower_bound`, `Ramsey310.exoo_no_one_vertex_extension` |
| `no-three-in-line-75` | `lake build` | `Grid75.maximum_in_range`, `Grid75.omitted_rows_separated` |
| `three-color-t-boards` | `lake build SplicePalCertificates` | `TBoards.at_least_45083592` |
| `three-color-t-boards` (small proof) | `lake build SimpleProof` | `TBoards.Simple.problem_solved` |
| `three-column-matrices` | `lake build` | `ThreeColumnMatrices.card_validMatrices` |
| `manabe-residue-seven` | `lake build` | `SubtractionGame.grundy_eq_three_iff` |
| `a026019-binomial-recurrence` | `lake build` | `A026019.recurrence` |
| `a176755-linear-recurrence` | `lake build` | `A176755.mathar` |
| `arctangent-sum` | `lake build` | `Arxiv.«2607.05739».positive_integer_count_isBigO` |

The E670 and E1486 proofs use Lean's native certificate-checking machinery; see
the trust and reproduction notes for
[E670](E670-order-10/README.md#reproduce) and
[E1486](E1486-order-15/README.md#reproduce).
Project documentation distinguishes mathematical proofs, verified finite
certificates, and exploratory searches. A timed-out search is not a proof.

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

- [Written on the Wall II #133](written-on-the-wall-133/LICENSE) retains its Apache-2.0 license, including the attribution in the [adapted radius bound](written-on-the-wall-133/Wall133/Chung.lean).
- [E1486-order-15](E1486-order-15/LICENSE) retains its Apache-2.0 license and
  the copyright notice of the Equational Theories Project contributors.
- The Formal Conjectures interval definition in [UpstreamInterval.lean](erdos-677-equal-lcms/UpstreamInterval.lean) retains its [Apache-2.0 license](erdos-677-equal-lcms/LICENSE-FormalConjectures) and copyright notice.
- The four definitions from Formal Conjectures in
  [ArctanBridge.lean](arctangent-sum/ArctanBridge.lean) retain their Apache-2.0
  license and copyright notice.
- Qiyuan Ma's manuscript, certificate data, documentation, and recorded
  outputs in [three-color-t-boards/sources](three-color-t-boards/sources/LICENSE_SCOPE.txt)
  retain CC-BY-4.0. The supplied Python programs retain their MIT license
  and original copyright notice.
- Ma's attribution also applies to the first five representatives and their
  symmetry images reused in the T-board data; see
  [source and attribution](three-color-t-boards/README.md#source-and-attribution).

The root MIT license does not replace these notices or relicense third-party
material.
