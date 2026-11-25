# Formal Math Lab

Lean 4 proofs, finite-case solutions, obstructions, and computational checks across combinatorics, Ramsey theory, finite algebra (Equational Theories Project), number theory, Erdős problems, OEIS conjectures, and discrete geometry.

Each folder is a self-contained Lake package with the mathematical statement, references (arXiv, DOI, OEIS, Erdős problem number, or ETP equation number), Lean theorem names, reproduction commands, and trust boundaries. Literature checks are recorded in [PRIOR_ART.md](PRIOR_ART.md) (updated 25 November 2026); "no earlier proof located" refers only to the sources checked and does not claim absolute priority.

## Settled problems, exact values, and proved recurrences

These folders settle a finite open case, determine an exact parameter value, or prove or refute a conjecture or recurrence in Lean 4.

| Problem | Result proved here | Prior art and status |
| --- | --- | --- |
| [Box-free 2-colorings of the 6 x 7 x n grid](box-free-6x7/) (Genkin Question 8.1, `10.5281/zenodo.24457907`) | Exact maximum height is $n = 52$. Lean kernel-checks an explicit 52-layer box-free coloring and proves $n \le 52$. | Genkin constructed 50 layers, proved $n \le 52$, and asked in Question 8.1 whether 52 is attainable. |
| [Queen domination on the 48 x 48 chessboard](queen-domination-48/) ($\gamma(Q_{48}) = 25$, Davies §9, `hexagonmath.org/pdf/2611.00830v1`) | Exact minimum is $\gamma(Q_{48}) = 25$ queens. Compiled Lean enumeration rules out 24 queens and checks a 25-queen cover of all 2,304 squares. | Östergård and Weakley gave the 25-queen upper bound. Davies listed $48 \times 48$ as the next open even board on 21 November 2026. |
| [Queen domination on the 48 x 48 board by SAT certificates](queen-domination-48-sat/) ($\gamma(Q_{48}) = i(Q_{48}) = 25$, Jason Davies frame method) | $\gamma(Q_{48}) = i(Q_{48}) = 25$: an independent second proof, plus the independent domination number. Lean's kernel proves the reduction to 47,580 CNF formulas (including the encoding) and checks a 25-queen independent dominating set; a compiled Lean program checks the LRAT certificates outside the kernel. | Östergård and Weakley had both numbers in $\{24, 25\}$. Frame method and encoder by Jason Davies. No earlier determination of $i(Q_{48})$ was located in a brief search. |
| [Equation 1486 finite magma spectrum](E1486-order-15/) (`x = (y ◇ x) ◇ (x ◇ (z ◇ z))`, orders 12, 14, 15, 17, 26; dual E2126) | No magma of order 12, 14, or 15; explicit magmas of order 17 and 26 exist. Settles the five orders left open in the ETP spectrum catalogue (combined with the fork's bounds, excluded orders are `2, 3, 5, 6, 7, 8, 10, 12, 14, 15`). | No earlier proof or model located for any of the five orders in the inspected sources (22-24 November 2026). |
| [Equation 670 at order 10](E670-order-10/) (`x = y ◇ (x ◇ ((x ◇ y) ◇ y))`, dual E2937) | No 10-element magma satisfies Equation 670 (SAT/LRAT refutation checked in Lean). Also verifies affine models at orders `19, 29, 31, 41, 59, 61`. | No earlier order-10 exclusion located; 10 was the smallest undecided order in the inspected ETP spectrum catalogue (23 November 2026). |
| [Equation 677 at orders 9 and 10, and E677 -> E255](E677-E255-order-9/) (`x = y ◇ (x ◇ ((y ◇ x) ◇ y))`, `x = ((x ◇ x) ◇ x) ◇ x`) | Order 9: every 9-element E677 magma satisfies E255. Order 10: no 10-element magma satisfies E677. | Formalizes José Brox's Mace4 reports (Dec 2024 and Jan 2025). No earlier Lean proof of order 10 located. General finite `E677 -> E255` remains open. |
| [Reciprocal Rado number `f_2(26) = 2028`](26-unit-fractions/) (`1/x_1 + ... + 1/x_26 = 1/y`, Gaiser-Ramezanpour Conjecture 1.3, `arXiv:2607.04373`) | Exact value $f_2(26) = 2028 = 3 \cdot 26^2$ (with repeated denominators allowed), proved in pure Lean 4. | No earlier proof of the 26-summand upper bound located; lower bound and initial identities are from Gaiser and Ramezanpour. General $f_2(k) = 3k^2$ remains open. |
| [Seven-cycle Ramsey threshold `R_3^2(C_7) = 11`](seven-cycle/) (at most 2 cyclic color changes, Allen et al. Problem 22, `arXiv:2607.03243`) | Exact threshold $R_3^2(C_7) = 11$. Every 3-edge-coloring of $K_{11}$ has a $C_7$ with $\le 2$ cyclic color changes; an explicit coloring of $K_{10}$ avoids one. | No earlier proof of this exact threshold located. Settles one finite case of Allen, Böttcher, Clemens, Hamann, Skokan, and Taraz Problem 22. |
| [Manabe's subtraction game `{3, 8, 11k + 7}`](manabe-residue-seven/) (`arXiv:2609.05358` Example 1) | For every $k \ge 1$, the unique heap with Grundy value 3 is $n = 11k + 10$, with least preperiod $11k + 11$ and eventual period $11k + 10$. | No earlier proof of the singleton-3 statement for all $k \ge 1$ located; REUF working notes anticipate the repeating block. |
| [Erdős Problem #708 for six integers: `g(6) = 8`](erdos-708-six/) (`erdosproblems.com/708`) | Exact value $g(6) = 8$. Every block of $\max A$ consecutive integers contains at most 8 distinct entries whose product is divisible by $\prod_{a \in A} a$ for $|A| = 6$, and 8 is sharp. | Formalizes C. Bergström's proof of $g(6) = 8$ (`10.5281/zenodo.24366897`) using John Tripodo's Lean bounds for $n = 4, 5$. General $g(n) \le 2n$ remains open. |
| [Erdős Problem #602: Property B without singleton intersections](erdos-602-property-b/) (Komjáth's question, `FormalConjectures/ErdosProblems/602.lean`) | Answered yes in full. Every family of countably infinite sets with finite pairwise intersections, none of size 1, has a 2-coloring with no monochromatic set (ZFC only). | No earlier proof of the unrestricted statement located in two limited searches (25 November 2026). Finite, countable, and several special families were known. |
| [Erdős Problem #1066, higher dimensions](erdos-1066-higher-dimensions/) (`g_d(n) >= cn/d`, `erdos_1066.variants.higher_dim`) | Variant refuted. For $A = 2^m$, $d = 6A^2$, $n = 4A^4$, at most $2A + 2$ of some $n$ points in $\mathbb{R}^d$ with minimum distance 1 are pairwise at distance $> 1$. | Follows quickly from de Caen's equiangular lines (2000); no one was found who had drawn this conclusion. The planar problem remains open. |
| [Erdős Problem #344, the $\sqrt{2N}$ variant](erdos-344-sqrt-two/) (Folkman 1966, `erdos_344.variants.sqrt_two`) | Variant proved. If $A$ has at least $\sqrt{2N}$ elements up to $N$ for all large $N$, its sums of distinct elements contain an infinite arithmetic progression. | No earlier proof located; close to Bergelson-Simmons (2017) and Fan (2026). The headline problem is due to Szemerédi and Vu. |
| [Erdős Problem #211, the constant 1/6](erdos-211-one-sixth/) (Beck's theorem, `erdos_211.variants.one_sixth`) | Variant refuted. Arbitrarily large sets of $n$ points with $O(n^{2/3})$ on any line determine at most $0.166\,n^2$ lines. | No earlier disproof located. Beck's theorem is unaffected, and nothing is proved for $k$ below about $0.996\,n$. |
| [Erdős Problem #387, Schinzel's conjecture for large $k$](erdos-387-schinzel/) (Colloq. Math. P 217, `erdos_387.variants.schinzel`) | Variant proved. For every large $k$ that is not a prime power, some $n$ has none of $n, \dots, n-k+1$ dividing $\binom{n}{k}$. | No earlier proof for all large $k$ located. The threshold is not explicit. The headline problem was answered by Bui, Naprienko, Pratt, and Zaharescu. |
| [Erdős Problem #338, restricted order bounded by the order](erdos-338-restricted-order/) (Erdős-Graham 1980 question 3(ii), `erdos_338.variants.bounded_by_order`) | Variant proved. If a basis of order $h$ has a restricted order, then it is at most $f(h)$, with $f$ explicit and independent of the basis. | No earlier bound depending only on $h$ located; follows the strategy of Chen, Yang, and Zhao (18 November 2026). The headline question is not addressed. |
| [Three-column binary matrices (`OEIS A401159`)](three-column-matrices/) ($n \times 3$ binary matrices with row/column sums $\le 2$, R. J. Mathar) | Exact formula $H^3 - n^4 + \binom{n}{2}$ where $H = 1 + n + \binom{n}{2}$ for all $n \ge 0$, matching Mathar's degree-6 polynomial. | Confirms Mathar's OEIS A401159 conjecture; implied by Adler and Ross (2001). |
| [Binomial recurrence (`OEIS A026019`)](a026019-binomial-recurrence/) (`a(n) = C(3n, n) - C(3n, n-3)`, R. J. Mathar) | Proves Mathar's three-term polynomial recurrence for all $n \ge 2$ over $\mathbb{Z}$ (taking binomial coefficients with negative lower index to be 0). | No earlier explicit proof located, though Georg Fischer's first-order recurrence in jOEIS (6 Nov 2026) implies it; priority unverified. |
| [Nonlinear-to-linear recurrence (`OEIS A176755`)](a176755-linear-recurrence/) (`a(n+1) = sum a(p)a(n-p) - 2`, R. J. Mathar / Georg Fischer) | Proves Mathar's five-term linear polynomial recurrence for all $n \ge 4$ via formal power series over $\mathbb{Z}[[x]]$. | Covered by Georg Fischer's January 2020 general recurrence (OEIS A176604/A176755). Independently formalized in Lean 4. |

## Partial results, bounds, reductions, and obstructions on open problems

For every entry below, the unrestricted problem remains open. Each package documents its Lean theorems and any bounds that rely on a written proof or an external computation.

| Problem | Partial result proved here | Unrestricted problem status |
| --- | --- | --- |
| [Three-color prismatic T-tetromino ziggurats](three-color-t-boards/) (`(T, 3)`-prismatic $Z_9$, Qiyuan Ma `10.5281/zenodo.23631079`) | At least 45,083,592 labeled boards (3,756,966 orbits of 12), a standalone proof of $> 60$ (72 boards), and a global orbit-size-12 theorem for every valid board. | Ma proved existence with 60 boards; no earlier proof of $> 60$ or $\ge 45{,}083{,}592$ located. Exact total remains open. |
| [Erdős Problem #64, power-of-two cycles](erdos-64-power-of-two-cycles/) (`erdosproblems.com/64`) | C++ enumeration verifies the conjecture through 41 vertices. In a smallest counterexample (breaking ties by edge count), every packing of disjoint triangles misses at least two degree-three vertices. Lean proves the cycle lift used in the packing argument and the full conjecture for graphs forbidding an induced $P_{15}\sqcup K_1$. [Order bound](erdos-64-power-of-two-cycles/Order41.md) · [Packing proof](erdos-64-power-of-two-cycles/DegreeComponents.md#contracting-disjoint-triangles) | The unrestricted conjecture remains open. Ducoffe and Dumitru verified all orders through 40 (`arXiv:2609.28594`). |
| [Erdős Problem #677: equal LCMs of consecutive integers](erdos-677-equal-lcms/) (`M(m, k) = M(n, k)`, `FormalConjectures/ErdosProblems/677.lean`) | Lengths $k = 2, 3, 4$ classified in Lean (unique collisions $(2, 3)$ and $(1, 2)$, both overlapping); length $k = 6$ settled computer-assisted (only $(3, 4), (5, 6), (13, 15)$); shift and endpoint bounds. | Earlier notes recorded $k = 3, 4$ and the four-cubic reduction at $k = 6$; no earlier Lean proofs of $k = 3, 4$ located. General $k$ remains open. |
| [Erdős Problem #617: missing colors in cliques](erdos-617-missing-colors/) (Erdős-Gyárfás on $K_{r^2+1}$, `FormalConjectures/ErdosProblems/617.lean`) | Proved for all $3 \le r \le 10$, for all $r \ge 3$ when one color has $r - 2$ disjoint $K_r$'s (or bounded degree excess), plus rank-window obstructions for counterexamples. | Erdős and Gyárfás proved $r = 3, 4$; a separate formalization covers $r = 5$. Cases $r \ge 11$ remain open. |
| [Erdős Problem #556: three-color nine-cycle Ramsey number `R_3(C_9)`](erdos-556-cycle-ramsey/) (`erdosproblems.com/556`) | Verifies $K_{32}$ lower-bound coloring; proves any 3-coloring of $K_{33}$ with a 15-vertex set missing one color has a monochromatic $C_9$; reduces $K_{33}$ to two cases. | Lower bound 33 is known. Upper bound $R_3(C_9) \le 33$ remains open. |
| [Erdős Problem #835: 17-color rainbow colorings at `k = 16`](erdos-835-coloring-subsets/) (32 points, $S(15, 16, 32)$, `FormalConjectures/ErdosProblems/835.lean`) | Excludes every regular abelian symmetry group of order 32, every involution fixing $\ge 4$ points (must move $\ge 30$), orders 11 and 13, and structured order-17 cases. | Earlier work excludes prime orders 19, 23, 29, 31 and two Steiner groups. Unrestricted existence remains open. |
| [Written on the Wall II, Graph Conjecture 133](written-on-the-wall-133/) (floored form `p >= r + floor(l(G))`, `FormalConjectures`) | Floored inequality holds for all orders $\le 29$, all $\lfloor l(G) \rfloor \le 4$, and all connected bipartite, regular, or diameter $\le 2$ graphs. | Haoyu Chen previously treated floors $\le 2$. Unrestricted floored (and updated unfloored) conjecture remains open. |
| [Arctangent-sum conjecture (`arXiv:2607.05739`)](arctangent-sum/) ($\tan(\sum_{k=1}^n \arctan k)$, Amdeberhan-Medina-Moll, Ken Ono) | Sparsity bound $O((\log N)^{3/4})$ (improving Ono's $O(\log N)$); any counterexample $n \ge 5$ has $n > 10^6$ and $|x_n| > n^{10} > 10^{60}$; infinite residue exclusions. | Excluding all $n \ge 5$ remains open. |
| [Integer cubic `z^2 + y^2 z + x^3 = 2`](integer-cubic/) (Grechuk Table 6 `arXiv:2404.08518`, Epoch FrontierMath) | Nonconstant rational polynomial family through an integer solution needs $\deg x \ge 6$; infinite family with integral $x, z$ and $y$ denominator 13; Pell amplification and quintic obstruction; 3 integer solutions with $|x| > 30{,}000{,}000$. | Infinitude of integer solutions (and Epoch's $|x| > 10^{50}$ challenge) remains open. |
| [Sum of three cubes `x^3 + y^3 + z^3 = 114`](three-cubes-114/) (Booker-Sutherland `arXiv:2007.01209`, Grantham-Walsh `arXiv:2211.12149`) | Arbitrarily large moduli admit a cube root of 114 while lying outside the full $\mathbb{Z}[\sqrt[3]{114}]$ norm family; Lean-verified modular sieves and bounded negative searches. | Existence of an integer solution summing to 114 remains open. |
| [Two triples producing nine squares (Dujella Problem 1.4)](square-triples/) (bipartite Diophantine triples $K_{3,3}$, $uv + 1 = \square$, `arXiv:2410.20120`) | In any solution, at least one triple has largest entry $> 1{,}000$ times its smallest entry (determinant bound plus kernel-checked exhaustion). | Existence of six distinct positive integers remains open. |
| [Book Ramsey number `R(B_63, B_64)`](book-ramsey/) ($253 \le R(B_{63}, B_{64}) \le 255$, Chung-Wesley `arXiv:2610.36522`, Dai-Lin `arXiv:2606.07214`) | Certifies 252-vertex graph ($R \ge 253$) and proves upper bound $R \le 255$; excludes 254-vertex identical-circulant graphs (and via McKay-Praeger, all vertex-transitive graphs of order 254). | Existence of a 254-vertex graph avoiding red $B_{63}$ and blue $B_{64}$ remains open. |
| [Classical Ramsey number `R(3, 10)`](ramsey-3-10/) ($40 \le R(3, 10) \le 41$, Exoo 1989, Angeltveit 2025) | Verifies two non-isomorphic 39-vertex witnesses (Exoo's 167-edge graph and a 172-edge graph, $R(3, 10) \ge 40$) and $C_{35}(\{1,7,11,16\})$ ($R(3, 9) \ge 36$); proves the weighted-Mantel / 9-regular dichotomy for $R(3, 10, 40)$, no 1-vertex extension of Exoo's graph, order-40 circulant and two-20-cycle exclusions, and SAT equivalence; C++23 exhaustive checks exclude all order-40 Cayley and order-20 bi-Cayley graphs. | Exact choice between 40 and 41 remains open. |
| [No-three-in-line problem on the 75 x 75 grid](no-three-in-line-75/) ($n = 75$, 148 vs. 150, Prellberg, Flammenkamp) | Verifies $148 \le \max \le 150$; proves Prellberg's 148-point set cannot be extended, every 150-point solution omits two of its points separated by $\ge 32$ rows, no 90°-symmetric 150-set exists, and polynomial curves mod 75 give $\le 50$ points. | Whether 149 or 150 points fit on the $75 \times 75$ grid remains open. |
| [42 consecutive-size squares (Erich Friedman Open Problem 10, `n = 21`)](consecutive-squares-21/) (two squares each of sizes 1..21, area 6,622) | The only possible tiled rectangle is $77 \times 86$ (up to rotation), excluding both $22 \times 301$ and $43 \times 154$. | Whether 42 squares tile $77 \times 86$ remains open (no earlier proof excluding $43 \times 154$ located). |
| [Nine-bit snake-in-the-box (`Q_9`, length 191 / 192)](nine-bit-snake/) (131 published snakes, Orland et al. `arXiv:2607.15270`, `arXiv:2611.25268`) | Keeping the first 156 steps of any published 191-step snake (from either end) yields no 192-step snake and no new 191-step class; gives a 17-step endpoint novelty criterion. | Existence of a 192-step snake or 132nd 191-step class in $Q_9$ remains open. |
| [Five 30-sided Go First Dice (`5 d30`, labels 1-150)](five-30-sided-dice/) (120 equal-probability permutations, `arXiv:2610.15421`) | Every die must have a face where two opponents' higher-label counts differ modulo 4; excludes 15 mirrored permutation blocks; verifies Paul Meyer's 60-sided dice (`5 d60`). | Existence of five 30-sided Go First Dice remains open (column-grouped family was already excluded earlier). |
| [Triple covering design `C(61, 25, 3)`](covering-61-25-3/) (26 vs. 27 blocks of size 25, Caleb Ashton) | Any 26-block cover can retain at most 20 of the 27 published blocks (all 296,010 choices of 21 blocks excluded in Lean); checks an 84-missing-triple candidate. | Whether $C(61, 25, 3) = 26$ or $27$ remains open. |
| [Equation 17260](E17260-partial-results/) (`x = (y ◇ x) ◇ (z ◇ (x ◇ (z ◇ z)))`, dual E28740) | Any magma with surjective squaring, an idempotent, a square 2-cycle, left/right cancellation, or an affine operation is trivial (`Subsingleton`), plus finite counting bounds. | Infinite models exist (`arXiv:2609.05690`); finite nontrivial existence remains open. |

## Find and check a theorem

Each folder has its own Lake configuration and pinned `lean-toolchain`:

* Lean 4.36.0 (stdlib only): `26-unit-fractions`, `book-ramsey`, `box-free-6x7`, `consecutive-squares-21`, `covering-61-25-3`, `E1486-order-15`, `E670-order-10`, `E677-E255-order-9`, `erdos-64-power-of-two-cycles`, `erdos-556-cycle-ramsey`, `five-30-sided-dice`, `manabe-residue-seven`, `nine-bit-snake`, `no-three-in-line-75`, `ramsey-3-10`, `seven-cycle`, `square-triples`, `three-color-t-boards`.
* Lean 4.36.0 + mathlib v4.36.0: `a026019-binomial-recurrence`, `a176755-linear-recurrence`, `arctangent-sum`, `E17260-partial-results`, `integer-cubic`, `three-column-matrices`, `three-cubes-114`.
* Lean 4.35.0 (stdlib only): `queen-domination-48`.
* Lean 4.35.0 + mathlib v4.35.0: `queen-domination-48-sat`.
* Lean 4.35.0-rc2 + mathlib: `erdos-617-missing-colors`, `erdos-677-equal-lcms`, `erdos-708-six` (with Tripodo's pinned development), `erdos-835-coloring-subsets`.
* Lean 4.33.1 + mathlib: `written-on-the-wall-133`, and, with the unmodified statements of Formal Conjectures, `erdos-211-one-sixth`, `erdos-338-restricted-order`, `erdos-344-sqrt-two`, `erdos-387-schinzel`, `erdos-602-property-b`, `erdos-1066-higher-dimensions`.

With `elan` installed, run the command in the corresponding directory. The `E670`, `E677`, and `E1486` SAT checks and large T-board certificates take noticeable time and memory; see their individual READMEs for details.

| Directory | Build command | Main Lean declaration(s) |
| --- | --- | --- |
| `square-triples` | `lake build` | `SquareTriples.solution_ratio_1000` |
| `box-free-6x7` | `lake build` | `BoxFree.exists_boxFree_iff` |
| `queen-domination-48` | `lake exe queens48` | `main` runs the exhaustive exclusion of 24 and verifies the 25-queen cover |
| `queen-domination-48-sat` | `lake exe cache get && lake build` | `QueenDom.gamma_48_eq_25_of_formulas_unsat`, `QueenDom.igamma_48_eq_25_of_formulas_unsat` |
| `nine-bit-snake` | `lake build` | `Snake.bank_no_192`, `Snake.bank_no_new_191`, `Snake.outside_bank_of_end_profiles` |
| `consecutive-squares-21` | `lake build` | `Squares42.exists_tiling_iff_77_by_86` |
| `five-30-sided-dice` | `lake build` | `FiveDice.EqualCuts.needs_distinct_residues`, `FiveDice.Mirrored.no_fifteen_mirrored` |
| `covering-61-25-3` | `lake build` | `Covering61.RepairSearch.published_six_for_five_screen` |
| `E677-E255-order-9` | `lake build` (with `E670-order-10` beside it) | `Nine.eq677_implies_eq255`, `Ten.no_model` |
| `E670-order-10` | `lake build` | `E670.no_model_of_order_ten` |
| `E1486-order-15` (order 15) | `lake build +Simple.NoTable` | `E1486.Simple.noTable` |
| `E1486-order-15` (order 12) | `lake build Simple.Order12.NoTable` | `E1486.Order12.noTable` |
| `E1486-order-15` (order 14) | `lake build Simple.Order14.NoTable` | `E1486.Order14.noTable` |
| `E1486-order-15` (order 17) | `lake build Simple.Order17` | `E1486.Order17.exists_table` |
| `E1486-order-15` (order 26) | `lake build Simple.Order26` | `E1486.Order26.exists_table` |
| `E17260-partial-results` | `lake exe cache get && lake build` | `Equation17260.subsingleton_of_surjective_square`, `affine_subsingleton` |
| `integer-cubic` | `lake exe cache get && lake build && lake exe boundedSearch` | `IntegerCubic.infinitely_many_with_two_integer_coordinates` |
| `integer-cubic` (Pell library) | `lake build SmallCubic` | `SmallCubic.MixedPell.infinite_of_nonconstant_quartic_chart`, `SmallCubic.QuinticSquareObstruction.no_negative_square_lift` |
| `three-cubes-114` | `lake exe cache get && lake build` | `ThreeCubes114.TernaryNorm.unbounded_normalized_moduli` |
| `26-unit-fractions` | `lake build` | `UnitFractions.forces_iff` |
| `erdos-64-power-of-two-cycles` | `lake build` ([order-41 replay](erdos-64-power-of-two-cycles/Order41.md#reproduction)) | `Erdos64.cycle_of_P15_plus_isolate_free`, `Erdos64.TrianglePacking.liftCycle` |
| `erdos-556-cycle-ramsey` | `lake build` | `Ramsey556.monoC9_of_independent15`, `Ramsey556.k33_iff_final_two_cases` |
| `erdos-617-missing-colors` | `lake exe cache get && lake build` | `Erdos617.missing_of_at_most_ten_colors`, `Erdos617.missing_of_all_but_two_parallel_rows` |
| `erdos-677-equal-lcms` | `lake exe cache get && lake build` ([length-6 arithmetic](erdos-677-equal-lcms/cubic/LengthSix.md#reproduction)) | `Erdos677.three_collision_iff`, `Erdos677.four_collision_iff`, `Erdos677.six_collision_iff_three_of_affine_cover` |
| `erdos-708-six` | `lake exe cache get && lake build` | `Erdos708.isLeast_six`, `IntervalSix.six_integer` |
| `erdos-211-one-sixth` | `lake exe cache get && lake build` | `main : ¬ type_of% @Erdos211.erdos_211.variants.one_sixth` |
| `erdos-338-restricted-order` | `lake exe cache get && lake build` | `main : type_of% @Erdos338.erdos_338.variants.bounded_by_order` |
| `erdos-344-sqrt-two` | `lake exe cache get && lake build` | `main : type_of% @Erdos344.erdos_344.variants.sqrt_two` |
| `erdos-387-schinzel` | `lake exe cache get && lake build` | `main : type_of% @Erdos387.erdos_387.variants.schinzel` |
| `erdos-602-property-b` | `lake exe cache get && lake build` | `main : type_of% @Erdos602.erdos_602` |
| `erdos-1066-higher-dimensions` | `lake exe cache get && lake build` | `main : ¬ type_of% @Erdos1066.erdos_1066.variants.higher_dim`, `Sol1066.gDim_upper` |
| `erdos-835-coloring-subsets` | `lake exe cache get && lake build` | `Erdos835.involution_moves_at_least_thirty`, `Erdos835.no_regular_abelian_symmetry` |
| `written-on-the-wall-133` | `lake exe cache get && lake build` | `Wall133.floored_of_order_le_29`, `Wall133.floored_of_floor_le_four` |
| `seven-cycle` | `lake build` | `SevenCycle.exact_threshold` |
| `book-ramsey` | `lake build` | `BookRamsey.Lower252.exists_252`, `BookRamsey.Upper255.upper` |
| `ramsey-3-10` | `lake build` | `Ramsey310.ramsey_lower_bound`, `Ramsey310.Structural.r310_40_dichotomy`, `Ramsey310.Dense39.dense39_witness`, `Ramsey310.exoo_no_one_vertex_extension` |
| `no-three-in-line-75` | `lake build` | `Grid75.maximum_in_range`, `Grid75.omitted_rows_separated` |
| `three-color-t-boards` (45M bound) | `lake build SplicePalCertificates` | `TBoards.at_least_45083592` |
| `three-color-t-boards` (small proof) | `lake build SimpleProof` | `TBoards.Simple.problem_solved` |
| `three-color-t-boards` (orbit size 12) | `lake build ExactSymmetry ExactOrbit` | `TBoards.ExactSymmetry.stabilizer_trivial`, `TBoards.ExactOrbit.twelve_distinct_images` |
| `three-column-matrices` | `lake exe cache get && lake build` | `ThreeColumnMatrices.card_validMatrices` |
| `manabe-residue-seven` | `lake build` | `SubtractionGame.grundy_eq_three_iff` |
| `a026019-binomial-recurrence` | `lake exe cache get && lake build` | `A026019.recurrence` |
| `a176755-linear-recurrence` | `lake exe cache get && lake build` | `A176755.mathar` |
| `arctangent-sum` | `lake exe cache get && lake build` | `Arxiv.«2607.05739».positive_integer_count_isBigO`, `counterexample_constraints` |

The `E670`, `E677`, and `E1486` exclusions use Lean's native LRAT checker; see the trust and reproduction notes for [E670](E670-order-10/README.md#reproduce), [E677](E677-E255-order-9/README.md#verify), and [E1486](E1486-order-15/README.md#reproduce). Each folder notes whether its results are kernel-checked proofs, `native_decide` or LRAT checks, compiled exhaustive searches, external arithmetic, or bounded exploratory searches.

## Supporting tools and attribution

[lake-compat](https://github.com/Cameron-Lyons/lake-compat) is a separate repository for checking Lean dependency upgrades. Its local checkout may sit beside these folders; it is not a mathematical result.

Problem references, known proofs, and literature-search notes are in [PRIOR_ART.md](PRIOR_ART.md). The T-board folder's [source attribution](three-color-t-boards/README.md#source-and-attribution) preserves Qiyuan Ma's licenses and credits. See [License](#license) for the collection's MIT license and components with separate notices.

For each added result, record its assumptions, named proof endpoint, reproduction command, source problem identifier, and dated prior-art search. Check general theorems and equivalent terminology as well as the exact title, since conjecture labels in catalogues can be out of date.

## License

Original collection material is licensed under the [MIT License](LICENSE), except material carrying separate license or attribution notices:

* [Written on the Wall II #133](written-on-the-wall-133/LICENSE) retains its Apache-2.0 license, including attribution in the [adapted radius bound](written-on-the-wall-133/Wall133/Chung.lean).
* [E1486-order-15](E1486-order-15/LICENSE) retains its Apache-2.0 license and the copyright notice of the Equational Theories Project contributors.
* [queen-domination-48-sat](queen-domination-48-sat/LICENSE) retains the Apache-2.0 license of Jason Davies' [queen-domination](https://github.com/jasondavies/queen-domination), whose files it uses, adapts, and transcribes; see its [source notes](queen-domination-48-sat/README.md#source-and-license).
* The Formal Conjectures interval definition in [UpstreamInterval.lean](erdos-677-equal-lcms/UpstreamInterval.lean) retains its [Apache-2.0 license](erdos-677-equal-lcms/LICENSE-FormalConjectures) and copyright notice.
* The four definitions from Formal Conjectures in [ArctanBridge.lean](arctangent-sum/ArctanBridge.lean) retain their Apache-2.0 license and copyright notice.
* The Formal Conjectures statements quoted in the comments of [#211](erdos-211-one-sixth/Erdos211.lean), [#338](erdos-338-restricted-order/Erdos338.lean), [#344](erdos-344-sqrt-two/Erdos344.lean), [#387](erdos-387-schinzel/Erdos387.lean), and [#1066](erdos-1066-higher-dimensions/Erdos1066.lean) are under that project's [Apache-2.0 license](https://github.com/google-deepmind/formal-conjectures/blob/main/LICENSE).
* Qiyuan Ma's manuscript, certificate data, documentation, and recorded outputs in [three-color-t-boards/sources](three-color-t-boards/sources/LICENSE_SCOPE.txt) retain CC-BY-4.0. The supplied Python programs retain their MIT license and original copyright notice.
* Code from [msolve](https://github.com/algebraic-solving/msolve) v0.11.0 (Jérémy Berthomieu, Christian Eder, and Mohab Safey El Din) in [three-color-t-boards/experiments](three-color-t-boards/experiments) remains under [GPL-2.0-or-later](three-color-t-boards/experiments/LICENSE-msolve). This covers the copied sources in `exact_algebra_backend_msolve_source` and `exact_msolve_tools`, the msolve patches, the C check programs and scripts that contain msolve functions, and the excerpts of msolve code in recorded outputs. The patches and check programs were modified in November 2026.
* Ma's attribution also applies to the first five representatives and their symmetry images reused in the T-board data; see [source and attribution](three-color-t-boards/README.md#source-and-attribution).

The root MIT license does not replace these notices or relicense third-party material.
