# Formal Math Lab

A collection of Lean 4 proofs, finite-case solutions, obstructions, and computational checks in combinatorics, Ramsey theory, finite algebra (the Equational Theories Project), number theory, Erdős problems, OEIS conjectures, and discrete geometry.

Each folder is a standalone Lake package. Its README states the math problem, source references (arXiv, DOI, OEIS, Erdős problem, or ETP equation), Lean theorem names, build commands, and trust boundaries. Literature checks are logged in [PRIOR_ART.md](PRIOR_ART.md) (updated 25 November 2026). When a note says no earlier proof was found, that covers only the sources checked and does not claim absolute priority.

## Settled problems, exact values, and proved recurrences

Each folder below settles a finite open case, finds an exact value, or proves or refutes a conjecture or recurrence in Lean 4.

| Problem | Result proved here | Prior art and status |
| --- | --- | --- |
| [Box-free 2-colorings of the 6 x 7 x n grid](box-free-6x7/) (Genkin Question 8.1, `10.5281/zenodo.24457907`) | Maximum height is $n = 52$. Lean's kernel checks a 52-layer box-free coloring and proves $n \le 52$. | Genkin built 50 layers, proved $n \le 52$, and asked whether 52 is reachable (Question 8.1). |
| [Queen domination on the 48 x 48 chessboard](queen-domination-48/) ($\gamma(Q_{48}) = 25$, Davies §9, `hexagonmath.org/pdf/2611.00830v1`) | $\gamma(Q_{48}) = 25$ queens. Compiled Lean search rules out 24 queens and checks a 25-queen cover of all 2,304 squares. | Östergård and Weakley gave the 25-queen upper bound. Davies listed $48 \times 48$ as the next open even board on 21 November 2026. |
| [Queen domination on the 48 x 48 board by SAT certificates](queen-domination-48-sat/) ($\gamma(Q_{48}) = i(Q_{48}) = 25$, Jason Davies frame method) | $\gamma(Q_{48}) = i(Q_{48}) = 25$ (independent second proof, plus independent domination). Lean's kernel proves the reduction and encoding into 47,580 CNF formulas and checks a 25-queen independent dominating set; a compiled Lean checker verifies the LRAT proofs outside the kernel. | Östergård and Weakley bounded both numbers to $\{24, 25\}$. Uses Jason Davies' frame method and encoder. No earlier value for $i(Q_{48})$ was found in a brief search. |
| [Equation 1486 finite magma spectrum](E1486-order-15/) (`x = (y ◇ x) ◇ (x ◇ (z ◇ z))`, orders 12, 14, 15, 17, 26; dual E2126) | No magma of order 12, 14, or 15; explicit models of orders 17 and 26. Settles all five open orders in the ETP spectrum catalogue (with the fork's bounds, ruled-out orders are `2, 3, 5, 6, 7, 8, 10, 12, 14, 15`). | No earlier proof or model found for these five orders in sources checked 22-24 November 2026. |
| [Equation 670 at order 10](E670-order-10/) (`x = y ◇ (x ◇ ((x ◇ y) ◇ y))`, dual E2937) | No 10-element magma satisfies E670 (SAT/LRAT refutation checked in Lean). Also checks affine models at orders `19, 29, 31, 41, 59, 61`. | No earlier proof at order 10 found; 10 was the smallest open order in the ETP spectrum catalogue checked on 23 November 2026. |
| [Equation 677 at orders 9 and 10, and E677 -> E255](E677-E255-order-9/) (`x = y ◇ (x ◇ ((y ◇ x) ◇ y))`, `x = ((x ◇ x) ◇ x) ◇ x`) | Order 9: every 9-element E677 magma satisfies E255. Order 10: no 10-element E677 magma exists. | Formalizes José Brox's Mace4 reports (Dec 2024, Jan 2025). No earlier Lean proof at order 10 found. General finite `E677 -> E255` is still open. |
| [Reciprocal Rado number `f_2(26) = 2028`](26-unit-fractions/) (`1/x_1 + ... + 1/x_26 = 1/y`, Gaiser-Ramezanpour Conjecture 1.3, `arXiv:2607.04373`) | $f_2(26) = 2028 = 3 \cdot 26^2$ (repeated denominators allowed), proved in pure Lean 4. | No earlier upper-bound proof at 26 terms found. Lower bound and initial identities come from Gaiser and Ramezanpour. General $f_2(k) = 3k^2$ is still open. |
| [Seven-cycle Ramsey threshold `R_3^2(C_7) = 11`](seven-cycle/) (at most 2 cyclic color changes, Allen et al. Problem 22, `arXiv:2607.03243`) | $R_3^2(C_7) = 11$. Every 3-edge-coloring of $K_{11}$ has a $C_7$ with $\le 2$ cyclic color changes; an explicit $K_{10}$ coloring avoids one. | No earlier proof found. Settles one finite case of Problem 22 from Allen, Böttcher, Clemens, Hamann, Skokan, and Taraz. |
| [Manabe's subtraction game `{3, 8, 11k + 7}`](manabe-residue-seven/) (`arXiv:2609.05358` Example 1) | For every $k \ge 1$, $n = 11k + 10$ is the only heap with Grundy value 3, giving least preperiod $11k + 11$ and eventual period $11k + 10$. | No earlier proof of the singleton-3 result for all $k \ge 1$ found. REUF working notes anticipate the repeating block. |
| [Erdős Problem #708 for six integers: `g(6) = 8`](erdos-708-six/) (`erdosproblems.com/708`) | $g(6) = 8$. For any 6-element set $A$, every block of $\max A$ consecutive integers has $\le 8$ distinct entries whose product is divisible by $\prod_{a \in A} a$, and 8 is sharp. | Formalizes C. Bergström's proof (`10.5281/zenodo.24366897`), importing John Tripodo's Lean bounds for $n = 4, 5$. General $g(n) \le 2n$ is still open. |
| [Erdős Problem #602: Property B without singleton intersections](erdos-602-property-b/) (Komjáth's question, `FormalConjectures/ErdosProblems/602.lean`) | Proved in full (ZFC only). Any family of countably infinite sets with finite pairwise intersections, none of size 1, has a 2-coloring with no monochromatic set. | No earlier unrestricted proof found in two limited searches (25 November 2026). Finite, countable, and several special cases were known. |
| [Erdős Problem #1066, higher dimensions](erdos-1066-higher-dimensions/) (`g_d(n) >= cn/d`, `erdos_1066.variants.higher_dim`) | Disproved. For $A = 2^m$, $d = 6A^2$, and $n = 4A^4$, there are $n$ points in $\mathbb{R}^d$ with minimum distance 1 where at most $2A + 2$ points have all pairwise distances $> 1$. | Short corollary of de Caen's equiangular lines (2000); no earlier statement of this corollary was found. The planar problem is still open. |
| [Erdős Problem #344, the $\sqrt{2N}$ variant](erdos-344-sqrt-two/) (Folkman 1966, `erdos_344.variants.sqrt_two`) | Proved. If $A$ has at least $\sqrt{2N}$ elements up to $N$ for all large $N$, its sums of distinct elements contain an infinite arithmetic progression. | No earlier proof found; close to Bergelson and Simmons (2017) and Fan (2026). Szemerédi and Vu proved the headline problem. |
| [Erdős Problem #211, the constant 1/6](erdos-211-one-sixth/) (Beck's theorem, `erdos_211.variants.one_sixth`) | Disproved. Arbitrarily large sets of $n$ points with $O(n^{2/3})$ points per line span at most $0.166\,n^2$ lines. | No earlier disproof found. Beck's theorem still holds, and nothing is proved for $k$ below about $0.996\,n$. |
| [Erdős Problem #387, Schinzel's conjecture for large $k$](erdos-387-schinzel/) (Colloq. Math. P 217, `erdos_387.variants.schinzel`) | Proved. For every large non-prime-power $k$, some $n$ has none of $n, \dots, n-k+1$ dividing $\binom{n}{k}$. | No earlier proof for all large $k$ found (threshold is not explicit). Bui, Naprienko, Pratt, and Zaharescu settled the headline problem. |
| [Erdős Problem #338, restricted order bounded by the order](erdos-338-restricted-order/) (Erdős-Graham 1980 question 3(ii), `erdos_338.variants.bounded_by_order`) | Proved. If a basis of order $h$ has a restricted order, it is at most an explicit $f(h)$ that does not depend on the basis. | No earlier bound depending only on $h$ found. Follows Chen, Yang, and Zhao (18 November 2026). Does not address the headline question. |
| [Three-column binary matrices (`OEIS A401159`)](three-column-matrices/) ($n \times 3$ binary matrices with row/column sums $\le 2$, R. J. Mathar) | Exact count $H^3 - n^4 + \binom{n}{2}$ with $H = 1 + n + \binom{n}{2}$ for all $n \ge 0$, matching Mathar's degree-6 polynomial. | Proves Mathar's OEIS A401159 conjecture; implied by Adler and Ross (2001). |
| [Binomial recurrence (`OEIS A026019`)](a026019-binomial-recurrence/) (`a(n) = C(3n, n) - C(3n, n-3)`, R. J. Mathar) | Proves Mathar's three-term polynomial recurrence for all $n \ge 2$ over $\mathbb{Z}$ (with negative lower binomial index taken as 0). | No earlier explicit proof found, though Georg Fischer's first-order jOEIS recurrence (6 Nov 2026) implies it. Priority unverified. |
| [Nonlinear-to-linear recurrence (`OEIS A176755`)](a176755-linear-recurrence/) (`a(n+1) = sum a(p)a(n-p) - 2`, R. J. Mathar / Georg Fischer) | Proves Mathar's five-term linear polynomial recurrence for all $n \ge 4$ using formal power series over $\mathbb{Z}[[x]]$. | Covered by Georg Fischer's January 2020 general recurrence (OEIS A176604/A176755). Independently formalized in Lean 4. |

## Partial results, bounds, reductions, and obstructions on open problems

In every entry below, the full problem is still open. Each folder lists what Lean proves and which bounds use a written proof or external code.

| Problem | Partial result proved here | Unrestricted problem status |
| --- | --- | --- |
| [Three-color prismatic T-tetromino ziggurats](three-color-t-boards/) (`(T, 3)`-prismatic $Z_9$, Qiyuan Ma `10.5281/zenodo.23631079`) | At least 45,083,592 labeled boards (3,756,966 orbits of 12), a standalone proof of $> 60$ (72 boards), and a theorem that every valid board has orbit size 12. | Ma gave 60 boards; no earlier proof of $> 60$ or $\ge 45{,}083{,}592$ found. Exact total is still open. |
| [Erdős Problem #64, power-of-two cycles](erdos-64-power-of-two-cycles/) (`erdosproblems.com/64`) | C++ search checks all graphs through 41 vertices ([order bound](erdos-64-power-of-two-cycles/Order41.md)). In a smallest counterexample (breaking ties by edge count), every packing of disjoint triangles misses at least two degree-3 vertices ([packing proof](erdos-64-power-of-two-cycles/DegreeComponents.md#contracting-disjoint-triangles)). Lean proves the cycle lift and the full conjecture for graphs with no induced $P_{15}\sqcup K_1$. | Full conjecture is still open. Ducoffe and Dumitru checked through 40 vertices (`arXiv:2609.28594`). |
| [Erdős Problem #677: equal LCMs of consecutive integers](erdos-677-equal-lcms/) (`M(m, k) = M(n, k)`, `FormalConjectures/ErdosProblems/677.lean`) | Classifies $k = 2, 3, 4$ in Lean (only overlapping collisions $(2, 3)$ and $(1, 2)$); settles $k = 6$ with computer assistance (only $(3, 4), (5, 6), (13, 15)$); adds shift and endpoint bounds. | Earlier notes gave $k = 3, 4$ and reduced $k = 6$ to four cubics; no earlier Lean proofs of $k = 3, 4$ found. General $k$ is still open. |
| [Erdős Problem #617: missing colors in cliques](erdos-617-missing-colors/) (Erdős-Gyárfás on $K_{r^2+1}$, `FormalConjectures/ErdosProblems/617.lean`) | Proved for $3 \le r \le 10$, and for all $r \ge 3$ when one color has $r - 2$ disjoint $K_r$'s (or bounded degree excess), plus rank-window obstructions. | Erdős and Gyárfás proved $r = 3, 4$; another Lean project covers $r = 5$. Cases $r \ge 11$ are still open. |
| [Erdős Problem #556: three-color nine-cycle Ramsey number `R_3(C_9)`](erdos-556-cycle-ramsey/) (`erdosproblems.com/556`) | Checks the $K_{32}$ lower-bound coloring; proves any 3-coloring of $K_{33}$ with 15 vertices missing a color has a monochromatic $C_9$; reduces $K_{33}$ to two cases. | Lower bound 33 is known. Upper bound $R_3(C_9) \le 33$ is still open. |
| [Erdős Problem #835: 17-color rainbow colorings at `k = 16`](erdos-835-coloring-subsets/) (32 points, $S(15, 16, 32)$, `FormalConjectures/ErdosProblems/835.lean`) | Rules out all regular abelian symmetry groups of order 32, involutions fixing $\ge 4$ points (must move $\ge 30$), orders 11 and 13, and structured order-17 cases. | Earlier work rules out prime orders 19, 23, 29, 31 and two Steiner groups. General existence is still open. |
| [Written on the Wall II, Graph Conjecture 133](written-on-the-wall-133/) (floored form `p >= r + floor(l(G))`, `FormalConjectures`) | Proves the floored bound for all orders $\le 29$, all $\lfloor l(G) \rfloor \le 4$, and all connected bipartite, regular, or diameter $\le 2$ graphs. | Haoyu Chen previously handled floors $\le 2$. General floored and updated unfloored forms are still open. |
| [Arctangent-sum conjecture (`arXiv:2607.05739`)](arctangent-sum/) ($\tan(\sum_{k=1}^n \arctan k)$, Amdeberhan-Medina-Moll, Ken Ono) | Improves Ono's $O(\log N)$ sparsity bound to $O((\log N)^{3/4})$; any counterexample $n \ge 5$ has $n > 10^6$ and $\lvert x_n \rvert > n^{10} > 10^{60}$; rules out infinite residue classes. | Ruling out all $n \ge 5$ is still open. |
| [Integer cubic `z^2 + y^2 z + x^3 = 2`](integer-cubic/) (Grechuk Table 6 `arXiv:2404.08518`, Epoch FrontierMath) | Any nonconstant rational polynomial family through an integer point needs $\deg x \ge 6$; infinite family with integer $x, z$ and $y$ denominator 13; Pell amplification and quintic obstruction; 3 integer solutions with $\lvert x \rvert > 30{,}000{,}000$. | Whether infinitely many integer solutions exist (and Epoch's $\lvert x \rvert > 10^{50}$ challenge) is still open. |
| [Sum of three cubes `x^3 + y^3 + z^3 = 114`](three-cubes-114/) (Booker-Sutherland `arXiv:2007.01209`, Grantham-Walsh `arXiv:2211.12149`) | Arbitrarily large moduli have a cube root of 114 while falling outside the $\mathbb{Z}[\sqrt[3]{114}]$ norm family; Lean-checked modular sieves and bounded negative searches. | Existence of an integer solution for 114 is still open. |
| [Two triples producing nine squares (Dujella Problem 1.4)](square-triples/) (bipartite Diophantine triples $K_{3,3}$, $uv + 1 = \square$, `arXiv:2410.20120`) | In any solution, one triple must have max/min ratio $> 1{,}000$ (determinant bound plus kernel-checked exhaustion). | Whether six distinct positive integers exist is still open. |
| [Book Ramsey number `R(B_63, B_64)`](book-ramsey/) ($253 \le R(B_{63}, B_{64}) \le 255$, Chung-Wesley `arXiv:2610.36522`, Dai-Lin `arXiv:2606.07214`) | Checks a 252-vertex witness ($R \ge 253$) and proves $R \le 255$; rules out 254-vertex identical-circulant graphs (and, with McKay-Praeger, all vertex-transitive order-254 graphs). | Existence of a 254-vertex graph avoiding red $B_{63}$ and blue $B_{64}$ is still open. |
| [Classical Ramsey number `R(3, 10)`](ramsey-3-10/) ($40 \le R(3, 10) \le 41$, Exoo 1989, Angeltveit 2025) | Checks two non-isomorphic 39-vertex witnesses (Exoo's 167-edge graph and a 172-edge graph, $R(3, 10) \ge 40$) and $C_{35}(\{1,7,11,16\})$ ($R(3, 9) \ge 36$). Proves the weighted-Mantel / 9-regular dichotomy for $R(3, 10, 40)$, no 1-vertex extension of Exoo's graph, order-40 circulant and two-20-cycle obstructions, and SAT equivalence. Standalone C++23 checks rule out all order-40 Cayley and order-20 bi-Cayley graphs. | Whether $R(3, 10)$ is 40 or 41 is still open. |
| [No-three-in-line problem on the 75 x 75 grid](no-three-in-line-75/) ($n = 75$, 148 vs. 150, Prellberg, Flammenkamp) | Checks $148 \le \max \le 150$. Proves Prellberg's 148-point set cannot be extended, any 150-point set drops two of its points at least 32 rows apart, no 90°-symmetric 150-set exists, and polynomial curves mod 75 give $\le 50$ points. | Whether 149 or 150 points fit on the $75 \times 75$ grid is still open. |
| [42 consecutive-size squares (Erich Friedman Open Problem 10, `n = 21`)](consecutive-squares-21/) (two squares each of sizes 1-21, area 6,622) | Only $77 \times 86$ can work (up to rotation); rules out $22 \times 301$ and $43 \times 154$. | Whether the 42 squares tile $77 \times 86$ is still open (no earlier proof ruling out $43 \times 154$ found). |
| [Nine-bit snake-in-the-box (`Q_9`, length 191 / 192)](nine-bit-snake/) (131 published snakes, Orland et al. `arXiv:2607.15270`, `arXiv:2611.25268`) | Keeping the first 156 steps of any published 191-step snake (from either end) gives no 192-step snake and no new 191-step class; adds a 17-step endpoint novelty test. | Whether a 192-step snake or a 132nd 191-step class exists in $Q_9$ is still open. |
| [Five 30-sided Go First Dice (`5 d30`, labels 1-150)](five-30-sided-dice/) (120 equal-probability permutations, `arXiv:2610.15421`) | Every die needs a face where two opponents' higher-label counts differ mod 4; rules out 15 mirrored permutation blocks; checks Paul Meyer's 60-sided dice (`5 d60`). | Whether five 30-sided Go First Dice exist is still open (column-grouped labelings were already ruled out). |
| [Triple covering design `C(61, 25, 3)`](covering-61-25-3/) (26 vs. 27 blocks of size 25, Caleb Ashton) | Any 26-block cover can keep at most 20 of the 27 published blocks (Lean rules out all 296,010 choices of 21); checks an 84-missing-triple candidate. | Whether $C(61, 25, 3)$ is 26 or 27 is still open. |
| [Equation 17260](E17260-partial-results/) (`x = (y ◇ x) ◇ (z ◇ (x ◇ (z ◇ z)))`, dual E28740) | Any model with surjective squaring, an idempotent, a square 2-cycle, left or right cancellation, or an affine operation has at most one element (`Subsingleton`), plus finite counting bounds. | Infinite models exist (`arXiv:2609.05690`); existence of a finite nontrivial model is still open. |

## Find and check a theorem

Each folder has its own Lake setup and pinned `lean-toolchain`:

* Lean 4.36.0 (stdlib only): `26-unit-fractions`, `book-ramsey`, `box-free-6x7`, `consecutive-squares-21`, `covering-61-25-3`, `E1486-order-15`, `E670-order-10`, `E677-E255-order-9`, `erdos-64-power-of-two-cycles`, `erdos-556-cycle-ramsey`, `five-30-sided-dice`, `manabe-residue-seven`, `nine-bit-snake`, `no-three-in-line-75`, `queen-domination-48`, `ramsey-3-10`, `seven-cycle`, `square-triples`, `three-color-t-boards`.
* Lean 4.36.0 + mathlib v4.36.0: `a026019-binomial-recurrence`, `a176755-linear-recurrence`, `arctangent-sum`, `E17260-partial-results`, `erdos-617-missing-colors`, `erdos-677-equal-lcms`, `erdos-708-six` (with Tripodo's pinned development), `erdos-835-coloring-subsets`, `integer-cubic`, `queen-domination-48-sat`, `three-column-matrices`, `three-cubes-114`, `written-on-the-wall-133`.
* Lean 4.33.1 + mathlib (with the unmodified statements of Formal Conjectures): `erdos-211-one-sixth`, `erdos-338-restricted-order`, `erdos-344-sqrt-two`, `erdos-387-schinzel`, `erdos-602-property-b`, `erdos-1066-higher-dimensions`.

With `elan` installed, run the command below inside that folder. The `E670`, `E677`, and `E1486` SAT checks and the large T-board certificates take noticeable time and memory; see their folder READMEs for details.

| Directory | Build command | Main Lean declaration(s) |
| --- | --- | --- |
| `square-triples` | `lake build` | `SquareTriples.solution_ratio_1000` |
| `box-free-6x7` | `lake build` | `BoxFree.exists_boxFree_iff` |
| `queen-domination-48` | `lake exe queens48` | `main` runs the exhaustive search ruling out 24 and checks the 25-queen cover |
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

The `E670`, `E677`, and `E1486` proofs use Lean's native LRAT checker. See the trust and reproduction notes for [E670](E670-order-10/README.md#reproduce), [E677](E677-E255-order-9/README.md#verify), and [E1486](E1486-order-15/README.md#reproduce). Every folder states whether its results rely on kernel-checked proofs, `native_decide` or LRAT checks, compiled exhaustive searches, external arithmetic, or bounded exploratory searches.

## Supporting tools and attribution

[lake-compat](https://github.com/Cameron-Lyons/lake-compat) is a separate repository for checking Lean dependency upgrades. A local checkout may sit beside these folders, though it is not a mathematical result.

Problem references, known proofs, and literature-search notes live in [PRIOR_ART.md](PRIOR_ART.md). The T-board folder's [source attribution](three-color-t-boards/README.md#source-and-attribution) keeps Qiyuan Ma's licenses and credits. See [License](#license) for the collection's MIT license and third-party notices.

When adding a result, record its assumptions, named proof endpoint, reproduction command, source problem identifier, and dated prior-art check. Search for general theorems and alternate phrasing as well as the exact title, since conjecture labels in catalogues can fall out of date.

## License

Original collection material uses the [MIT License](LICENSE), except where separate license or attribution notices apply:

* [Written on the Wall II #133](written-on-the-wall-133/LICENSE) keeps its Apache-2.0 license, including attribution in the [adapted radius bound](written-on-the-wall-133/Wall133/Chung.lean).
* [E1486-order-15](E1486-order-15/LICENSE) keeps its Apache-2.0 license and the copyright notice of the Equational Theories Project contributors.
* [queen-domination-48-sat](queen-domination-48-sat/LICENSE) keeps the Apache-2.0 license of Jason Davies' [queen-domination](https://github.com/jasondavies/queen-domination), whose files it uses, adapts, and transcribes; see its [source notes](queen-domination-48-sat/README.md#source-and-license).
* The Formal Conjectures interval definition in [UpstreamInterval.lean](erdos-677-equal-lcms/UpstreamInterval.lean) keeps its [Apache-2.0 license](erdos-677-equal-lcms/LICENSE-FormalConjectures) and copyright notice.
* The four definitions from Formal Conjectures in [ArctanBridge.lean](arctangent-sum/ArctanBridge.lean) keep their Apache-2.0 license and copyright notice.
* The Formal Conjectures statements quoted in the comments of [#211](erdos-211-one-sixth/Erdos211.lean), [#338](erdos-338-restricted-order/Erdos338.lean), [#344](erdos-344-sqrt-two/Erdos344.lean), [#387](erdos-387-schinzel/Erdos387.lean), and [#1066](erdos-1066-higher-dimensions/Erdos1066.lean) remain under that project's [Apache-2.0 license](https://github.com/google-deepmind/formal-conjectures/blob/main/LICENSE).
* Qiyuan Ma's manuscript, certificate data, documentation, and recorded outputs in [three-color-t-boards/sources](three-color-t-boards/sources/LICENSE_SCOPE.txt) keep CC-BY-4.0. The included Python programs keep their MIT license and original copyright notice.
* Code from [msolve](https://github.com/algebraic-solving/msolve) v0.11.0 (Jérémy Berthomieu, Christian Eder, and Mohab Safey El Din) in [three-color-t-boards/experiments](three-color-t-boards/experiments) stays under [GPL-2.0-or-later](three-color-t-boards/experiments/LICENSE-msolve). This covers the copied sources in `exact_algebra_backend_msolve_source` and `exact_msolve_tools`, the msolve patches, the C check programs and scripts that contain msolve functions, and the excerpts of msolve code in recorded outputs. The patches and check programs were modified in November 2026.
* Ma's attribution also applies to the first five representatives and their symmetry images reused in the T-board data; see [source and attribution](three-color-t-boards/README.md#source-and-attribution).

The root MIT license does not replace these notices or relicense third-party material.
