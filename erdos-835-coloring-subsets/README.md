# Erdős Problem #835 (Erdos #835) at k = 16: Symmetry obstructions for 17-color rainbow colorings — Lean 4 proofs

**Status: existence of a rainbow coloring at $k = 16$ (and for general $k$) remains open.** At $k = 16$, **Erdős Problem #835** asks whether the 16-subsets of a 32-point set can be colored with 17 colors so that every 17-subset contains all 17 colors (equivalently, partitioning $\binom{[32]}{16}$ into 17 Steiner systems $S(15, 16, 32)$). A point permutation is a symmetry if it maps color classes to color classes (possibly permuting the 17 colors).

This Lean 4 project excludes every regular abelian symmetry group of order 32, every involution with at least 4 fixed points (any involution must move at least 30 of the 32 points), every point symmetry of order 11 or 13 (for both rainbow colorings and single Steiner systems $S(15, 16, 32)$), and several structured cases of order-17 symmetry.

| Field | Summary |
| --- | --- |
| **Problem & identifiers** | **Erdős Problem #835** (`Erdos #835`, `erdosproblems.com/835`) at $k = 16$ ($2k = 32$ points, $k + 1 = 17$ colors, Steiner system $S(15, 16, 32)$), `FormalConjectures/ErdosProblems/835.lean` |
| **Status** | **Partial results (symmetry obstructions).** Existence of a coloring at $k = 16$ and the general question remain open. |
| **Main Lean theorems** | `Erdos835.no_regular_abelian_symmetry`, `involution_moves_at_least_thirty`, `no_order11_or_13`, `IsSteinerSystem.no_order11_or_13`, `TwentyPoint.order17_requires_concrete_seed` |
| **Verification** | `lake exe cache get && lake build` (Lean 4.35.0-rc2 + mathlib; core symmetry theorems are kernel-checked, two order-17 SAT/LRAT sub-results use `native_decide`) |
| **Prior-art status** | Checked **23 November 2026**: earlier work excludes prime orders 19, 23, 29, 31 and two groups on a single Steiner system, and Kolotoğlu–Magliveras (2014) implies order 11 and single 13-cycle cases. See [Relation to earlier work](#relation-to-earlier-work) and [PRIOR_ART.md](../PRIOR_ART.md#erdős-835-coloring-subsets). |

## Main symmetry exclusions in Lean

| Symmetry excluded | Object | Lean theorem (namespace `Erdos835`) |
| --- | --- | --- |
| Every regular abelian group of order 32 (including cyclic shifts $\mathbb{Z}/32\mathbb{Z}$ and translations of $\mathbb{F}_2^5$) | Rainbow coloring | [`no_regular_abelian_symmetry`](Abelian.lean) |
| Every point involution (order 2) with at least 4 fixed points (i.e., moving $\le 28$ points) | Rainbow coloring | [`involution_moves_at_least_thirty`](Involution.lean) |
| Every point permutation of order 11 or 13 (both single-cycle and two-cycle types) | Rainbow coloring | [`no_order11_or_13`](PrimeSymmetry.lean) |
| Every point permutation of order 11 or 13 | Single Steiner system $S(15, 16, 32)$ | [`IsSteinerSystem.no_order11_or_13`](Steiner.lean) |

A regular action takes any given point to any other by exactly one group element. The abelian theorem allows a separate choice of color permutation for each group element; the proof shows that these choices automatically form a group action. [`property16_formulation`](Erdos835.lean) checks by definitional equality that the local rainbow predicate matches the linked Formal Conjectures statement at $k = 16$.

## Proof summaries

### Why an involution must move at least 30 points

On any invariant 17-set, label each point by the color obtained by deleting it. Every color appears exactly once, and the involution permutes these labels in the same way that it permutes the points. Every invariant 17-set therefore contains exactly as many fixed points as there are fixed colors.

Suppose an involution moves fewer than 30 points. Set aside two fixed points and one transposed pair. The remaining 28 points contain a fixed point. Choose an invariant 15-set among them by taking transposed pairs until you have seven or run out of pairs, then filling the remaining places with fixed points. Adjoining the two reserved fixed points or the reserved transposed pair gives two invariant 17-sets whose fixed-point counts differ by 2, a contradiction. [Lean proof](Involution.lean)

### Why orders 11 and 13 fail

For any 18-set $W$, color each edge $xy$ of the complete graph on $W$ by the color of $W \setminus \{x, y\}$. The 17 edges at $x$ have the colors of the 16-subsets of $W \setminus \{x\}$, using each color once, so every color gives a perfect matching of $W$.

A point permutation of order $p \in \{11, 13\}$ has at most two cycles of length $p$. Choose $W$ to contain one such cycle and $18 - p$ fixed points (there are enough fixed points even with two cycles). An edge between two fixed points has a fixed color, preserving its matching, so the partner of every fixed point must also be fixed by uniqueness. This would pair up 7 fixed points for $p = 11$, or 5 for $p = 13$, which is impossible.

For a single Steiner system, take the 14 points outside $W$ as a common core and join $x, y$ when adding them to the core gives a block; unique coverage of each 15-set yields an invariant perfect matching and the same parity contradiction for both cycle types of each prime. [Lean matching lemma](Edges.lean) · [Choice of $W$](Cycles.lean)

### Why regular abelian groups fail

Let $g$ be a fixed-point-free involution. Choose any nine of its transposed pairs to form $W$. A fixed color yields an invariant matching of 9 edges on $W$; since exchanged edges come in pairs, $g$ must fix an edge of that matching, which must be one of the nine transposed pairs. Distinct fixed colors use distinct edges, so at most 9 colors are fixed.

Suppose exactly 9 colors are fixed. Then every choice of 9 pairs has all 9 fixed colors among the 8-pair subsets obtained by deleting one pair. Restricting to 11 pairs and selecting one fixed color, the complements (within those 11 indices) of its 8-pair subsets form triples covering every 2-element subset of 11 indices once — partitioning 55 pairs into triples, impossible. Since an involution on 17 colors fixes an odd number of colors, $g$ fixes at most 7 colors. [Involution bound](PaletteBound.lean) · [Triple count](Nine.lean)

Now let an abelian group of order 32 act regularly on the points. Every nonidentity element has a power that is a nonidentity involution, so every nonidentity element fixes at most 7 colors. Burnside's lemma bounds the number of color orbits by $\lfloor(17 + 31 \cdot 7)/32\rfloor = 7$. Each orbit has a nontrivial point stabilizer (since $17 < 32$), and because the group is abelian that stabilizer fixes the whole orbit, forcing every orbit to have size 1, 2, or 4. Partitioning 17 colors into at most 7 such orbits requires two orbits of size 4. An ordered pair of representatives from those two orbits has at most 16 images, so some nonidentity element fixes both representatives and hence both orbits — giving 8 fixed colors, a contradiction. [Group-action proof](TranslationGroup.lean) · [Coloring theorem](Abelian.lean)

## Relation to earlier work

The September 2026 discussion excludes point permutations of prime orders 19, 23, 29, and 31 for colorings, and the associated computation separately excludes $\operatorname{AGL}(5, 2)$ and $\operatorname{PGL}(2, 31)$ for a single Steiner system. Because a coloring can have translation symmetry without having the full affine group as a symmetry, the abelian theorem above applies directly to the translation subgroup acting alone. [September 28 coloring argument](https://www.erdosproblems.com/forum/thread/835#post-9219) · [Single-system computations](https://github.com/veljjanoski/erdos835)

Some prime-order cases also follow from an earlier result of Kolotoğlu and Magliveras on automorphism groups of $S(4, 5, 21)$: deriving at an invariant 11-set gives that implication for order 11 and for a single 13-cycle, whereas a permutation with two 13-cycles and 6 fixed points has no invariant 11-set and is covered directly by the matching proof above. [Kolotoğlu and Magliveras, *Journal of Combinatorial Designs* (2014)](https://onlinelibrary.wiley.com/doi/10.1002/jcd.21370)

## The order-17 search

An order-17 permutation on 32 points rotates 17 points and fixes the other 15. The 16-subsets inside the rotating 17-set have distinct colors, so deleting the next point in the cycle advances the color through a 17-cycle as well.

Take the 17 rotating points and 3 fixed points to form a 20-set $W$, and represent each 16-subset of $W$ by the 4 points it omits. Every triple in $W$ has 17 extensions to a quadruple (one of each color), because its complement in $W$ is a 17-set. Thus the quadruples of one color must cover each triple once and meet each orbit of quadruples once; conversely, developing such a family through its 17 translates gives the required coloring on $W$. This coordinate reduction is formalized in Lean. [Coordinate theorem](Order17Coordinates.lean)

* **19-point seed:** the analogous 19-point problem is feasible; 57 seed triples cover all 171 pairs once and their translates partition all 969 triples. [Seed data](certificates/order17-19.json) · [Lean certificate](certificates/Order17On19.lean)
* **Partial 20-point family & nonextension:** on 20 points there is a 145-quadruple family retaining this 19-point seed at point 19 (covering all 460 triples meeting points 17, 18, or 19, plus 120 moving triples). Lean proves via exact-cover clauses and an LRAT refutation (`native_decide`) that no cyclic seed contains these 145 blocks (independent search: 526,346 nodes; reproduce residual CNF with `python search/order17_on20.py --extend certificates/order17-partial20.json`). Other choices of the 145 quadruples remain possible. [Partial design](certificates/order17-partial20.json) · [Lean certificate](certificates/Order17Partial20.lean) · [Nonextension theorem](Order17BoundaryGeometry.lean) · [Residual refutation](Order17BoundaryObstruction.lean)
* **Packings:** Lean kernel-checks packings of 257 quadruples (retaining all 145 boundary blocks) and 263 quadruples (covering 1,052 of 1,140 triples), both blocked at triple $\{0, 1, 15\}$. [Packing certificates](certificates/Order17Packings.lean) · [257 blocks](certificates/order17-packing257.json) · [263 blocks](certificates/order17-packing263.json)
* **Additional order-17 obstructions proved in Lean:**
  * A full seed has 140 wholly moving quadruples; every moving pair lies in 6 or 7, and every moving point in 32 or 33. [Counting proof](CoreCounts.lean)
  * No Steiner quadruple system on 20 points can contain all 140 zero-sum moving quadruples (mod 17). [Zero-sum obstruction](AdditiveCore.lean)
  * No cyclic 20-point seed is invariant under multiplication by 9 mod 17 (order 8), even on wholly moving quadruples alone (Boolean clauses + LRAT refutation via `native_decide`). [Multiplier proof](MultiplierCore.lean) · [SAT checker](MultiplierSAT.lean) · [Certificate generator](search/multiplier_core_certificate.py)
  * Reflection on the 17 moving points fixing the 3 extra points individually cannot carry a seed to any translate. [Reflection proof](Order17Reflection.lean)

Generate the full 20-point SAT instance (4,845 variables, 1,140 triple constraints, 285 orbit constraints) with `python search/order17_on20.py > order17_on20.cnf` ([generator](search/order17_on20.py)). Bounded CaDiCaL and CP-SAT searches did not decide the full instance; proving it unsatisfiable would exclude order-17 symmetry on 32 points.

## Verification

The project pins Lean **4.35.0-rc2** and mathlib. From this directory, run:

```sh
lake exe cache get
lake build
```

To print the axioms of the main theorems:

```sh
lake env lean --stdin <<'LEAN'
import Erdos835
#print axioms Erdos835.no_regular_abelian_symmetry
#print axioms Erdos835.no_order11_or_13
#print axioms Erdos835.IsSteinerSystem.no_order11_or_13
#print axioms Erdos835.involution_moves_at_least_thirty
#print axioms Erdos835.TwentyPoint.order17_requires_concrete_seed
#print axioms Erdos835.no_additive_quadruple_extension
#print axioms Erdos835.TwentyPoint.MultiplierCore.no_order_eight_multiplier
#print axioms Erdos835.Order17BoundaryObstruction.no_seed_contains_boundary
LEAN
```

## References

* [Erdős Problems #835](https://www.erdosproblems.com/835)
* [Formal Conjectures `ErdosProblems/835.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/835.lean)
* [Dated prior-art audit](../PRIOR_ART.md#erdős-835-coloring-subsets)
