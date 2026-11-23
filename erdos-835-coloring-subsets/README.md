# Symmetries in Erdős problem 835 at k = 16

A rainbow coloring assigns 17 colors to the 16-subsets of a 32-point set so that every 17-set contains all colors. A point permutation is a symmetry if it carries color classes to color classes. It may permute the 17 colors.

Lean proves the following restrictions on the 32-point problem.

| Symmetry excluded | Object | Lean theorem |
| --- | --- | --- |
| Every regular abelian group of order 32, including cyclic shifts and the translations of the five-dimensional binary vector space | Rainbow coloring | [`no_regular_abelian_symmetry`](Abelian.lean) |
| Every point permutation of order two with at least four fixed points | Rainbow coloring | [`involution_moves_at_least_thirty`](Involution.lean) |
| Every point permutation of order 11 or 13 | Rainbow coloring | [`no_order11_or_13`](PrimeSymmetry.lean) |
| Every point permutation of order 11 or 13 | A single Steiner system S(15,16,32) | [`IsSteinerSystem.no_order11_or_13`](Steiner.lean) |

A regular action takes any given point to any other by exactly one group element. The abelian theorem allows a separate choice of color permutation for each group element. The proof shows that these choices automatically form a group action. The unrestricted existence question at k = 16 and the original question over all k remain open. [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/835.lean)

## Why an involution must move at least 30 points

On any invariant 17-set, label each point by the color obtained by deleting it. Every color appears exactly once, and the involution permutes these labels in the same way that it permutes the points. Every invariant 17-set therefore contains exactly as many fixed points as there are fixed colors.

Suppose an involution moves fewer than 30 points. Set aside two fixed points and one transposed pair. The remaining 28 points contain a fixed point. Choose an invariant 15-set among them. Take transposed pairs until you have seven or run out of pairs, then fill the remaining places with fixed points. Adjoining the two reserved fixed points or the reserved transposed pair now gives two invariant 17-sets. The first has two more fixed points than the second, a contradiction. [Lean proof](Involution.lean)

## Why orders 11 and 13 fail

For any 18-set W, color the edge xy of the complete graph on W by the color of W with x and y removed. The 17 edges at x have the colors of the 16-subsets of W with x removed. They use each color exactly once. Every color therefore gives a perfect matching of W.

A point permutation of order p = 11 or 13 has at most two cycles of length p. Choose W to contain one such cycle and 18 − p fixed points. There are enough fixed points even when there are two cycles. An edge between two fixed points has a fixed color, so its entire matching is preserved. The partner of every fixed point must also be fixed by uniqueness. This would pair up seven fixed points for p = 11, or five for p = 13.

For a single Steiner system, take the 14 points outside W as a common core. Join x and y exactly when adding them to the core gives a block. Unique coverage of each 15-set gives an invariant perfect matching and the same parity contradiction. This proof covers both cycle types for each prime. [Lean matching lemma](Edges.lean) · [Choice of W](Cycles.lean)

## Why abelian translations fail

Let g be a point involution with no fixed point. Choose any nine of its transposed pairs to form W. A fixed color yields an invariant matching of nine edges on W. The involution must fix an edge of that matching, because exchanged edges come in twos. Such an edge is one of the original nine transposed pairs. Distinct fixed colors use distinct edges, so at most nine colors are fixed.

Suppose exactly nine colors are fixed. Then every choice of nine pairs has all nine fixed colors among the eight-pair subsets obtained by deleting one pair. Restrict to eleven pairs and select one fixed color. The complements, within these eleven indices, of its eight-element subsets are triples. Each two-element subset is in exactly one of these triples, by the rainbow condition on its nine-element complement. This would partition 55 pairs into sets of three. As the number of fixed colors of an involution on 17 colors is odd, g fixes at most seven colors. [Involution bound](PaletteBound.lean) · [Triple count](Nine.lean)

Now let an abelian group of order 32 act regularly on the points. If a coloring admitted this action, every nonidentity element would fix at most seven colors. Indeed, a power of that element is a nonidentity involution and fixes every color the element fixes. Burnside's lemma bounds the number of color orbits by ⌊(17 + 31 · 7)/32⌋ = 7. Each orbit has a nontrivial point stabilizer since there are fewer than 32 colors. As the group is abelian, that stabilizer fixes the whole orbit, so every orbit has size 1, 2, or 4. Fitting 17 colors into at most seven such orbits requires two orbits of size four. An ordered pair of representatives from those two orbits has at most 16 images. A nonidentity element fixes both representatives and hence both orbits, giving eight fixed colors. [Group-action proof](TranslationGroup.lean) · [Coloring theorem](Abelian.lean)

## Relation to earlier work

The September 2026 discussion excludes point permutations of prime orders 19, 23, 29, and 31 for colorings. The associated computation separately excludes the two groups AGL(5,2) and PGL(2,31) for a single Steiner system. A coloring can have translation symmetry without having the full affine group as a symmetry. The abelian result above applies directly to the translation subgroup acting alone. [September 28 coloring argument](https://www.erdosproblems.com/forum/thread/835#post-9219) · [Single-system computations](https://github.com/veljjanoski/erdos835)

Some prime-order cases also follow from an earlier result of Kolotoğlu and Magliveras on automorphism groups of S(4,5,21). Deriving at an invariant 11-set gives that implication for order 11 and for a single 13-cycle. A permutation with two 13-cycles and six fixed points has no invariant 11-set. The matching proof covers that case directly. [Kolotoğlu and Magliveras, Journal of Combinatorial Designs (2014)](https://onlinelibrary.wiley.com/doi/10.1002/jcd.21370)

## The order-17 search

An order-17 permutation on 32 points rotates 17 points and fixes the other 15. The 16-subsets inside the rotating 17-set have distinct colors. Deleting the next point in the cycle therefore advances the color through a 17-cycle as well.

Take the rotating points and three fixed points to form a 20-set W. Represent each 16-subset of W by the four points it omits. Every triple in W has 17 extensions to a quadruple, one of each color, because its complement in W is a 17-set. The quadruples of one color must therefore cover each triple exactly once and meet each orbit of quadruples exactly once. Conversely, developing such a family through its 17 translates gives the required coloring on W.

The reduction from a 32-point coloring with order-17 symmetry to these precise search coordinates is formalized in Lean. [Coordinate theorem](Order17Coordinates.lean)

The analogous 19-point problem is feasible. The 57 seed triples cover all 171 pairs once, and their translates partition all 969 triples. [Seed data](certificates/order17-19.json) · [Lean certificate](certificates/Order17On19.lean)

On 20 points there is a family of 145 quadruples that retains this exact 19-point seed at point 19. Every one of the 460 triples meeting points 17, 18 or 19 occurs once. The family also covers 120 distinct triples on the moving points, and its 17 translates partition the 2,465 quadruples meeting a fixed point. A full family would still require 140 quadruples on the moving points. [Partial design](certificates/order17-partial20.json) · [Lean certificate](certificates/Order17Partial20.lean)

On this particular family the residual search has 1,022 candidate quadruples and 700 exact-one constraints. Lean proves that no cyclic seed can contain these 145 blocks. The proof checks the incidences, derives the exact-cover clauses, and verifies an LRAT refutation. It uses compiled evaluation for these finite checks. An independent exhaustive search visited 526,346 nodes. Reproduce the residual CNF with `python search/order17_on20.py --extend certificates/order17-partial20.json`. Other choices of the 145 quadruples remain possible. [Nonextension theorem](Order17BoundaryGeometry.lean) · [Residual problem and refutation](Order17BoundaryObstruction.lean)

The search also found a packing of 257 quadruples retaining the entire 145-block family, and a separate packing of 263 quadruples covering 1,052 of the 1,140 triples. In each packing every triple occurs at most once, and all 17 translates are disjoint. In both examples the missing triple {0,1,15} has no compatible fourth point. Lean checks these statements by kernel reduction. [Packing certificates](certificates/Order17Packings.lean) · [257 blocks](certificates/order17-packing257.json) · [263 blocks](certificates/order17-packing263.json)

The local proofs also establish the following restrictions.

* A full seed has exactly 140 wholly moving quadruples. Every moving pair belongs to six or seven of them, and every moving point belongs to 32 or 33. [Counting proof](CoreCounts.lean)
* No single Steiner quadruple system on 20 points can contain all 140 moving quadruples whose labels sum to zero modulo 17. In any extension, a specified set of 36 triples would require completion using the three extra points. Distinct triples that share two points must use different extra points, and Lean exhausts the three-color assignments to this finite graph. [Zero-sum obstruction](AdditiveCore.lean)
* Multiplication by 9 modulo 17 has order eight. A cyclic 20-point seed cannot be invariant under this map even when invariance is assumed only for its wholly moving quadruples. The proof checks that every such seed would satisfy a particular collection of Boolean clauses and checks an LRAT refutation of those clauses. Lean uses compiled evaluation (`native_decide`) for finite geometry and the LRAT checker. [Multiplier proof](MultiplierCore.lean) · [SAT checker](MultiplierSAT.lean) · [Certificate generator](search/multiplier_core_certificate.py)
* Reflection on the 17 moving points while fixing all three extra points individually cannot carry a seed to any of its translates. [Reflection proof](Order17Reflection.lean)

Generate the full 20-point instance with `python search/order17_on20.py > order17_on20.cnf`. The 4,845 Boolean variables select quadruples. The 1,140 triple constraints and 285 orbit constraints each require exactly one of 17 quadruples. The generator allows every 19-point seed and imposes only the specified cycle. Bounded CaDiCaL and CP-SAT searches did not decide this instance. A complete local design could be tested for extension to 21 points. A proof that the full instance is unsatisfiable would exclude the order-17 symmetry on 32 points. [Instance generator](search/order17_on20.py)

## Verification

The project pins Lean 4.35.0-rc2 and mathlib. From this directory, run

```sh
lake exe cache get
lake build
```

[`property16_formulation`](Erdos835.lean) checks by definitional equality that the local rainbow predicate gives the existential in the linked statement at k = 16. The proofs use only mathlib and the local modules. To print the logical dependencies of the main conclusions, run

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
