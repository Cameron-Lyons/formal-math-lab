# Erdős Problem #835 at k = 16: symmetry obstructions for 17-color rainbow colorings

At $k = 16$, **Erdős Problem #835** asks whether we can color every 16-element subset of a 32-point set using **17 colors** so that every 17-element subset is **rainbow**—meaning its 17 internal 16-subsets display all 17 colors once each.

Equivalently, this asks whether $\binom{[32]}{16}$ can be partitioned into 17 **Steiner systems $S(15, 16, 32)$** (a family of 16-element "blocks" such that every 15-element subset lies in a unique block: indeed, for any 15-set $S$ and any two outside points $x, y$, the 17-set $S \cup \{x, y\}$ is rainbow, so $S \cup \{x\}$ and $S \cup \{y\}$ must get distinct colors, forcing each of the 17 colors to appear on exactly one extension $S \cup \{x\}$).

Whether such a coloring exists—at $k = 16$ or for general $k$—remains **open**. A standard attack on huge combinatorial structures is to study their **symmetries**: point permutations that map color classes to color classes (possibly permuting the 17 colors). This Lean 4 project rules out a wide swath of candidate symmetries:

* **Pure kernel-checked Lean proofs:** rule out every **regular abelian symmetry group of order 32**, every **involution (order 2) with at least 4 fixed points** (so any involution must move at least 30 of the 32 points), and every **point symmetry of order 11 or 13** (for both rainbow colorings and single Steiner systems $S(15, 16, 32)$).
* **Order-17 symmetry obstructions:** rule out several structured families of order-17 symmetry (pure kernel proofs for coordinate reduction, core counts, additive core, and reflection; two SAT/LRAT sub-results checked via `native_decide`).

## At a glance

| Field | Summary |
| --- | --- |
| Problem | Erdős Problem #835 (`erdosproblems.com/835`) at $k = 16$ (32 points, 17 colors, Steiner system $S(15, 16, 32)$), `FormalConjectures/ErdosProblems/835.lean` |
| Status | Partial results (symmetry obstructions). Existence at $k = 16$ and in general is still open. |
| Main theorems | `Erdos835.no_regular_abelian_symmetry`, `involution_moves_at_least_thirty`, `no_order11_or_13`, `IsSteinerSystem.no_order11_or_13`, `TwentyPoint.order17_requires_concrete_seed` |
| Verification | `lake exe cache get && lake build` (Lean 4.36.0 + mathlib; core symmetry theorems are kernel-checked, two order-17 SAT/LRAT sub-results use `native_decide`) |
| Prior art | Checked 23 November 2026: earlier work rules out prime orders 19, 23, 29, 31 and two groups on a single Steiner system, and Kolotoğlu and Magliveras (2014) imply the order-11 and single 13-cycle cases. See [Relation to earlier work](#relation-to-earlier-work). |

## Main symmetry exclusions in Lean

| Symmetry ruled out | Object | Lean theorem (namespace `Erdos835`) |
| --- | --- | --- |
| Every regular abelian group of order 32 (including cyclic shifts $\mathbb{Z}/32\mathbb{Z}$ and translations of $\mathbb{F}_2^5$) | Rainbow coloring | [`no_regular_abelian_symmetry`](Abelian.lean) |
| Every point involution (order 2) with at least 4 fixed points (moving $\le 28$ points) | Rainbow coloring | [`involution_moves_at_least_thirty`](Involution.lean) |
| Every point permutation of order 11 or 13 (single-cycle and two-cycle types) | Rainbow coloring | [`no_order11_or_13`](PrimeSymmetry.lean) |
| Every point permutation of order 11 or 13 | Single Steiner system $S(15, 16, 32)$ | [`IsSteinerSystem.no_order11_or_13`](Steiner.lean) |

A group acts **regularly** on the 32 points if any point can be mapped to any other by a unique group element. The abelian theorem allows each group element to choose its own color permutation, and the proof shows those permutations automatically form a group action. [`property16_formulation`](Erdos835.lean) checks by definitional equality that our local rainbow predicate matches the linked Formal Conjectures statement at $k = 16$.

## Proof summaries

### Why an involution must move at least 30 points

**The big idea.** An order-2 symmetry (involution) must fix the exact same number of points inside *every* invariant 17-subset. Yet having 4 or more fixed points gives enough wiggle room to build two invariant 17-subsets whose fixed-point counts differ by 2.

1. **Fixed points equal fixed colors:** Take any invariant 17-set, and label each point $x$ in it by the color of the 16-set obtained by deleting $x$. Because the 17-set is rainbow, every color appears once, and the involution permutes these labels in lockstep with the points. Therefore, **every invariant 17-set contains as many fixed points as there are fixed colors**.
2. **Swapping a pair for two fixed points:** Suppose an involution moves fewer than 30 points (so it fixes at least 4 points). Set aside two fixed points and one transposed pair. The remaining 28 points still contain at least one fixed point. Build an invariant 15-set among those 28 points by taking transposed pairs until you have 7 pairs or run out of pairs, then filling the remaining slots with fixed points. Adding *either* the two reserved fixed points *or* the reserved transposed pair yields two invariant 17-sets whose fixed-point counts differ by 2, a contradiction ([Involution.lean](Involution.lean)).

### Why orders 11 and 13 fail

**The 18-set perfect-matching trick.** Pick *any* 18-point subset $W$, and color each edge $xy$ of the complete graph on $W$ by the color of the 16-set $W \setminus \{x, y\}$. At any vertex $x \in W$, its 17 incident edges receive the colors of the 16-subsets of the 17-set $W \setminus \{x\}$, using each color once. Thus **every color class forms a perfect matching on $W$** (pairing up all 18 vertices).

**Parity contradiction for $p \in \{11, 13\}$.** A point permutation of prime order $p \in \{11, 13\}$ has at most two cycles of length $p$ (since $3p > 32$), leaving at least $32 - 2p$ fixed points (10 for $p = 11$, 6 for $p = 13$). Choose $W$ to consist of one $p$-cycle plus $18 - p$ fixed points ($7$ fixed points for $p = 11$, or $5$ for $p = 13$ — enough fixed points even with two cycles).

Take any edge between two fixed points in $W$. Its color is fixed by the permutation, so the permutation preserves that color's perfect matching on $W$. By uniqueness of matching partners, the partner of every fixed point in $W$ must also be fixed. That would pair up all 7 fixed points (for $p = 11$) or all 5 fixed points (for $p = 13$) — impossible because both numbers are odd!

**Single Steiner system $S(15, 16, 32)$.** Take the 14 points outside $W$ as a fixed core, and join $x, y \in W$ by an edge whenever adding $\{x, y\}$ to the core produces a block. Unique coverage of every 15-set gives an invariant perfect matching on $W$ and the exact same odd-parity contradiction for both cycle types of each prime ([Edges.lean](Edges.lean), [Cycles.lean](Cycles.lean)).

### Why regular abelian groups fail

**Part 1: Every fixed-point-free involution fixes at most 7 colors.** Let $g$ be a fixed-point-free involution (splitting the 32 points into 16 transposed pairs).

* *At most 9 fixed colors:* Pick any 9 of those 16 pairs to form an invariant 18-set $W$. Every color fixed by $g$ yields a $g$-invariant perfect matching of 9 edges on $W$. Because edges moved by $g$ come in swapped pairs and 9 is odd, $g$ must fix at least one edge of the matching—which must be one of the 9 transposed pairs. Distinct fixed colors have disjoint matchings and hence use distinct transposed pairs, so $g$ fixes at most 9 colors.
* *Not 9 fixed colors:* Suppose $g$ fixes 9 colors. Then for every choice of 9 pairs, all 9 fixed colors appear among the 8-pair subsets obtained by deleting one pair. Restrict to 11 pairs and pick one fixed color. Within those 11 indices, the complements of its 8-pair subsets are 3-element subsets (triples) covering every 2-element subset of the 11 indices exactly once. That would partition $\binom{11}{2} = 55$ pairs into triples (3 pairs per triple), which is impossible since $3 \nmid 55$.
* *At most 7 fixed colors:* Because an involution acting on 17 colors fixes an odd number of colors, $g$ fixes at most 7 colors ([PaletteBound.lean](PaletteBound.lean), [Nine.lean](Nine.lean)).

**Part 2: Burnside's lemma and pigeonhole kill any regular abelian group of order 32.** Now let an abelian group $G$ of order 32 act regularly on the 32 points.

1. Every nonidentity element of $G$ has order a power of 2, so some power of it is a nonidentity (hence fixed-point-free) involution. Therefore **every nonidentity element of $G$ fixes at most 7 colors**.
2. By **Burnside's lemma**, the number of color orbits is at most

   $$
   \left\lfloor \frac{17 + 31 \cdot 7}{32} \right\rfloor = \left\lfloor \frac{234}{32} \right\rfloor = 7.
   $$

3. Because $17 < 32$, each orbit has a nontrivial point stabilizer, and because $G$ is abelian, that stabilizer fixes the *entire* orbit. Since no nonidentity element can fix 8 or more colors, no orbit can have size 8 or 16—every orbit has size **1, 2, or 4**.
4. Partitioning 17 colors into at most 7 orbits of sizes $\in \{1, 2, 4\}$ requires **at least two orbits of size 4** (since $4 + 6 \cdot 2 = 16 < 17$).
5. Pick one representative color from each of two size-4 orbits. As $g$ runs over the 32 elements of $G$, this ordered pair has at most $4 \times 4 = 16$ distinct images. By the pigeonhole principle, some nonidentity element fixes *both* representatives, and hence (by commutativity) all $4 + 4 = 8$ colors in their two orbits—contradicting the bound of at most 7 fixed colors ([TranslationGroup.lean](TranslationGroup.lean), [Abelian.lean](Abelian.lean)).

## Relation to earlier work

The [September 28, 2026 coloring argument](https://www.erdosproblems.com/forum/thread/835#post-9219) rules out point permutations of prime orders 19, 23, 29, and 31 for colorings, and the associated [single-system computations](https://github.com/veljjanoski/erdos835) rule out $\operatorname{AGL}(5, 2)$ and $\operatorname{PGL}(2, 31)$ for a single Steiner system. Because a coloring can have translation symmetry without full affine symmetry, our abelian theorem directly covers the translation subgroup on its own.

Some prime-order cases also follow from [Kolotoğlu and Magliveras (*Journal of Combinatorial Designs*, 2014)](https://onlinelibrary.wiley.com/doi/10.1002/jcd.21370) on automorphism groups of $S(4, 5, 21)$. Deriving at an invariant 11-set gives order 11 and a single 13-cycle, whereas a permutation with two 13-cycles and 6 fixed points has no invariant 11-set and is handled directly by the matching proof above.

## The order-17 search

An order-17 symmetry on 32 points rotates 17 points in a single cycle and fixes the other 15. The 16-subsets inside the rotating 17-set have all 17 distinct colors, so shifting the omitted point one step around the cycle advances the color through a 17-cycle as well.

**Reduction to a 20-point cyclic seed.** Take the 17 rotating points plus 3 fixed points to form a 20-set $W$, and represent each 16-subset of $W$ by the 4 points it omits. Every triple in $W$ has a 17-point complement in $W$, so its 17 extensions to a quadruple must carry all 17 colors once each. Consequently, the quadruples of one color—a **cyclic seed**—must cover every triple in $W$ once and meet each cyclic orbit of quadruples once; conversely, developing such a family through its 17 cyclic translates produces the required coloring on $W$ ([Order17Coordinates.lean](Order17Coordinates.lean)).

* **19-point seed (feasible):** The analogous 19-point problem has a solution: 57 seed triples cover all 171 pairs once and their translates partition all 969 triples ([certificates/order17-19.json](certificates/order17-19.json), [certificates/Order17On19.lean](certificates/Order17On19.lean)).
* **Partial 20-point family and nonextension:** On 20 points, a 145-quadruple family keeps this 19-point seed at point 19 (covering all 460 triples meeting points 17, 18, or 19, plus 120 moving triples). Using exact-cover clauses and an LRAT refutation (`native_decide`), Lean proves that no cyclic seed contains these 145 blocks. Other choices of the 145 quadruples remain possible ([certificates/order17-partial20.json](certificates/order17-partial20.json), [certificates/Order17Partial20.lean](certificates/Order17Partial20.lean), [Order17BoundaryGeometry.lean](Order17BoundaryGeometry.lean), [Order17BoundaryObstruction.lean](Order17BoundaryObstruction.lean)).
* **Packings:** Lean kernel-checks packings of 257 quadruples (keeping all 145 boundary blocks) and 263 quadruples (covering 1,052 of 1,140 triples). Both stall at triple $\{0, 1, 15\}$ ([certificates/Order17Packings.lean](certificates/Order17Packings.lean), [257 blocks](certificates/order17-packing257.json), [263 blocks](certificates/order17-packing263.json)).
* **Further order-17 obstructions proved in Lean:**
  * A full seed has 140 wholly moving quadruples; every moving pair lies in 6 or 7, and every moving point in 32 or 33 ([CoreCounts.lean](CoreCounts.lean)).
  * No Steiner quadruple system on 20 points can contain all 140 zero-sum moving quadruples mod 17 ([AdditiveCore.lean](AdditiveCore.lean)).
  * No cyclic 20-point seed is invariant under multiplication by 9 mod 17 (order 8), even on wholly moving quadruples alone (Boolean clauses plus LRAT refutation via `native_decide`; [MultiplierCore.lean](MultiplierCore.lean), [MultiplierSAT.lean](MultiplierSAT.lean)).
  * Reflection on the 17 moving points fixing the 3 extra points individually cannot carry a seed to any translate ([Order17Reflection.lean](Order17Reflection.lean)).

## Verification

Lean and mathlib are pinned to 4.36.0. From this directory, run:

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
