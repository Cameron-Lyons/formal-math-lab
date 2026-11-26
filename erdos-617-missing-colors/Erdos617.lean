module

public import Erdos617.Affine
public import Erdos617.AffinePalette
public import Erdos617.AlmostParallelRows
public import Erdos617.CriticalSquare
public import Erdos617.ForeignCliquePacking
public import Erdos617.FourIndependent
public import Erdos617.FourWitnessRowSquare
public import Erdos617.FullCliquePropagation
public import Erdos617.FullForeignTransversals
public import Erdos617.GrowingRowSquare
public import Erdos617.LeastCounterexample
public import Erdos617.LineMultiplicityRange
public import Erdos617.MultiCover
public import Erdos617.NearCliqueOverlap
public import Erdos617.ObstructionMatching
public import Erdos617.OddIntersection
public import Erdos617.OddResidualSplit
public import Erdos617.PaletteCycles
public import Erdos617.PolynomialObstruction
public import Erdos617.QuadraticObstruction
public import Erdos617.RankOneVariance
public import Erdos617.RankTwoCycle
public import Erdos617.SmallRange
public import Erdos617.SmallerPalette
public import Erdos617.SquareEditDistance
public import Erdos617.ThreeColors
public import Erdos617.TransversalCliques
public import Erdos617.TransverseNearLines
public import Erdos617.Turan

@[expose] public section

/-!
# Partial proofs for Erdős problem 617

* `missing_of_all_but_two_parallel_rows` proves the original conclusion
  for every `r≥3` if one color contains `r−2` vertex-disjoint cliques of
  order `r`. More generally,
  `missing_of_almost_parallel_full_cliques` only needs `r−q` of them
  whenever `1000(2q+1)²<r`.
* `MinimalObstruction.packed_full_foreign_color` finds, in a first
  obstruction of rank t, at least `r−2t+4` vertex-disjoint cliques of
  order t in one other color. They are all maximum independent sets
  for the obstruction color.
* `counterexample_rank_window` combines the color threshold, rank window,
  and matching estimates on a single obstruction.
* `three_avoidable_on_every_square` proves that on **every** subset of
  order `(r−1)²+1` in a counterexample with `r≥6`, at least three colors
  can individually be omitted on r vertices. This rules out the exactly-two
  branch in `least_counterexample_descent` and precludes a one-step palette
  merger on any such subset.
* `exists_row_square_many_ambient_witnesses` finds two full monochromatic
  cliques meeting at one vertex. Their complement is a square of side r−1.
  Both clique colors occur on every r-set there, and at least (r−99)/33
  other colors can individually be omitted on r vertices in that same
  square. `missing_of_few_avoidable_on_two_line_square` gives the original
  missing-color conclusion when the numerical bound fails.
* `exists_square_of_sharp_quadratic_gap` finds a square of order
  `(r−m)²+1` where two colors occur on every `(r−m+1)`-set, whenever
  `m≥2` and `min (3m²) (2m²+140m)≤r`.
* `exists_transversal_full_rows` finds at least `2*r+1` monochromatic
  r-cliques. Within each color the selected cliques are disjoint, and
  between colors they meet exactly once. Deleting one or two rows in
  each of two directions gives `exists_square_of_at_most_two_rows`.
  Every full clique contains a point on full cliques of three colors
  by `triple_point_on_every_full_clique`.
* `independent_six_in_subset_of_thirty_three_le` shows that in every
  balanced coloring with at least 33 colors, every set of `5*r+1`
  vertices contains six avoiding any prescribed color.
  `MinimalObstruction.rank_five_lt_thirty_three` excludes rank five above
  32 colors, and `exists_rank_five_eleven` isolates it at eleven colors.
* `missing_matching` finds b+1 disjoint edges avoiding a specified color
  in any r+b vertices containing no r-clique of that color when r>2b+2.
  `MinimalObstruction.matching_reduction` applies these matchings to all
  minimal obstructions in the half-range, bounding the edges lost when
  the minimum-degree vertex and its neighbors are deleted.
* `MinimalObstruction.exists_clique_bouquet` finds a common vertex and
  one monochromatic clique per color covering all but 2t−3 vertices of
  the obstruction. At least r−t+3 of the other colors have clique size t.
  `CliqueBouquet.perfect_matching` finds a matching in the original color
  between the remaining t−1 vertices of any two such cliques.
* `MinimalObstruction.exists_palette_product_obstructions` finds, for every
  other color `j`, a subset of order `a_j*b_j+1`, where `a_j` and `b_j`
  are its independence numbers in the original color and in `j`.
  The mean of the `b_j` is strictly less than `(t+1)/2` over the reals.
  When `t=4`, `MinimalObstruction.majority_odd_cycles` forces distinct
  induced odd cycles for a strict majority of the other colors.
* `odd_endpoint_grids` describes the case `r=2*s+1` in which no obstruction
  has parameter at most `s`. At least three colors have at most the average
  number of edges. Each such color has exactly `s` monochromatic r-cliques.
  These are disjoint and partition the complement of its core. At most
  `s-1` edges of that color join different parts of the partition consisting
  of the core and the cliques. Cliques from two of these families meet in one
  vertex, and their cores meet in `(s+1)^2+1` vertices with independence number
  at most `s+1` in both colors.
* `full_clique_propagation` shows that each monochromatic r-clique meets at
  least `r-2+h` distinct r-cliques of other colors, where `h` counts outside
  vertices with an edge of the original color into the clique.
* `missing_of_sparse_line_subgraph` proves the original conclusion for any
  number of colors when one color contains a spanning line graph of a loopless
  multigraph with independence number and average degree both at most `r`.
  Without the degree hypothesis, multiplicity at most five suffices by
  `missing_of_line_subgraph_of_multiplicity_le_five`. The sufficient bound
  in `missing_of_line_subgraph_of_multiplicity_range` grows with `r`.
* `MinimalObstruction.qfold_clique_cover_card` shows that covering a minimal
  obstruction of independence number `t` at least `q` times by cliques in
  its color takes at least `q*t+2` cliques for every `q ≥ 2`.
* `exists_nested_obstruction_quadratic_range` finds two distinct colors on a
  subset of the same obstruction. Their independence numbers `a` and `b`
  satisfy `a ≤ t` and `2*b ≤ t`, and the subset has `a*b+1` vertices.
  Every proper subset has order at most the product of its two independence numbers.
  For `t ≤ 5`, `MinimalObstruction.exists_nested_odd_cycle` proves that
  the first color induces an odd cycle on this subset.
* `MinimalObstruction.foreign_clique_packing` gives more than
  `(r-1)*(r-t+1)` cliques across the other colors, disjoint within each
  color, each with between `t-⌊√t⌋` and `t` vertices.
* `exists_minimalObstruction_quadratic_range` proves that a balanced coloring
  on `r²+1` vertices forces a color k and a subset of `t*r+1` vertices
  with independence number t in color k, where `r ≤ 1000*t^2` and
  `t ≤ (r+1)/2` (natural-number division).
* `independent_in_subset_of_quadratic_palette` works in any balanced coloring.
  For every prescribed color k, every `p*r+1` vertices contain `p+1`
  vertices avoiding k whenever `1000*p^2 < r`.
* `missing_of_local_window` gives the original missing-color conclusion if the
  local independence statement holds throughout the remaining parameter range.
* `missing_of_at_most_ten_colors` proves the conjecture for all `3 ≤ r ≤ 10`.
* `missing_of_degree_excess` proves the conjectured conclusion if one color has
  fewer than `r` total incidences above the degree allowance `r`.
  `missing_of_bounded_color_degree` includes the case of zero such incidences.
  `missing_of_regular_colors` applies this to colorings with regular color classes.
* `missing_color_on_r_vertices` gives an unconditional set of size `r` once
  the number of vertices exceeds `(r - 1)^2`.
* `erdos_617.variants.r2` proves sharpness for infinitely many color counts.
  `missing_of_affine_extension` proves that adjoining a vertex to the finite
  field slope construction forces a missing color.
* For any balanced coloring and any prescribed color, `independent_three_in_subset`
  gives an independent triple inside any `2*r+1` vertices for `r ≥ 3`.
  `independent_four_in_subset` gives a four-set inside any `3*r+1` vertices for `r ≥ 6`.
  `independent_five_in_subset_of_seven_le` gives five inside any `4*r+1` vertices for `r ≥ 7`.
* `exists_minimalObstruction` extracts a color and a set of `t*r+1` vertices,
  for `1 ≤ t < r`, from any counterexample. Every proper subset satisfies the
  independence bound. The obstruction contains no clique of size `r` in that
  color, and `MinimalObstruction.twice_edges_ge` bounds its edge count from below.
  Counting the other colors gives `r*(4*t+1) ≤ r*t^2+4*t` in
  `MinimalObstruction.parameter_bound`.

In a hypothetical counterexample every color must have total degree excess
at least `r`. The edge counts at individual vertices do not by themselves rule
this out. By `missing_of_last_local_step`, extending the local bounds to
`r` independent vertices on `(r-1)*r+1` vertices would suffice.

The conjecture and the three-color result are due to Erdős and Gyárfás in
[Split and balanced colorings of complete graphs](https://doi.org/10.1016/S0012-365X(98)00323-9).
The target statements are in the
[Formal Conjectures collection](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/617.lean).
-/

namespace Erdos617

open scoped Classical in
/-- A coloring with too few individually avoidable colors outside two full
lines has a missing color on r+1 vertices in the original graph. -/
theorem missing_of_few_avoidable_on_two_line_square {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) {i j : Fin r} (C D U : Finset V)
    (fullC : (colorGraph c i).IsNClique r C) (fullD : (colorGraph c j).IsNClique r D)
    (meet : (C∩D).card=1) (out : Disjoint U (C∪D)) (sz : U.card=(r-1)^2+1)
    (few : let d := fun e : Sym2 U => c (e.map Subtype.val)
           33*(Finset.univ.filter fun k => ¬HitsPalette d (r-1) {k}).card+99<r) :
    ∃ (S : Finset V) (k : Fin r), S.card=r+1 ∧
      ∀ x∈S, ∀ y∈S, x≠y → c s(x,y)≠k := by
  by_contra absent
  exact few.not_ge (two_line_avoidable_linear_bound hn c (balanced_of_no_witness c absent)
    C D U fullC fullD meet out sz)

/-- Necessary conditions on the whole palette of an arbitrary counterexample.
The same outer set and parameter work for all the restrictions. -/
theorem counterexample_palette_descent {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (hr : 3 ≤ r) (hn : Fintype.card V = r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c) :
    ∃ (k : Fin r) (t : ℕ) (S : Finset V) (W : Fin r → Finset V),
      4 ≤ t ∧ t ≤ (r+1)/2 ∧ r ≤ 1000*t^2 ∧ MinimalObstruction c k t S ∧
      (∀ j ≠ k, W j ⊆ S ∧
        RankProductObstruction (colorGraph c k) (colorGraph c j) (W j) ∧
        (W j).card = rankOn (colorGraph c k) (W j) * rankOn (colorGraph c j) (W j) + 1 ∧
        2 ≤ rankOn (colorGraph c k) (W j) ∧ rankOn (colorGraph c k) (W j) ≤ t ∧
        2 ≤ rankOn (colorGraph c j) (W j)) ∧
      2*(∑ j ∈ Finset.univ.erase k, (rankOn (colorGraph c j) (W j)-1)) < (r-1)*(t-1) := by
  obtain ⟨k,t,S,hlo,hhi,h⟩ := exists_minimalObstruction_quadratic_range hr hn c hb
  have htr : t < r := by omega
  obtain ⟨j,_,U,_,_,_,hhalf,_,hsecond,_⟩ := h.exists_nested_product_obstruction hr hb htr
  obtain ⟨W,hw,hsum⟩ := h.exists_palette_product_obstructions hr hb htr
  refine ⟨k,t,S,W,by omega,hhi,hlo,h,?_,hsum⟩
  intro j hj
  obtain ⟨hsub,hprod,hbounds⟩ := hw j hj
  exact ⟨hsub,hprod,hprod.card_eq,hbounds⟩

/-- Every counterexample has at least eleven colors and a minimal obstruction
in this parameter window. The same obstruction satisfies the matching bounds. -/
theorem counterexample_rank_window {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (hr : 3≤r) (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c) :
    11≤r ∧ ∃ (k : Fin r) (t : ℕ) (S : Finset V), 5≤t ∧ (33≤r → 6≤t) ∧
      r≤1000*t^2 ∧ t≤(r+1)/2 ∧ MinimalObstruction c k t S ∧
      ∃ (b z : ℕ) (W : Finset V), 1≤b ∧ b+3≤t ∧ W⊂S ∧ W.card+(r+b)=S.card ∧
        rankOn (colorGraph c k) W<t ∧
        blockEdges (colorGraph c k) S=(r+b).choose 2+z+blockEdges (colorGraph c k) W ∧
        (∀ m≤b+1, m*(r+1-b)≤z+(2*m).choose 2) ∧ r*(b+1)≤16*z := by
  have large : 11≤r := by
    by_contra! small
    obtain ⟨T,k,n,avoid⟩ := missing_of_at_most_ten_colors hr (by omega) hn c
    obtain ⟨x,hx,y,hy,xy,edge⟩ := hb T n k
    exact avoid x hx y hy xy edge
  obtain ⟨k,t,S,quad,half,h⟩ := exists_minimalObstruction_quadratic_range hr hn c hb
  have lt : t<r := by omega
  have lower := h.five_le_of_seven_le (by omega) hb lt
  exact ⟨large,k,t,S,lower,fun high => h.six_le_of_thirty_three_le high hb lt,
    quad,half,h,h.matching_reduction (by omega) (by omega) half hb⟩

/-- The three-color variant in the exact interface of Formal Conjectures. -/
theorem erdos_617.variants.r_eq_3 (r : ℕ) (_hr : r ≥ 3) {V : Type} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V = 3^2 + 1) (coloring : Sym2 V → Fin 3) :
    ∃ (S : Finset V) (k : Fin 3), S.card = 3 + 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u,v) ≠ k :=
  three_colors hV coloring

/-- For the full range r ≥ 3, a color whose total degree excess is less than r
forces the desired witness in the coloring. -/
theorem missing_of_degree_excess {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (hr : 3 ≤ r) (hV : Fintype.card V = r^2+1) (c : Sym2 V → Fin r) (k : Fin r)
    (hT : (∑ v, ((colorGraph c k).degree v - r)) < r) :
    ∃ (S : Finset V) (l : Fin r), S.card = r+1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u,v) ≠ l := by
  rcases eq_or_lt_of_le hr with he | h
  · subst r
    exact three_colors hV c
  · exact missing_of_total_excess_lt h hV c k hT

end Erdos617
