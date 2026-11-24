import Wall133.BipartiteAll
import Wall133.RegularAll
import Wall133.StrictOrderBound
import Wall133.BlocksBranchVertices
import Wall133.BlocksTriangleTips
import Wall133.GirthSixFar
import Wall133.GirthSixSevenRing
import Wall133.FourCycleFreeMinDegree
import Wall133.ShortGirthFourthBand
import Wall133.ShortGirthFive
import Wall133.FifthDensity
import Wall133.FifthEccentricity
import Wall133.CoreExterior
import Wall133.HereditaryDensity
import Wall133.GirthSixDensity
import Wall133.NeighborhoodTriangles
import Wall133.Pentagon
import Wall133.Hexagon

/-!
# Written on the Wall II, conjecture 133 (floored version)

`FlooredConjecture` uses the path and neighborhood-independence invariants of
Formal Conjectures. Its exponent agrees with the explicit four-vertex cycle
test by `noFourCycle_iff`.

`floored_of_floor_le_four` proves all values below average five, including
graphs with triangles. In the last radius-four case a local configuration
of independent neighbors forces an induced path on eight vertices.

The bound also holds for connected regular graphs, bipartite graphs, and
graphs of diameter at most two. At girth at least six every even floor and floor five
hold, while every odd floor is within one vertex of the desired bound.
At floor five only radii four and five and girths three and five remain.
The order estimate implies the conjecture for all graphs on at most 29 vertices.
-/

namespace Wall133

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The inequality in the question. The exponent is zero in the presence of
a four-cycle, including one with a chord. -/
noncomputable def FlooredConjecture (G : SimpleGraph V) : Prop := by
  classical
  exact (G.radius.toNat : ℝ) + (⌊l G⌋ : ℝ) ^ (if NoFourCycle G then 1 else 0 : ℕ) ≤ G.path

omit [DecidableEq V] [Nontrivial V] [DecidableRel G.Adj] in
private lemma average_nonneg : 0 ≤ l G :=
  div_nonneg (Finset.sum_nonneg (fun v _ => Nat.cast_nonneg (G.indepNeighborsCard v))) (Nat.cast_nonneg _)

omit [Nontrivial V] [DecidableRel G.Adj] in
theorem floored_iff_of_noFourCycle (h4 : NoFourCycle G) :
    FlooredConjecture G ↔ G.radius.toNat + ⌊l G⌋₊ ≤ G.path := by
  classical
  simp only [FlooredConjecture, if_pos h4, pow_one, ← Int.natCast_floor_eq_floor (average_nonneg (G := G)),
    Int.cast_natCast]
  exact_mod_cast (Iff.rfl : G.radius.toNat + ⌊l G⌋₊ ≤ G.path ↔ _)

omit [Nontrivial V] [DecidableRel G.Adj] in
theorem floored_of_fourCycle (hc : G.Connected) (h4 : ¬ NoFourCycle G) : FlooredConjecture G := by
  classical
  simp only [FlooredConjecture, if_neg h4, pow_zero]
  exact_mod_cast radius_add_one_le_path G hc

omit [Nontrivial V] in
/-- The conjecture with its four-cycle exponent, for connected bipartite
graphs of radius at most six. -/
theorem floored_of_bipartite_radius_le_six (hc : G.Connected) (hb : G.IsBipartite)
    (hr : G.radius.toNat ≤ 6) : FlooredConjecture G := by
  classical
  have : Nonempty V := hc.nonempty
  by_cases h4 : NoFourCycle G
  · exact (floored_iff_of_noFourCycle h4).2
      (radius_add_floor_le_path_of_bipartite_radius_le_six hc hb h4 hr)
  · exact floored_of_fourCycle hc h4

omit [Nontrivial V] [DecidableRel G.Adj] in
/-- The floored version of Graph Conjecture 133 holds for every finite
connected bipartite graph, at every radius and with arbitrary degrees. -/
theorem floored_of_bipartite (hc : G.Connected) (hb : G.IsBipartite) : FlooredConjecture G := by
  classical
  have : Nonempty V := hc.nonempty
  by_cases h4 : NoFourCycle G
  · exact (floored_iff_of_noFourCycle h4).2 (radius_add_floor_le_path_of_bipartite hc hb h4)
  · exact floored_of_fourCycle hc h4

omit [Nontrivial V] [DecidableRel G.Adj] in
private theorem nontrivial_of_counterexample (hc : G.Connected) (bad : ¬FlooredConjecture G) :
    Nontrivial V := by
  by_contra absent
  let : Subsingleton V := not_nontrivial_iff_subsingleton.mp absent
  exact bad (floored_of_bipartite hc
    ⟨fun _ => (0 : Fin 2), fun {x y} h => False.elim (h.ne (Subsingleton.elim x y))⟩)

/-- A six-cycle or a five-cycle forces the sixth path vertex when the radius
is at least three and the average neighborhood independence is above two. -/
theorem six_le_path_of_radius_ge_three (hc : G.Connected) (h4 : NoFourCycle G)
    (hr : 3 ≤ G.radius.toNat) (hav : 2 < l G) : 6 ≤ G.path := by
  by_contra! hp
  have hex (C : Ring G 6) (hC : C.Induced) : False := by
    rcases hexagon_radius_or_average hc h4 hp C hC with h | h
    · omega
    · exact hav.not_ge h
  obtain ⟨n,hn,C,hC⟩ := exists_induced_ring_of_two_le_l hc h4 hav.le
  by_cases h : 6 < n
  · exact hp.not_ge (C.path_bound hC h)
  rcases (show n = 5 ∨ n = 6 by omega) with rfl | rfl
  · rcases ring_five_trichotomy hc h4 C hC with h | h | ⟨D,hD⟩
    · omega
    · omega
    · exact hex D hD
  · exact hex C hC

theorem radius_add_three_le_path (hc : G.Connected) (h4 : NoFourCycle G) (hav : 2 < l G) :
    G.radius.toNat + 3 ≤ G.path := by
  have h5 := five_le_path_of_two_lt_l hc h4 hav
  by_cases h : 3 ≤ G.radius.toNat
  · have h6 := six_le_path_of_radius_ge_three hc h4 h hav
    have hchung := chung_bound_nat G hc
    omega
  · omega

/-- The floored conjecture holds on its entire range below average four. -/
theorem floored_of_floor_le_three (hc : G.Connected) (hk : ⌊l G⌋₊ ≤ 3) : FlooredConjecture G := by
  classical
  by_cases h4 : NoFourCycle G
  · apply (floored_iff_of_noFourCycle h4).2
    by_cases h3 : 3 ≤ ⌊l G⌋₊
    · have hreal : (3 : ℝ) ≤ l G := (Nat.le_floor_iff' (by decide : 3 ≠ 0)).mp h3
      have := radius_add_three_le_path hc h4 (by linarith)
      omega
    by_cases h2 : 2 ≤ ⌊l G⌋₊
    · have hreal : (2 : ℝ) ≤ l G := (Nat.le_floor_iff' (by decide : 2 ≠ 0)).mp h2
      have := radius_add_two_le_path_of_one_lt_l hc h4 (by linarith)
      omega
    · have := radius_add_one_le_path G hc
      omega
  · exact floored_of_fourCycle hc h4

/-- At girth at least six, the floored conjecture holds through radius four.
An even floor also covers radius five. -/
theorem floored_of_girth_six_small_radius (hc : G.Connected) (hg : 6 ≤ G.egirth)
    (hr : G.radius.toNat ≤ 4 ∨ G.radius.toNat ≤ 5 ∧ ⌊l G⌋₊ % 2 = 0) :
    FlooredConjecture G := by
  classical
  by_cases hk : ⌊l G⌋₊ ≤ 3
  · exact floored_of_floor_le_three hc hk
  by_cases h4 : NoFourCycle G
  · apply (floored_iff_of_noFourCycle h4).2
    have hav := sum_degree_ge_of_le_l (G := G) (Nat.floor_le (average_nonneg (G := G)))
    have bound := girth_six_density_path_bound hg (by omega : 4 ≤ ⌊l G⌋₊) hav
    omega
  · exact floored_of_fourCycle hc h4

/-- Conditions that any counterexample to the requested inequality must satisfy. -/
theorem necessary_for_counterexample (hc : G.Connected) (hbad : ¬ FlooredConjecture G) :
    NoFourCycle G ∧ 4 ≤ ⌊l G⌋₊ ∧ 2 ≤ G.radius.toNat ∧ G.radius.toNat ≤ ⌊l G⌋₊ ∧
    G.egirth < 7 ∧ (G.IsBipartite → 7 ≤ G.radius.toNat ∧ ¬ ∃ d, G.IsRegularOfDegree d) := by
  classical
  have h4 : NoFourCycle G := by_contra fun h => hbad (floored_of_fourCycle hc h)
  have hk : 4 ≤ ⌊l G⌋₊ := by
    by_contra! h
    exact hbad (floored_of_floor_le_three hc (by omega))
  have hp := (floored_iff_of_noFourCycle h4).not.mp hbad
  have hr : 2 ≤ G.radius.toNat := by
    by_contra! h
    by_cases h1 : G.radius.toNat = 1
    · have := l_lt_two_of_radius_one hc h4 h1
      have hl : (4 : ℝ) ≤ l G := (Nat.le_floor_iff' (by decide : 4 ≠ 0)).mp hk
      linarith
    · have hz : G.radius.toNat = 0 := by omega
      rcases ENat.toNat_eq_zero.mp hz with he | he
      · exact not_subsingleton _ (G.radius_eq_zero_iff.mp he).2
      · exact (G.radius_ne_top_iff.mpr hc) he
  refine ⟨h4,hk,hr,?_,?_,?_⟩
  · have := chung_bound_nat G hc
    omega
  · exact lt_of_not_ge fun h => hp (radius_add_floor_le_path_of_girth_seven h hc)
  · intro hb
    refine ⟨?_,?_⟩
    · by_contra! h
      exact hp (radius_add_floor_le_path_of_bipartite_radius_le_six hc hb h4 (by omega))
    · rintro ⟨d,hreg⟩
      have h := radius_add_l_le_path_of_regular_bipartite hc hb h4 hreg
      have hf := Nat.floor_le (average_nonneg (G := G))
      apply hp
      exact_mod_cast (show (G.radius.toNat : ℝ) + ⌊l G⌋₊ ≤ (G.path : ℝ) by linarith)

/-- At each vertex it suffices to have k independent neighbors or strictly
more than k neighbors, where k is the floor of the graph average. -/
theorem floored_of_local_threshold (hc : G.Connected)
    (hloc : ∀ v, ⌊l G⌋₊ ≤ G.indepNeighborsCard v ∨ ⌊l G⌋₊ < G.degree v) :
    FlooredConjecture G := by
  by_contra bad
  obtain ⟨h4,_,hr,_,_,_⟩ := necessary_for_counterexample hc bad
  exact bad ((floored_iff_of_noFourCycle h4).2 (radius_add_local_threshold_le_path hc h4
    (Nat.floor_le (average_nonneg (G := G))) hr hloc))

omit [Nontrivial V] in
/-- The floored conjecture holds for every connected regular graph. -/
theorem floored_of_regular (hc : G.Connected) {d : ℕ} (hreg : G.IsRegularOfDegree d) :
    FlooredConjecture G := by
  classical
  by_cases nontriv : Nontrivial V
  · let := nontriv
    exact floored_of_local_threshold hc (local_threshold_of_regular hreg (Nat.floor_le (average_nonneg (G := G))))
  · let : Subsingleton V := not_nontrivial_iff_subsingleton.mp nontriv
    apply floored_of_bipartite hc
    exact ⟨fun _ => (0 : Fin 2), fun {x y} h => False.elim (h.ne (Subsingleton.elim x y))⟩

/-- This includes graphs with odd cycles when their vertices of degree at
least three induce a bipartite graph. -/
theorem floored_of_bipartite_branch_vertices (hc : G.Connected)
    (h : (G.induce {x | 3 ≤ G.degree x}).IsBipartite) : FlooredConjecture G := by
  by_contra bad
  obtain ⟨h4,hk,_,_,_,_⟩ := necessary_for_counterexample hc bad
  exact bad ((floored_iff_of_noFourCycle h4).2
    (radius_add_floor_le_path_of_bipartite_branch_vertices hc h4 h hk))

theorem floored_of_girth_six_even (hc : G.Connected) (hg : 6 ≤ G.egirth)
    (he : ⌊l G⌋₊%2 = 0) : FlooredConjecture G := by
  classical
  by_cases h4 : NoFourCycle G
  · apply (floored_iff_of_noFourCycle h4).2
    have := radius_add_floor_le_path_girth_six_sharp hc hg
    omega
  · exact floored_of_fourCycle hc h4

/-- For girth at least six, the fifth floor band holds at every radius. -/
theorem floored_of_girth_six_five (hc : G.Connected) (hg : 6 ≤ G.egirth)
    (hk : ⌊l G⌋₊=5) : FlooredConjecture G := by
  have h4 := noFourCycle_of_girth_five (G:=G) (by exact le_trans (by decide : (5:ℕ∞)≤6) hg)
  apply (floored_iff_of_noFourCycle h4).2
  have hav := sum_degree_ge_of_le_l (G:=G) (Nat.floor_le (average_nonneg (G:=G)))
  rw [hk] at hav ⊢
  exact radius_add_five_density_le_path_girth_six hc hg hav

/-- Even in an irregular graph, if every edge belongs to a triangle the
floored lower bound holds to within one vertex. -/
theorem within_one_of_triangle_edges (hc : G.Connected) (h4 : NoFourCycle G)
    (tri : ∀ {u v},G.Adj u v → ∃ z,G.Adj u z ∧ G.Adj v z) :
    G.radius.toNat+⌊l G⌋₊ ≤ G.path+1 := by
  by_cases h : FlooredConjecture G
  · have := (floored_iff_of_noFourCycle h4).1 h
    omega
  obtain ⟨_,_,hr,_,_,_⟩ := necessary_for_counterexample hc h
  apply radius_add_half_density_le_path_add_one hc h4 hr
  simp_rw [← twice_indep_eq_degree_of_edges_in_triangles h4 tri,← Finset.mul_sum,Nat.mul_assoc]
  exact Nat.mul_le_mul_left 2 (le_average_iff_sum_indep.mp (Nat.floor_le (average_nonneg (G:=G))))

/-- Floors five and six satisfy the full bound through radius two. -/
theorem floored_of_five_or_six_at_radius_two (hc : G.Connected) (hr : G.radius.toNat≤2)
    (hk : ⌊l G⌋₊=5 ∨ ⌊l G⌋₊=6) : FlooredConjecture G := by
  by_cases h4 : NoFourCycle G
  · apply (floored_iff_of_noFourCycle h4).2
    have := half_floor_add_five_le_path h4 (show 5≤⌊l G⌋₊ by omega)
      (Nat.floor_le (average_nonneg (G:=G)))
    omega
  · exact floored_of_fourCycle hc h4

omit [Nontrivial V] in
/-- The first four floor bands hold at every radius, without restrictions
on triangles, five-cycles, or the degree sequence. -/
theorem floored_of_floor_le_four (hc : G.Connected) (hk : ⌊l G⌋₊ ≤ 4) : FlooredConjecture G := by
  by_contra bad
  have := nontrivial_of_counterexample hc bad
  apply bad
  by_cases low : ⌊l G⌋₊ ≤ 3
  · exact floored_of_floor_le_three hc low
  by_cases h4 : NoFourCycle G
  · apply (floored_iff_of_noFourCycle h4).2
    have av := (Nat.le_floor_iff' (a:=l G) (by decide : 4≠0)).mp (show 4≤⌊l G⌋₊ by omega)
    have := radius_add_four_le_path h4 hc av
    omega
  · exact floored_of_fourCycle hc h4

omit [Nontrivial V] in
/-- Every connected graph of diameter at most two satisfies the floored
conjecture, at any value of its average neighborhood independence. -/
theorem floored_of_diameter_le_two (hc : G.Connected) (diam : G.diam≤2) :
    FlooredConjecture G := by
  classical
  by_cases nontriv : Nontrivial V
  · let := nontriv
    by_cases low : ⌊l G⌋₊≤3
    · exact floored_of_floor_le_three hc low
    by_cases h4 : NoFourCycle G
    · apply (floored_iff_of_noFourCycle h4).2
      have rd : G.radius.toNat≤G.diam := ENat.toNat_le_toNat G.radius_le_ediam
        (G.connected_iff_ediam_ne_top.mp hc)
      have path := three_le_min_degree_add_two hc h4 (show 3≤⌊l G⌋₊ by omega)
        (floor_le_min_degree_of_diameter_two hc h4 diam)
      omega
    · exact floored_of_fourCycle hc h4
  · let : Subsingleton V := not_nontrivial_iff_subsingleton.mp nontriv
    exact floored_of_bipartite hc
      ⟨fun _ => (0 : Fin 2), fun {x y} h => False.elim (h.ne (Subsingleton.elim x y))⟩

/-- If every edge lies in a triangle, the full inequality holds through
radius three at every floor. -/
theorem floored_of_triangle_edges_radius_le_three (hc : G.Connected) (rad : G.radius.toNat≤3)
    (tri : ∀ {u v},G.Adj u v → ∃ z,G.Adj u z ∧ G.Adj v z) : FlooredConjecture G := by
  by_cases small : ⌊l G⌋₊≤3
  · exact floored_of_floor_le_three hc small
  by_cases h4 : NoFourCycle G
  · apply (floored_iff_of_noFourCycle h4).2
    have density : (2*⌊l G⌋₊)*Fintype.card V ≤ ∑ v,G.degree v := by
      simp_rw [← twice_indep_eq_degree_of_edges_in_triangles h4 tri,← Finset.mul_sum,Nat.mul_assoc]
      exact Nat.mul_le_mul_left 2 (le_average_iff_sum_indep.mp (Nat.floor_le (average_nonneg (G:=G))))
    have := half_degree_density_add_three h4 (show 4≤2*⌊l G⌋₊ by omega) density
    omega
  · exact floored_of_fourCycle hc h4

/-- If the floor is at most the minimum degree, a counterexample has equal
radius and diameter from three through seven, or radius three and diameter four. -/
theorem radius_and_diameter_of_min_degree_counterexample (hc : G.Connected)
    (bad : ¬FlooredConjecture G) (hmin : ∀ v,⌊l G⌋₊≤G.degree v) :
    (3≤G.radius.toNat ∧ G.radius.toNat=G.diam ∧ G.diam≤7) ∨
      (G.radius.toNat=3 ∧ G.diam=4) := by
  obtain ⟨h4,hk,_,hrk,_,_⟩ := necessary_for_counterexample hc bad
  have miss := (floored_iff_of_noFourCycle h4).not.mp bad
  have rd : G.radius.toNat ≤ G.diam := ENat.toNat_le_toNat G.radius_le_ediam
    (G.connected_iff_ediam_ne_top.mp hc)
  have minPath := three_le_min_degree_add_two hc h4 (show 3≤⌊l G⌋₊ by omega) hmin
  obtain ⟨a,b,eq⟩ := G.exists_dist_eq_diam
  obtain ⟨q,_,hq⟩ := hc.exists_path_of_dist a b
  have bounds := geodesic_degree_bounds_of_noFourCycle hc h4 q hq (by omega) hmin
  omega

/-- At floor five a single nonempty induced subgraph of girth at least six
and average degree at least five suffices at every ambient radius. -/
theorem floored_of_five_dense_girth_six_induce (hc : G.Connected) (hk : ⌊l G⌋₊=5)
    (S : Finset V) (hs : S.Nonempty) (hg : 6≤(G.induce (S:Set V)).egirth)
    (dense : 5*S.card ≤ ∑ v:S,(G.induce (S:Set V)).degree v) : FlooredConjecture G := by
  classical
  by_cases h4 : NoFourCycle G
  · apply (floored_iff_of_noFourCycle h4).2
    let H := G.induce (S:Set V)
    have : Nonempty S := hs.to_subtype
    have size : 5*Fintype.card S ≤ ∑ v:S,H.degree v := by simpa [H] using dense
    have ten := (ten_le_path_of_girth_six_density hg size).trans (G.path_induce_le (S:Set V))
    have chung := chung_bound_nat G hc
    omega
  · exact floored_of_fourCycle hc h4

omit [Nontrivial V] in
/-- When the floor is five the conjecture holds through radius three. -/
theorem floored_of_five_at_radius_le_three (hc : G.Connected) (rad : G.radius.toNat≤3)
    (hk : ⌊l G⌋₊=5) : FlooredConjecture G := by
  by_contra bad
  have := nontrivial_of_counterexample hc bad
  apply bad
  by_cases h4 : NoFourCycle G
  · apply (floored_iff_of_noFourCycle h4).2
    have avg := (Nat.le_floor_iff' (a:=l G) (by decide : 5≠0)).mp hk.ge
    rw [hk]
    exact radius_add_five_le_path_of_radius_le_three h4 rad avg
  · exact floored_of_fourCycle hc h4

omit [Fintype V] [DecidableEq V] [Nontrivial V] [DecidableRel G.Adj] in
private theorem girth_three_or_five (h4 : NoFourCycle G) (low : G.egirth<6) :
    G.egirth=3 ∨ G.egirth=5 := by
  obtain ⟨a,p,cycle,eq⟩ := exists_egirth_eq_length (G:=G) |>.2 (fun ac => by
    rw [ac.egirth_eq_top] at low
    exact (not_lt_of_ge le_top) low)
  have lo := cycle.three_le_length
  have hi : p.length<6 := by rw [eq] at low; exact_mod_cast low
  have ne : p.length≠4 := by
    intro len
    have diff (i j : ℕ) (si : i<4) (sj : j<4) (d : i≠j) : p.getVert i≠p.getVert j :=
      fun e => d (cycle.getVert_injOn' (by omega : i≤p.length-1) (by omega : j≤p.length-1) e)
    have close : p.getVert 4=p.getVert 0 := by rw [←len,Walk.getVert_length,Walk.getVert_zero]
    have e30 := p.adj_getVert_succ (i:=3) (by omega)
    change G.Adj (p.getVert 3) (p.getVert 4) at e30
    rw [close] at e30
    exact diff 1 3 (by decide) (by decide) (by decide)
      (h4 (diff 0 2 (by decide) (by decide) (by decide))
        (p.adj_getVert_succ (i:=0) (by omega)) (p.adj_getVert_succ (i:=1) (by omega)).symm
        e30.symm (p.adj_getVert_succ (i:=2) (by omega)))
  rcases (show p.length=3 ∨ p.length=5 by omega) with h|h
  · left; simp [eq,h]
  · right; simp [eq,h]

/-- At floor five every potential failure has short girth and misses the
claimed inequality by precisely one vertex. -/
theorem fifth_floor_counterexample (hc : G.Connected) (bad : ¬FlooredConjecture G)
    (hk : ⌊l G⌋₊=5) : NoFourCycle G ∧ 4≤G.radius.toNat ∧ G.radius.toNat≤5 ∧
      3≤G.diam ∧ G.egirth<6 ∧ G.path=G.radius.toNat+4 := by
  classical
  obtain ⟨h4,_,_,upper,_,_⟩ := necessary_for_counterexample hc bad
  have rad : 4≤G.radius.toNat := by
    by_contra! low
    exact bad (floored_of_five_at_radius_le_three hc (by omega) hk)
  have diam : 3≤G.diam := by by_contra! low; exact bad (floored_of_diameter_le_two hc (by omega))
  have girth : G.egirth<6 := lt_of_not_ge (fun six => bad (floored_of_girth_six_five hc six hk))
  have av := (Nat.le_floor_iff' (a:=l G) (by decide : 4≠0)).mp (show 4≤⌊l G⌋₊ by omega)
  have four := radius_add_four_le_path h4 hc av
  have miss := (floored_iff_of_noFourCycle h4).not.mp bad
  exact ⟨h4,rad,by omega,diam,girth,by omega⟩

/-- At floor five, only radii four and five and girths three and five
can still occur in a counterexample. -/
theorem remaining_fifth_band (hc : G.Connected) (bad : ¬FlooredConjecture G)
    (hk : ⌊l G⌋₊=5) : (G.radius.toNat=4 ∨ G.radius.toNat=5) ∧
      (G.egirth=3 ∨ G.egirth=5) ∧ G.path=G.radius.toNat+4 := by
  obtain ⟨h4,lo,hi,_,short,eq⟩ := fifth_floor_counterexample hc bad hk
  exact ⟨by omega,girth_three_or_five h4 short,eq⟩

/-- A remaining counterexample must have a locally deficient vertex, an
irregular degree sequence, and a nonbipartite graph on its branch vertices.
At girth six its floor is odd and at least seven, and it misses by one. -/
theorem restrictions_of_counterexample (hc : G.Connected) (bad : ¬FlooredConjecture G) :
    NoFourCycle G ∧ 5≤⌊l G⌋₊ ∧ 2≤G.radius.toNat ∧ G.radius.toNat≤⌊l G⌋₊ ∧ G.egirth<7 ∧
    (¬∃ d,G.IsRegularOfDegree d) ∧ ¬(G.induce {x | 3≤G.degree x}).IsBipartite ∧
    (∃ v,G.indepNeighborsCard v<⌊l G⌋₊ ∧ G.degree v≤⌊l G⌋₊) ∧
    (6≤G.egirth → 7≤⌊l G⌋₊ ∧ ⌊l G⌋₊%2=1 ∧ G.radius.toNat+⌊l G⌋₊=G.path+1) := by
  classical
  obtain ⟨h4,_,hr,hrk,hg,_⟩ := necessary_for_counterexample hc bad
  have five : 5≤⌊l G⌋₊ := by by_contra! h; exact bad (floored_of_floor_le_four hc (by omega))
  refine ⟨h4,five,hr,hrk,hg,fun ⟨_,reg⟩ => bad (floored_of_regular hc reg),
    fun bi => bad (floored_of_bipartite_branch_vertices hc bi),?_,?_⟩
  · by_contra! all
    exact bad (floored_of_local_threshold hc (fun v => by
      by_cases ok : ⌊l G⌋₊≤G.indepNeighborsCard v
      · exact Or.inl ok
      · exact Or.inr (all v (by omega))))
  · intro six
    have odd : ⌊l G⌋₊%2≠0 := fun even => bad (floored_of_girth_six_even hc six even)
    have notFive : ⌊l G⌋₊≠5 := fun eq => bad (floored_of_girth_six_five hc six eq)
    have close := radius_add_floor_le_path_girth_six_sharp hc six
    have missed := (floored_iff_of_noFourCycle h4).not.mp bad
    omega

/-- The square of the floor plus the radius is a lower bound on the
number of vertices in any counterexample. -/
theorem order_of_counterexample (hc : G.Connected) (bad : ¬FlooredConjecture G) :
    ⌊l G⌋₊^2+G.radius.toNat ≤ Fintype.card V := by
  obtain ⟨h4,_,hr,_,_,_,_,⟨v,defect,_⟩,_⟩ := restrictions_of_counterexample hc bad
  have := sq_add_radius_le_order_of_independence_defect hc h4
    (Nat.floor_le (average_nonneg (G:=G))) defect
  omega

/-- At radius at least four the order bound is strict. -/
theorem order_of_counterexample_radius_ge_four (hc : G.Connected) (bad : ¬FlooredConjecture G)
    (hr : 4≤G.radius.toNat) : ⌊l G⌋₊^2+G.radius.toNat+1 ≤ Fintype.card V := by
  obtain ⟨h4,hk,_,hrk,_,_,_,⟨v,low,_⟩,_⟩ := restrictions_of_counterexample hc bad
  exact sq_add_radius_add_one_le_order_of_independence_defect hc h4 hk hr hrk
    (Nat.floor_le (average_nonneg (G:=G))) low

omit [Nontrivial V] in
/-- Every connected graph on at most 29 vertices satisfies the conjecture. -/
theorem floored_of_order_le_29 (hc : G.Connected) (order : Fintype.card V≤29) :
    FlooredConjecture G := by
  by_contra bad
  have := nontrivial_of_counterexample hc bad
  have bound := order_of_counterexample hc bad
  obtain ⟨_,five,hr,_,_,_,_,_,_⟩ := restrictions_of_counterexample hc bad
  by_cases eq : ⌊l G⌋₊=5
  · have := (fifth_floor_counterexample hc bad eq).2.1
    have strict := order_of_counterexample_radius_ge_four hc bad this
    rw [eq] at strict
    omega
  · have sq := Nat.pow_le_pow_left (show 6≤⌊l G⌋₊ by omega) 2
    omega

/-- The fourth floor band holds through radius two. -/
theorem floored_of_four_at_small_radius (hc : G.Connected) (hr : G.radius.toNat ≤ 2)
    (hk : ⌊l G⌋₊ = 4) : FlooredConjecture G := by
  classical
  by_cases h4 : NoFourCycle G
  · exact (floored_iff_of_noFourCycle h4).2 (radius_two_floor_four h4 hr hk)
  · exact floored_of_fourCycle hc h4

/-- Any counterexample to the floored conjecture is nonbipartite, has no
four-cycle, and has girth less than seven. -/
theorem remaining_cases_of_counterexample (hc : G.Connected) (hbad : ¬FlooredConjecture G) :
    ¬G.IsBipartite ∧ NoFourCycle G ∧ 4 ≤ ⌊l G⌋₊ ∧
    2 ≤ G.radius.toNat ∧ G.radius.toNat ≤ ⌊l G⌋₊ ∧ G.egirth < 7 := by
  obtain ⟨h4,hk,hr,hrk,hg,_⟩ := necessary_for_counterexample hc hbad
  exact ⟨fun hb => hbad (floored_of_bipartite hc hb),h4,hk,hr,hrk,hg⟩

/-- A bipartite counterexample must have radius at least seven, miss the
claimed bound by one or two vertices, and have unequal degrees within
at least one color class of every proper two-coloring. -/
theorem bipartite_counterexample_restrictions (hc : G.Connected) (hb : G.IsBipartite)
    (hbad : ¬FlooredConjecture G) :
    7 ≤ G.radius.toNat ∧ G.radius.toNat ≤ ⌊l G⌋₊ ∧
    (G.radius.toNat+⌊l G⌋₊ = G.path+1 ∨ G.radius.toNat+⌊l G⌋₊ = G.path+2) ∧
    ∀ c : G.Coloring (Fin 2), ∃ u v, c u = c v ∧ G.degree u ≠ G.degree v := by
  obtain ⟨h4,_,_,hr,_,hbi⟩ := necessary_for_counterexample hc hbad
  have hp := (floored_iff_of_noFourCycle h4).not.mp hbad
  have ht := radius_add_floor_le_path_add_two_of_bipartite hc hb h4
  refine ⟨(hbi hb).1, hr, by omega, ?_⟩
  intro c
  by_contra! hall
  exact hp (radius_add_floor_le_path_of_constant_degree_on_parts hc c h4 hall)

/-- A counterexample at large radius needs two distinct vertices of degree at most two. It also
has no induced subgraph with average degree at least two larger than
the floor of the average in the whole graph. -/
theorem bipartite_counterexample_degree_bounds (hc : G.Connected) (hb : G.IsBipartite)
    (hbad : ¬FlooredConjecture G) :
    (17+3*(⌊l G⌋₊%2) ≤ G.radius.toNat → ∃ u v, u ≠ v ∧ G.degree u ≤ 2 ∧ G.degree v ≤ 2) ∧
    ∀ U : Finset V, U.Nonempty →
      ∑ v : U, (G.induce (U : Set V)).degree v < (⌊l G⌋₊+2)*U.card := by
  obtain ⟨h4,_,hr,_,_,_⟩ := necessary_for_counterexample hc hbad
  have hp := (floored_iff_of_noFourCycle h4).not.mp hbad
  constructor
  · intro hrad
    have low (e : V) : ∃ v, v ≠ e ∧ G.degree v ≤ 2 := by
      by_contra! hdeg
      exact hp (radius_add_floor_le_path_of_one_degree_exception hc hb h4 e (fun v hv => hdeg v hv) hrad)
    obtain ⟨u,_,hu⟩ := low (Classical.arbitrary V)
    obtain ⟨v,hne,hv⟩ := low u
    exact ⟨u,v,hne.symm,hu,hv⟩
  · intro U hU
    by_contra! h
    exact hp (radius_add_floor_le_path_of_dense_induce hc hb h4 U hU h hr)

end Wall133
