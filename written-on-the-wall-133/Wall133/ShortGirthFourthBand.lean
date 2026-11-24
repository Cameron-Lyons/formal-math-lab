import Wall133.ShortGirthFourEdges
import Wall133.ShortGirthSimplicialFour
import Wall133.ShortGirthThree

namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Nonempty V] in
/-- A vertex with four independent neighbors in a core of minimum
neighborhood independence three forces an induced path on eight vertices
as soon as some vertex of the graph is at distance four or more. -/
theorem eight_of_distant_core_star (h4 : NoFourCycle G) (hc : G.Connected)
    {S : Set V} {v a : V} (star : IndependentCoreStar G S v 4)
    (core : ∀ x∈S, Nonempty (IndependentCoreStar G S x 3))
    (far : 4 ≤ G.dist v a) : 8 ≤ G.path := by
  obtain ⟨q,_,hq⟩ := hc.exists_path_of_dist v a
  let P : Chain G 4 := ⟨q.getVert,fun {i j} hi hj e =>
    (q.isPath_of_length_eq_dist hq).getVert_injOn (by omega : i≤q.length) (by omega : j≤q.length) e,
    fun {i j} hi hj => adj_getVert_iff_consecutive_of_length_eq_dist q hq (by omega : i≤q.length) (by omega : j≤q.length)⟩
  have geo (i) (hi : i≤4) : G.dist (P.vertex 0) (P.vertex i)=i := by
    change G.dist (q.getVert 0) (q.getVert i)=i
    simpa using dist_getVert_eq_sub_of_le_of_length_eq_dist q hq (Nat.zero_le i) (by omega : i≤q.length)
  have root : P.vertex 0=v := by simp [P]
  have atP : IndependentCoreStar G S (P.vertex 0) 4 := root ▸ star
  by_cases simp : ∀ z,G.Adj z (P.vertex 4) → z≠P.vertex 3 → G.Adj z (P.vertex 3)
  · exact eight_of_simplicial_end P h4 hc geo S atP core simp
  push Not at simp
  obtain ⟨z,hz,ne,na⟩ := simp
  exact eight_of_nonsimplicial_end P h4 hc geo S atP core hz ne na

/-- At radius at least four, average neighborhood independence at least four
forces an induced path on eight vertices. -/
theorem eight_le_path_of_four_le_average (h4 : NoFourCycle G) (hc : G.Connected)
    (hr : 4 ≤ G.radius.toNat) (hav : (4:ℝ) ≤ l G) : 8 ≤ G.path := by
  obtain ⟨S,v,⟨star⟩,core⟩ := exists_four_core_star h4 hav
  obtain ⟨a,q,hq,hl⟩ := exists_geodesic_ge_radius G hc v
  exact eight_of_distant_core_star h4 hc star core (a:=a) (by omega)

/-- The fourth floor band of the conjecture at every radius. -/
theorem radius_add_four_le_path [Nontrivial V] (h4 : NoFourCycle G) (hc : G.Connected)
    (hav : (4:ℝ)≤l G) : G.radius.toNat+4≤G.path := by
  by_cases h : G.radius.toNat≤3
  · exact radius_add_four_le_path_of_radius_le_three h4 hc h hav
  have eight := eight_le_path_of_four_le_average h4 hc (by omega) hav
  have chung := chung_bound_nat G hc
  omega

end Wall133
