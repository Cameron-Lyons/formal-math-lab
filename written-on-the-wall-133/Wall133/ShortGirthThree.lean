import Wall133.ShortGirthThreeEdges
import Wall133.ShortGirthSimplicial
import Wall133.ShortGirthFour

namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At radius at least three, average neighborhood independence at least four
forces an induced path on seven vertices. -/
theorem seven_le_path_of_four_le_average (h4 : NoFourCycle G) (hc : G.Connected)
    (hr : 3 ≤ G.radius.toNat) (hav : (4:ℝ) ≤ l G) : 7 ≤ G.path := by
  obtain ⟨S,v,⟨star⟩,core⟩ := exists_four_core_star h4 hav
  obtain ⟨a,q,hq,hl⟩ := exists_geodesic_ge_radius G hc v
  let P : Chain G 3 := ⟨q.getVert,fun {i j} hi hj e =>
    (q.isPath_of_length_eq_dist hq).getVert_injOn (by omega : i≤q.length) (by omega : j≤q.length) e,
    fun {i j} hi hj => adj_getVert_iff_consecutive_of_length_eq_dist q hq (by omega : i≤q.length) (by omega : j≤q.length)⟩
  have geo (i) (hi : i≤3) : G.dist (P.vertex 0) (P.vertex i)=i := by
    change G.dist (q.getVert 0) (q.getVert i)=i
    simpa using dist_getVert_eq_sub_of_le_of_length_eq_dist q hq (Nat.zero_le i) (by omega : i≤q.length)
  have root : P.vertex 0=v := by simp [P]
  have atP : IndependentCoreStar G S (P.vertex 0) 4 := root ▸ star
  by_cases simp : ∀ z,G.Adj z (P.vertex 3) → z≠P.vertex 2 → G.Adj z (P.vertex 2)
  · exact seven_of_simplicial_end P h4 hc geo S atP core simp
  push Not at simp
  obtain ⟨z,hz,ne,na⟩ := simp
  exact seven_of_nonsimplicial_end P h4 hc geo S atP core hz ne na

theorem radius_add_four_le_path_of_radius_le_three (h4 : NoFourCycle G) (hc : G.Connected)
    (hr : G.radius.toNat≤3) (hav : (4:ℝ)≤l G) : G.radius.toNat+4≤G.path := by
  by_cases h : 3≤G.radius.toNat
  · have := seven_le_path_of_four_le_average h4 hc h hav
    omega
  · have := half_floor_add_four_le_path h4 (le_refl 4) hav
    omega

end Wall133
