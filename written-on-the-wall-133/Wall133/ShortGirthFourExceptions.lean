module

public import Wall133.ShortGirthExceptions
public import Wall133.ShortGirthFour
public import Wall133.RegularAll

@[expose] public section

namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In the fourth band, the threshold is local to the neighborhood of a single
high vertex. Two nonadjacent neighbors cannot both fail it. -/
theorem radius_add_four_of_local_neighbors (hc : G.Connected) (h4 : NoFourCycle G)
    (hav : (4 : ℝ)≤l G)
    (start : ∀ a,2≤G.indepNeighborsCard a ∨ 3≤G.degree a)
    (v : V) (hv : 4 ≤ G.indepNeighborsCard v)
    (nb : ∀ x y,G.Adj v x → G.Adj v y → x≠y → ¬G.Adj x y →
      (4≤G.indepNeighborsCard x ∨ 5≤G.degree x) ∨ (4≤G.indepNeighborsCard y ∨ 5≤G.degree y)) :
    G.radius.toNat+4 ≤ G.path := by
  by_cases hr : G.radius.toNat≤2
  · have := half_floor_add_four_le_path h4 (le_refl 4) hav; omega
  obtain ⟨a,q,hq,hlen⟩ := exists_geodesic_ge_radius G hc v
  have geom : q.reverse.length=G.dist a v := by simpa [G.dist_comm (u := a)] using hq
  have len : q.reverse.length=q.length := q.length_reverse
  have bound := geodesic_add_threshold_of_local_ends h4 hc q.reverse geom (by omega) hv
    (by have := start a; omega)
    (fun u hoff hdist => by
      have zu : G.dist a u = 0 := by omega
      have eu := ((G.dist_eq_zero_iff_eq_or_not_reachable).mp zu).resolve_right (not_not_intro (hc a u))
      subst u
      exact (hoff q.reverse.start_mem_support).elim)
    (fun x y hx hy _ _ hxy na => nb x y hx hy hxy na)
  omega

/-- In particular, arbitrary vertices may have degree below four, provided
every vertex has degree at least three and at most one vertex fails the
local fourth-band threshold. -/
theorem radius_add_four_of_one_exception (hc : G.Connected) (h4 : NoFourCycle G)
    (hav : (4:ℝ)≤l G) (hmin : ∀ v,3≤G.degree v) (e : V)
    (outside : ∀ w,w≠e → 4≤G.indepNeighborsCard w ∨ 5≤G.degree w) :
    G.radius.toNat+4 ≤ G.path := by
  obtain ⟨v,hv⟩ := exists_large_indep_neighbors (k:=4) hav
  apply radius_add_four_of_local_neighbors hc h4 hav (fun a => Or.inr (hmin a)) v hv
  intro x y _ _ hxy _
  by_cases h : x=e
  · exact Or.inr (outside y (fun he => hxy (h.trans he.symm)))
  · exact Or.inl (outside x h)

end Wall133
