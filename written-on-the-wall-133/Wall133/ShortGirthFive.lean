module

public import Wall133.ShortGirthRooted
public import Wall133.IndependenceCore

@[expose] public section

namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Neighborhood independence averaging at least k gives an induced path on
at least k/2+5 vertices, also for irregular graphs containing triangles. -/
theorem half_floor_add_five_le_path (h4 : NoFourCycle G) {k : ℕ} (hk : 5≤k) (hav : (k:ℝ)≤l G) :
    k/2+5 ≤ G.path := by
  classical
  obtain ⟨S,hS,hmin,hsum⟩ := exists_independence_core h4 (by omega) hav
  let H := G.induce (S : Set V)
  have hg : NoFourCycle H := by
    intro x y a b hxy hxa hya hxb hyb
    exact Subtype.ext (h4 (x := x.val) (y := y.val) (fun h => hxy (Subtype.ext h)) hxa hya hxb hyb)
  have high : ∃ a : S, k ≤ H.indepNeighborsCard a := by
    by_contra! h
    have u := Finset.sum_lt_sum_of_nonempty (s:=(Finset.univ : Finset S))
      (by have := hS.to_subtype; exact Finset.univ_nonempty) (fun v _ => h v)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul] at u
    change (∑ v:S,H.indepNeighborsCard v) < S.card*k at u
    change k*S.card ≤ ∑ v:S,H.indepNeighborsCard v at hsum
    rw [Nat.mul_comm k] at hsum
    omega
  obtain ⟨a,ha⟩ := high
  have hp := min_neighborhood_independence_add_four (G := H) hg (by omega) hmin a (by omega)
  have mono : H.path ≤ G.path := G.path_induce_le (S : Set V)
  omega

/-- At radius two the fifth floor band holds for every four-cycle-free graph. -/
theorem radius_two_floor_five (h4 : NoFourCycle G) (hr : G.radius.toNat≤2) (hk : ⌊l G⌋₊=5) :
    G.radius.toNat+⌊l G⌋₊ ≤ G.path := by
  have av := (Nat.le_floor_iff' (a := l G) (by decide : 5≠0)).mp (show 5≤⌊l G⌋₊ by omega)
  have := half_floor_add_five_le_path h4 (le_refl 5) av
  omega

end Wall133
