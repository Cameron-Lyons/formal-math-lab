module

public import Wall133.ShortGirthCore
public import Wall133.IndependenceCore

@[expose] public section

namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Neighborhood independence averaging at least k gives an induced path on
at least k/2+4 vertices, also for irregular graphs containing triangles. -/
theorem half_floor_add_four_le_path (h4 : NoFourCycle G) {k : ℕ} (hk : 4≤k) (hav : (k:ℝ)≤l G) :
    k/2+4 ≤ G.path := by
  classical
  obtain ⟨S,hS,hmin,hsum⟩ := exists_independence_core h4 (by omega) hav
  let H := G.induce (S : Set V)
  have hg : NoFourCycle H := by
    intro x y a b hxy hxa hya hxb hyb
    exact Subtype.ext (h4 (x := x.val) (y := y.val) (fun h => hxy (Subtype.ext h)) hxa hya hxb hyb)
  have high : ∃ a : S, k/2+1 < H.indepNeighborsCard a := by
    by_contra! h
    have u := Finset.sum_le_sum (s := Finset.univ) (fun (v : S) _ => h v)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul] at u
    change k*S.card ≤ ∑ v:S,H.indepNeighborsCard v at hsum
    have hl := Nat.mul_lt_mul_of_pos_right (show k/2+1<k by omega) hS.card_pos
    rw [Nat.mul_comm (k/2+1)] at hl
    change (∑ v:S,H.indepNeighborsCard v) ≤ S.card*(k/2+1) at u
    omega
  obtain ⟨a,ha⟩ := high
  have hp := min_neighborhood_independence_path_bound (G := H) hg (by omega) hmin a
  rw [ite_eq_left ha] at hp
  have mono : H.path ≤ G.path := G.path_induce_le (S : Set V)
  omega

/-- At radius two the fourth floor band holds for every four-cycle-free graph. -/
theorem radius_two_floor_four (h4 : NoFourCycle G) (hr : G.radius.toNat≤2) (hk : ⌊l G⌋₊=4) :
    G.radius.toNat+⌊l G⌋₊ ≤ G.path := by
  have av := (Nat.le_floor_iff' (a := l G) (by decide : 4≠0)).mp (show 4≤⌊l G⌋₊ by omega)
  have := half_floor_add_four_le_path h4 (le_refl 4) av
  omega

end Wall133
