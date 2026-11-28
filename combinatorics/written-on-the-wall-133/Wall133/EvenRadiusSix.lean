module

public import Wall133.OddRadiusFive

@[expose] public section

namespace Wall133
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

/-- At every even density threshold at least six, a four-cycle-free bipartite
graph contains an induced path exceeding that threshold by at least six. -/
theorem add_six_le_path_of_even_bipartite_density [DecidableEq V] [Nonempty V]
    (hb : G.IsBipartite) (h4 : NoFourCycle G)
    {m : ℕ} (hm : 3 ≤ m) (hav : (2*m : ℕ) ≤ l G) : 2*m+6 ≤ path G := by
  classical
  have hdeg := sum_degree_ge_of_le_l hav
  have hh : 2 * (∑ _v : V, m) ≤ ∑ v, G.degree v := by
    simpa [Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_comm] using hdeg
  obtain ⟨S, hS, hmin, hsum⟩ := exists_weighted_degree_core G (fun _ => m) (by omega) hh
  have : Nonempty S := hS.to_subtype
  let H := G.induce (S : Set V)
  obtain ⟨c⟩ := hb
  let C : H.Coloring (Fin 2) := ⟨fun x => c x.val, fun h => c.map_rel h⟩
  have h4' : NoFourCycle H := by
    intro x y a b hxy hxa hya hxb hyb
    exact Subtype.ext (h4 (x := x.val) (y := y.val) (fun h => hxy (Subtype.ext h))
      hxa hya hxb hyb)
  have hhigh : ∃ v : S, 2*m ≤ H.degree v := by
    by_contra! h
    have hlt := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun v _ => h v)
    have hh : ∑ v : S, H.degree v < 2 * ∑ _v ∈ S, m := by
      simpa [Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_comm] using hlt
    exact hh.not_ge hsum
  obtain ⟨v, hv⟩ := hhigh
  have hp := two_mul_minDegree_add_four_of_high_vertex C h4' (d := m+1)
    (by omega) hmin v (by omega)
  have htransfer := G.path_induce_le (S : Set V)
  change path H ≤ _ at htransfer
  omega

/-- Radius six and even neighborhood-independence floor at least six. -/
theorem radius_add_floor_le_path_of_bipartite_radius_six_even
    [DecidableEq V] [Nonempty V] (hb : G.IsBipartite) (h4 : NoFourCycle G)
    (hr : G.radius.toNat ≤ 6) (hl : 6 ≤ ⌊l G⌋₊) (he : ⌊l G⌋₊ % 2 = 0) :
    G.radius.toNat + ⌊l G⌋₊ ≤ path G := by
  let k := ⌊l G⌋₊
  have eq : 2*(k/2) = k := by dsimp [k]; omega
  have hav : (k : ℝ) ≤ l G := Nat.floor_le (div_nonneg
    (Finset.sum_nonneg (fun v _ => Nat.cast_nonneg (G.indepNeighborsCard v))) (Nat.cast_nonneg _))
  have hp := add_six_le_path_of_even_bipartite_density hb h4 (m := k/2)
    (by dsimp [k]; omega) (by rwa [eq])
  change _ + k ≤ _
  omega

end Wall133
