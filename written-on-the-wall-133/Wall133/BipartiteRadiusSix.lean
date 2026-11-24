import Wall133.BipartiteRadiusFive
import Wall133.EvenRadiusSix
import Wall133.OddRadiusSix

namespace Wall133
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At every integer density threshold at least six there is an induced
path on at least six more vertices than the threshold. -/
theorem add_six_le_path_of_bipartite_density (hb : G.IsBipartite) (h4 : NoFourCycle G)
    {k : ℕ} (hk : 6 ≤ k) (hav : (k : ℝ) ≤ l G) : k+6 ≤ G.path := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · have he : 2*(k/2) = k := by omega
    have := add_six_le_path_of_even_bipartite_density hb h4 (m := k/2) (by omega) (by rwa [he])
    omega
  · have he : 2*(k/2)+1 = k := by omega
    have := add_six_le_path_of_odd_bipartite_density hb h4 (m := k/2) (by omega) (by rwa [he])
    omega

/-- The floored inequality holds on every connected four-cycle-free
bipartite graph of radius at most six. -/
theorem radius_add_floor_le_path_of_bipartite_radius_le_six
    (hc : G.Connected) (hb : G.IsBipartite) (h4 : NoFourCycle G)
    (hr : G.radius.toNat ≤ 6) : G.radius.toNat+⌊l G⌋₊ ≤ G.path := by
  by_cases hnt : Nontrivial V
  · have : Nontrivial V := hnt
    by_cases hsmall : G.radius.toNat ≤ 5
    · exact radius_add_floor_le_path_of_bipartite_radius_le_five hc hb h4 hsmall
    by_cases hk : 6 ≤ ⌊l G⌋₊
    · have hav := Nat.floor_le (show 0 ≤ l G from div_nonneg
        (Finset.sum_nonneg (fun v _ => Nat.cast_nonneg (G.indepNeighborsCard v))) (Nat.cast_nonneg _))
      have := add_six_le_path_of_bipartite_density hb h4 hk hav
      omega
    · have := chung_bound_nat G hc
      omega
  · have : Subsingleton V := not_nontrivial_iff_subsingleton.mp hnt
    have hf : ⌊l G⌋₊ = 0 := by
      by_contra! h
      have hh := sum_degree_ge_of_le_l (G := G)
        ((Nat.le_floor_iff' (by decide : (1 : ℕ) ≠ 0)).mp (show 1 ≤ ⌊l G⌋₊ by omega))
      simp at hh
    have := radius_add_one_le_path G hc
    omega

end Wall133
