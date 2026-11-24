import Wall133.OddRadiusFive

namespace Wall133
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem odd_density_path (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    {m : ℕ} (hm : 2 ≤ m) (hdeg : (2*m+1)*Fintype.card V ≤ ∑ v, G.degree v) :
    2*m+6 ≤ path G := by
  classical
  obtain ⟨a,S,hS,hmin,hsum⟩ := exists_odd_degree_core_with_density c (by omega : 0 < m) hdeg
  let H := G.induce (S : Set V)
  let C : H.Coloring (Fin 2) := ⟨fun v => c v.val, fun h => c.map_rel h⟩
  have : Nonempty S := hS.to_subtype
  have h4' : NoFourCycle H := by
    intro x y u v hxy hxu hyu hxv hyv
    exact Subtype.ext (h4 (x := x.val) (y := y.val) (fun h => hxy (Subtype.ext h)) hxu hyu hxv hyv)
  have hP : 2*(m+1)+4 ≤ path H := by
    rcases odd_core_path_or_high C a h4' hm hmin hsum with hp | ⟨v,hc,hv⟩
    · exact hp
    · have base (x : S) : m+1 ≤ H.degree x := (Nat.le_add_right _ _).trans (hmin x)
      have side (x : S) (hx : C x = C v) : (m+1)+1 ≤ H.degree x := by
        have he : c x.val = a := hx.trans hc
        simpa [he] using hmin x
      exact odd_path_of_high_vertex C h4' (by omega) base v hv side
  have ht := G.path_induce_le (S : Set V)
  change path H ≤ _ at ht
  omega

/-- For any even or odd threshold k ≥ 5, a bipartite four-cycle-free graph
of average neighborhood independence at least k has an induced path on k+5 vertices. -/
theorem add_five_le_path_of_bipartite_density (hb : G.IsBipartite) (h4 : NoFourCycle G)
    {k : ℕ} (hk : 5 ≤ k) (hav : (k : ℝ) ≤ l G) : k+5 ≤ path G := by
  rcases Nat.mod_two_eq_zero_or_one k with he | ho
  · have heq : 2*(k/2) = k := by omega
    have hp := add_five_le_path_of_even_bipartite_density hb h4 (m := k/2) (by omega) (by rwa [heq])
    omega
  · have heq : 2*(k/2)+1 = k := by omega
    have hdeg := sum_degree_ge_of_le_l hav
    obtain ⟨c⟩ := hb
    have hp := odd_density_path c h4 (m := k/2) (by omega) (by rwa [heq])
    omega

/-- WOWII 133 for every connected bipartite graph without four-cycles whose
radius is at most five, including graphs of irregular degrees on either side. -/
theorem radius_add_floor_le_path_of_bipartite_radius_le_five [Nontrivial V]
    (hc : G.Connected) (hb : G.IsBipartite) (h4 : NoFourCycle G)
    (hr : G.radius.toNat ≤ 5) : G.radius.toNat + ⌊l G⌋₊ ≤ path G := by
  by_cases hsmall : G.radius.toNat ≤ 4
  · exact radius_add_floor_le_path_of_bipartite_radius_le_four hc hb h4 hsmall
  by_cases hk : 5 ≤ ⌊l G⌋₊
  · have hav := Nat.floor_le (show 0 ≤ l G from div_nonneg
      (Finset.sum_nonneg (fun v _ => Nat.cast_nonneg (G.indepNeighborsCard v))) (Nat.cast_nonneg _))
    have := add_five_le_path_of_bipartite_density hb h4 hk hav
    omega
  · have := chung_bound_nat G hc
    omega

end Wall133
