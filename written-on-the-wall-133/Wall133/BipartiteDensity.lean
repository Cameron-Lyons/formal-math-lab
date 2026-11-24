import Wall133.Bipartite
import Wall133.Density
import Wall133.FirstBands

namespace Wall133
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [Nonempty V] [DecidableRel G.Adj] in
private theorem noFourCycle_induce (S : Finset V) (h4 : NoFourCycle G) :
    NoFourCycle (G.induce (S : Set V)) := by
  intro x y a b hxy hxa hya hxb hyb
  apply Subtype.ext
  exact h4 (x := x.val) (y := y.val) (fun h => hxy (Subtype.ext h)) hxa hya hxb hyb

private def inducedColoring (S : Finset V) (c : G.Coloring (Fin 2)) :
    (G.induce (S : Set V)).Coloring (Fin 2) where
  toFun v := c v.val
  map_rel' := fun h => c.map_rel h

private theorem even_band_le_path (hb : G.IsBipartite) (h4 : NoFourCycle G)
    {m : ℕ} (hm : 2 ≤ m) (hdeg : (2*m)*Fintype.card V ≤ ∑ v, G.degree v) :
    2*m+4 ≤ path G := by
  classical
  have hh : 2 * (∑ _v : V, m) ≤ ∑ v, G.degree v := by
    simpa [Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_comm] using hdeg
  obtain ⟨S, hS, hmin, hsum⟩ := exists_weighted_degree_core G (fun _ => m) (by omega) hh
  have : Nonempty S := hS.to_subtype
  let H := G.induce (S : Set V)
  have hhigh : ∃ v : S, 2*m ≤ H.degree v := by
    by_contra! h
    have hlt := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun v _ => h v)
    have hh : ∑ v : S, H.degree v < 2 * ∑ _v ∈ S, m := by
      simpa [Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_comm] using hlt
    exact hh.not_ge hsum
  obtain ⟨v, hv⟩ := hhigh
  obtain ⟨c⟩ := hb
  have hp := two_mul_minDegree_add_two_le_path (G := H) ⟨inducedColoring S c⟩
    (noFourCycle_induce S h4) (d := m+1) (by omega) hmin v (by omega)
  have htransfer := G.path_induce_le (S : Set V)
  change path H ≤ _ at htransfer
  omega

private theorem odd_band_le_path (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    {m : ℕ} (hm : 0 < m) (hdeg : (2*m+1)*Fintype.card V ≤ ∑ v, G.degree v) :
    2*m+5 ≤ path G := by
  classical
  obtain ⟨a, S, hS, hmin⟩ := exists_odd_degree_core (G := G) c hm hdeg
  let H := G.induce (S : Set V)
  let C := inducedColoring S c
  have hbase (v : S) : m+1 ≤ H.degree v := (Nat.le_add_right _ _).trans (hmin v)
  have ha : ∃ v : S, c v.val = a := by
    obtain ⟨v, hv⟩ := hS
    let u : S := ⟨v, hv⟩
    by_cases hcolor : c u.val = a
    · exact ⟨u, hcolor⟩
    have hne : (H.neighborFinset u).Nonempty := Finset.card_pos.mp (by
      rw [H.card_neighborFinset_eq_degree]
      have := hbase u
      omega)
    obtain ⟨w, hw⟩ := hne
    have hdiff : c u.val ≠ c w.val := C.valid ((H.mem_neighborFinset _ _).mp hw)
    refine ⟨w, Fin.ext ?_⟩
    have := (c u.val).isLt
    have := (c w.val).isLt
    have := a.isLt
    have := Fin.val_ne_of_ne hdiff
    have := Fin.val_ne_of_ne hcolor
    omega
  obtain ⟨v, hv⟩ := ha
  have hhigh (x : S) (hx : C x = C v) : m+1 < H.degree x := by
    change c x.val = c v.val at hx
    have := hmin x
    simpa [hx.trans hv] using this
  have hp := two_mul_minDegree_add_three_le_path C (noFourCycle_induce S h4)
    (d := m+1) (by omega) hbase v hhigh
  have htransfer := G.path_induce_le (S : Set V)
  change 2*(m+1)+3 ≤ path H at hp
  change path H ≤ _ at htransfer
  omega

/-- Every four-cycle-free bipartite graph whose average neighborhood independence
is at least `k ≥ 3` has an induced path on at least `k + 4` vertices. -/
theorem add_four_le_path_of_bipartite_density (hb : G.IsBipartite) (h4 : NoFourCycle G)
    {k : ℕ} (hk : 3 ≤ k) (hav : (k : ℝ) ≤ l G) : k+4 ≤ path G := by
  have hdeg := sum_degree_ge_of_le_l hav
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · have he : 2*(k/2) = k := by omega
    have hp := even_band_le_path hb h4 (m := k/2) (by omega) (by rwa [he])
    omega
  · have he : 2*(k/2)+1 = k := by omega
    obtain ⟨c⟩ := hb
    have hp := odd_band_le_path c h4 (m := k/2) (by omega) (by rwa [he])
    omega

/-- The floored WOWII 133 inequality holds on every connected four-cycle-free
bipartite graph of radius at most four. -/
theorem radius_add_floor_le_path_of_bipartite_radius_le_four [Nontrivial V]
    (hc : G.Connected) (hb : G.IsBipartite) (h4 : NoFourCycle G)
    (hr : G.radius.toNat ≤ 4) : G.radius.toNat + ⌊l G⌋₊ ≤ path G := by
  let k := ⌊l G⌋₊
  change G.radius.toNat + k ≤ _
  by_cases hk : 3 ≤ k
  · have hp := add_four_le_path_of_bipartite_density hb h4 hk
      (Nat.floor_le (by
        unfold l averageIndepNeighbors
        apply div_nonneg
        · apply Finset.sum_nonneg; intro v _; exact Nat.cast_nonneg _
        · positivity))
    omega
  · by_cases hk' : 2 ≤ k
    · have hav : 1 < l G := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
        ((Nat.le_floor_iff' (by norm_num : (2 : ℕ) ≠ 0)).mp hk')
      have hp := radius_add_two_le_path_of_one_lt_l hc h4 hav
      omega
    · have hp := radius_add_one_le_path G hc
      omega

end Wall133
