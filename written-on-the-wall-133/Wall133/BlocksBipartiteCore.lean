module

public import Wall133.BipartiteAll
public import Wall133.LeafPruning

@[expose] public section

/-! # Transferring the bipartite bound to a graph with odd cycles -/

namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
/-- When every omitted vertex sees both color classes of the retained graph,
its distance to a retained center is at most the radius of the retained graph. -/
theorem radius_le_of_neighbors_in_both_colors (hc : G.Connected) (S : Finset V)
    (hcH : (G.induce (S : Set V)).Connected) (c : (G.induce (S : Set V)).Coloring (Fin 2))
    (both : ∀ z ∉ S, ∃ a b : S, c a ≠ c b ∧ G.Adj z a.val ∧ G.Adj z b.val) :
    G.radius.toNat ≤ (G.induce (S : Set V)).radius.toNat := by
  classical
  let H := G.induce (S : Set V)
  let : Nonempty S := hcH.nonempty
  obtain ⟨u,hu⟩ := H.exists_eccent_eq_radius
  obtain ⟨z,p,hp,hr⟩ := exists_geodesic_ge_radius G hc u.val
  have hbound (w : S) : G.dist u.val w.val ≤ H.dist u w :=
    dist_val_le_dist_induce _ hcH u w
  have hrH (w : S) : H.dist u w ≤ H.radius.toNat :=
    dist_le_radius_toNat_of_eccent_eq_radius hcH hu w
  by_cases hz : z ∈ S
  · exact (hr.trans_eq hp).trans ((hbound ⟨z,hz⟩).trans (hrH ⟨z,hz⟩))
  · obtain ⟨a,b,hab,ha,hb⟩ := both z hz
    have hdiff := dist_ne_of_color_ne hcH c (v := u) hab
    rw [H.dist_comm (u := a) (v := u), H.dist_comm (u := b) (v := u)] at hdiff
    have tri (w : S) (hw : G.Adj w.val z) : G.dist u.val z ≤ H.dist u w + 1 := by
      have ht := hc.dist_triangle (u := u.val) (v := w.val) (w := z)
      rw [dist_eq_one_iff_adj.mpr hw] at ht
      exact ht.trans (Nat.add_le_add_right (hbound w) _)
    have := tri a ha.symm
    have := tri b hb.symm
    have := hrH a
    have := hrH b
    change G.radius.toNat ≤ H.radius.toNat
    omega

/-- Each omitted vertex deletes at most twice its degree from the total
degree, counting the ends of all deleted edges. -/
theorem sum_degree_le_induced_add_twice_outside (S : Finset V) :
    (∑ x, G.degree x) ≤ (∑ x : S, (G.induce (S : Set V)).degree x) +
      2 * ∑ x ∈ Sᶜ, G.degree x := by
  classical
  let H := G.induce (S : Set V)
  let edge (v w : V) : ℕ := if G.Adj v w then 1 else 0
  have eqdeg (v : V) : (∑ w, edge v w) = G.degree v := by
    rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]
    simp [edge, Finset.sum_boole]
  have inner (v : S) : (∑ w ∈ S, edge v.val w) = H.degree v := by
    rw [← Finset.sum_attach, ← H.card_neighborFinset_eq_degree, H.neighborFinset_eq_filter]
    change (∑ w : S, if H.Adj v w then 1 else 0) = _
    exact Finset.sum_boole (R := ℕ) (fun w : S => H.Adj v w) Finset.univ
  have split (v : S) : G.degree v.val = H.degree v + ∑ w ∈ Sᶜ, edge v.val w := by
    rw [← inner, ←eqdeg, Finset.sum_add_sum_compl]
  have cross : (∑ v : S, ∑ w ∈ Sᶜ, edge v.val w) ≤ ∑ w ∈ Sᶜ, G.degree w := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro w _
    rw [←eqdeg, Finset.univ_eq_attach S, Finset.sum_attach S (fun x => edge x w)]
    simp_rw [show ∀ x, edge x w = edge w x from fun x => by simp [edge, G.adj_comm x w]]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    · intro _ _ _
      omega
  have total := Finset.sum_add_sum_compl S (fun v => G.degree v)
  rw [←Finset.sum_attach S, Finset.sum_congr rfl (fun u _ => split u),
    Finset.sum_add_distrib] at total
  rw [Finset.attach_eq_univ] at total
  change (∑ x, G.degree x) ≤ (∑ x : S, H.degree x) + _
  omega

/-- A connected induced bipartite graph supplies the full bound when its
average degree reaches the ambient threshold and each outside vertex has
neighbors in both of its color classes. -/
theorem radius_add_threshold_le_path_of_dense_bipartite_core (hc : G.Connected) (h4 : NoFourCycle G)
    (S : Finset V) (hcH : (G.induce (S : Set V)).Connected)
    (c : (G.induce (S : Set V)).Coloring (Fin 2))
    (both : ∀ z ∉ S, ∃ a b : S, c a ≠ c b ∧ G.Adj z a.val ∧ G.Adj z b.val)
    {k : ℕ} (hd : k * Fintype.card S ≤ ∑ u : S, (G.induce (S : Set V)).degree u) :
    G.radius.toNat + k ≤ G.path := by
  classical
  let H := G.induce (S : Set V)
  let : Nonempty S := hcH.nonempty
  have hf : k ≤ ⌊l H⌋₊ := Nat.le_floor (le_l_of_sum_degree c (k := k) (by
    convert hd using 1))
  have h4H : NoFourCycle H := fun _ _ _ _ hne ha hb hc hd =>
    Subtype.ext (h4 (fun he => hne (Subtype.ext he)) ha hb hc hd)
  have hp := radius_add_floor_le_path_of_bipartite hcH ⟨c⟩ h4H
  have hr := radius_le_of_neighbors_in_both_colors hc S hcH c both
  have hsub := G.path_induce_le (S : Set V)
  change H.path ≤ G.path at hsub
  change H.radius.toNat+⌊l H⌋₊ ≤ H.path at hp
  change G.radius.toNat ≤ H.radius.toNat at hr
  change G.radius.toNat+k ≤ _
  omega

/-- The conjectured bound transfers from a connected induced bipartite
graph when all omitted vertices see both color classes and the total degree
lost on their deletion is covered by their share of the average. -/
theorem radius_add_floor_le_path_of_bipartite_core (hc : G.Connected) (h4 : NoFourCycle G)
    (S : Finset V) (hcH : (G.induce (S : Set V)).Connected)
    (c : (G.induce (S : Set V)).Coloring (Fin 2))
    (both : ∀ z ∉ S, ∃ a b : S, c a ≠ c b ∧ G.Adj z a.val ∧ G.Adj z b.val)
    (charge : 2 * (∑ w ∈ Sᶜ, G.degree w) ≤ Sᶜ.card * ⌊l G⌋₊) :
    G.radius.toNat + ⌊l G⌋₊ ≤ G.path := by
  classical
  let H := G.induce (S : Set V)
  let : Nonempty S := hcH.nonempty
  let : Nonempty V := hc.nonempty
  let k := ⌊l G⌋₊
  have hav : (k : ℝ) ≤ l G := Nat.floor_le (div_nonneg
    (Finset.sum_nonneg (fun v _ => Nat.cast_nonneg (G.indepNeighborsCard v))) (Nat.cast_nonneg _))
  have count := sum_degree_ge_of_le_l hav
  have sizes := Finset.card_add_card_compl S
  rw [←sizes,Nat.mul_add] at count
  have hsum := sum_degree_le_induced_add_twice_outside (G := G) S
  change _ ≤ (∑ u : S, H.degree u) + _ at hsum
  change _ ≤ Sᶜ.card * k at charge
  rw [Nat.mul_comm Sᶜ.card k] at charge
  have hd : k * Fintype.card S ≤ ∑ u : S, H.degree u := by
    rw [Fintype.card_coe]
    omega
  exact radius_add_threshold_le_path_of_dense_bipartite_core hc h4 S hcH c both hd

end Wall133
