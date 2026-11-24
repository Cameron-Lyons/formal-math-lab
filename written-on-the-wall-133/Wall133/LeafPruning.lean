import Wall133.PendantForest

/-! # Deleting a peripheral leaf while preserving a counterexample -/
namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
private theorem indep_eq_degree (c : G.Coloring (Fin 2)) (v : V) :
    G.indepNeighborsCard v = G.degree v := by
  classical
  apply (indepNeighborsCard_le_degree v).antisymm
  rw [← G.card_neighborSet_eq_degree]
  have hs : (G.induce (G.neighborSet v)).IsIndepSet
      (↑(Finset.univ : Finset (G.neighborSet v)) : Set _) := by
    intro x _ y _ _ hxy
    exact c.valid (show G.Adj x.val y.val from hxy)
      (color_common c x.property.symm y.property.symm)
  simpa [indepNeighborsCard] using hs.card_le_indepNum

omit [DecidableEq V] in
theorem le_l_of_sum_degree [Nonempty V] (c : G.Coloring (Fin 2)) {k : ℕ}
    (hk : k * Fintype.card V ≤ ∑ v, G.degree v) : (k : ℝ) ≤ l G := by
  unfold l averageIndepNeighbors
  apply (le_div_iff₀ (by exact_mod_cast Fintype.card_pos : 0 < (Fintype.card V : ℝ))).2
  simp only [indepNeighbors, indep_eq_degree c]
  exact_mod_cast hk

/-- The floored average for a bipartite graph cannot decrease on deleting
a leaf if the old floor is at least two. -/
theorem floor_le_floor_delete_leaf [Nonempty V] (c : G.Coloring (Fin 2))
    (w : V) (hw : G.degree w = 1) (hk : 2 ≤ ⌊l G⌋₊) :
    let S := Finset.univ.erase w
    ⌊l G⌋₊ ≤ ⌊l (G.induce (S : Set V))⌋₊ := by
  classical
  let S := Finset.univ.erase w
  let H := G.induce (S : Set V)
  change ⌊l G⌋₊ ≤ ⌊l H⌋₊
  obtain ⟨z,hz,-⟩ := degree_eq_one_iff_existsUnique_adj.mp hw
  let : Nonempty S := ⟨⟨z, Finset.mem_erase.mpr ⟨hz.ne.symm, Finset.mem_univ _⟩⟩⟩
  let C : H.Coloring (Fin 2) := ⟨fun u => c u.val, fun h => c.map_rel h⟩
  let k := ⌊l G⌋₊
  have hav : (k : ℝ) ≤ l G := Nat.floor_le (div_nonneg
    (Finset.sum_nonneg (fun v _ => Nat.cast_nonneg (G.indepNeighborsCard v))) (Nat.cast_nonneg _))
  have hs := sum_degree_ge_of_le_l hav
  have sum := sum_degree_erase_vertex G w
  rw [hw] at sum
  change (∑ v, G.degree v) = (∑ u : S, H.degree u)+2*1 at sum
  have hcard : Fintype.card V = Fintype.card S + 1 := by
    simp only [Fintype.card_coe, S, Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ]
    have := Fintype.card_pos (α := V)
    omega
  rw [hcard, Nat.mul_add, Nat.mul_one] at hs
  have bound : k * Fintype.card S ≤ ∑ u : S, H.degree u := by
    change 2 ≤ k at hk
    omega
  exact Nat.le_floor (le_l_of_sum_degree C (k := k) (by
    convert bound using 1 <;> congr 2))

/-- A leaf can be pruned whenever each remaining vertex still has a
remaining vertex at least the old radius away. -/
theorem counterexample_delete_leaf_of_far_witnesses [Nonempty V]
    (hc : G.Connected) (c : G.Coloring (Fin 2)) (w : V) (hw : G.degree w = 1)
    (hk : 2 ≤ ⌊l G⌋₊) (hbad : G.path < G.radius.toNat + ⌊l G⌋₊)
    (hkeep : ∀ x, x ≠ w → ∃ y, y ≠ w ∧ G.radius.toNat ≤ G.dist x y) :
    let S := Finset.univ.erase w
    let H := G.induce (S : Set V)
    H.Connected ∧ G.radius.toNat ≤ H.radius.toNat ∧ ⌊l G⌋₊ ≤ ⌊l H⌋₊ ∧
      H.path < H.radius.toNat+⌊l H⌋₊ := by
  classical
  let S := Finset.univ.erase w
  let H := G.induce (S : Set V)
  have hconn : H.Connected := by
    have he : (S : Set V) = {w}ᶜ := by ext x; simp [S]
    change (G.induce (S : Set V)).Connected
    rw [he]
    exact hc.induce_compl_singleton_of_degree_eq_one hw
  let : Nonempty S := hconn.nonempty
  have hrad : G.radius.toNat ≤ H.radius.toNat := by
    obtain ⟨x, hx⟩ := H.exists_eccent_eq_radius
    obtain ⟨y, hne, hdist⟩ := hkeep x.val (Finset.mem_erase.mp x.property).1
    let z : S := ⟨y,Finset.mem_erase.mpr ⟨hne,Finset.mem_univ _⟩⟩
    have hle := dist_val_le_dist_induce (G := G) (S : Set V) hconn x z
    have hub := dist_le_radius_toNat_of_eccent_eq_radius hconn hx z
    exact hdist.trans (hle.trans hub)
  have hf := floor_le_floor_delete_leaf c w hw hk
  have hp := G.path_induce_le (S : Set V)
  change H.path ≤ G.path at hp
  change ⌊l G⌋₊ ≤ ⌊l H⌋₊ at hf
  have fail : H.path < H.radius.toNat+⌊l H⌋₊ := by omega
  exact ⟨hconn,hrad,hf,fail⟩

/-- In a counterexample any leaf in a singly attached forest can be
deleted if a different vertex of the forest is at least as far from
the attachment. Thus a smallest counterexample has at most one leaf
in each such forest. -/
theorem counterexample_prune_pendant_leaf [Nonempty V]
    (hc : G.Connected) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    (T : Finset V) (e : V) (hforest : (G.induce (T : Set V)).IsAcyclic)
    (hsep : ∀ z ∈ T, ∀ w, G.Adj z w → w ∈ T ∨ w = e)
    {w z : V} (hw : w ∈ T) (hdeg : G.degree w = 1) (hz : z ∈ T) (hne : z ≠ w)
    (hdeep : G.dist e w ≤ G.dist e z) (hr : 7 ≤ G.radius.toNat)
    (hbad : G.path < G.radius.toNat + ⌊l G⌋₊) :
    let S := Finset.univ.erase w
    let H := G.induce (S : Set V)
    H.Connected ∧ G.radius.toNat ≤ H.radius.toNat ∧ ⌊l G⌋₊ ≤ ⌊l H⌋₊ ∧
      H.path < H.radius.toNat+⌊l H⌋₊ := by
  classical
  let k := ⌊l G⌋₊
  have hk : 7 ≤ k := by have := chung_bound_nat G hc; dsimp [k]; omega
  have hav : (k : ℝ) ≤ l G := Nat.floor_le (div_nonneg
    (Finset.sum_nonneg (fun v _ => Nat.cast_nonneg (G.indepNeighborsCard v))) (Nat.cast_nonneg _))
  obtain ⟨C,a,hd,_⟩ := exists_growth_anchor c hk (sum_degree_ge_of_le_l hav)
  have disj := core_disjoint_of_pendant_forest T C e hsep hforest
    (fun u => (by omega : 3 ≤ k/2+1).trans (hd u))
  have depth (t : V) (ht : t ∈ T) : G.dist e t < G.radius.toNat := by
    obtain ⟨b,hb,hnear⟩ := (distances_to_core_of_bipartite_counterexample hc ⟨c⟩ h4
      (by omega) hbad C ⟨a.val,a.property⟩ hd t).1
    have := dist_add_of_boundary hc T e hsep (Finset.disjoint_left.mp disj hb) ht
    omega
  obtain ⟨y,p,hp,hy⟩ := exists_geodesic_ge_radius G hc e
  have hout : y ∉ T := fun hyT => (depth y hyT).not_ge (hy.trans_eq hp)
  apply counterexample_delete_leaf_of_far_witnesses hc c w hdeg (by change 2 ≤ k; omega) hbad
  intro x _
  by_cases hx : x ∈ T
  · refine ⟨y, fun he => hout (he ▸ hw), ?_⟩
    have h := dist_add_of_boundary hc T e hsep hout hx
    rw [G.dist_comm (u := y) (v := x), G.dist_comm (u := y) (v := e)] at h
    omega
  · obtain ⟨v,q,hq,hv⟩ := exists_geodesic_ge_radius G hc x
    by_cases he : v = w
    · refine ⟨z,hne,?_⟩
      have hfar : G.radius.toNat ≤ G.dist x v := by omega
      rw [he, dist_add_of_boundary hc T e hsep hx hw] at hfar
      rw [dist_add_of_boundary hc T e hsep hx hz]
      omega
    · exact ⟨v,he,by omega⟩

end Wall133
