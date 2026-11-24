import Wall133.BlocksBipartiteCore
import Wall133.NeighborhoodTriangles

/-! # Triangles attached along edges of a bipartite graph -/

namespace Wall133
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/-- A vertex outside a retained vertex set whose two neighbors are the
endpoints of one edge of the retained graph. -/
def IsTriangleTipOver (G : SimpleGraph V) (S : Finset V) (z : V) : Prop :=
  ∃ a b : S, G.Adj a.val b.val ∧ ∀ w, G.Adj z w ↔ w = a.val ∨ w = b.val

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private theorem tip_indep_le_one (h4 : NoFourCycle G) {S : Finset V} {z : V}
    (ht : IsTriangleTipOver G S z) : G.indepNeighborsCard z ≤ 1 := by
  classical
  obtain ⟨a,b,hab,hz⟩ := ht
  have hsub : G.neighborFinset z ⊆ {a.val,b.val} := by
    intro w hw
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      (hz w).1 ((G.mem_neighborFinset _ _).mp hw)
  have hd := Finset.card_le_card hsub
  rw [G.card_neighborFinset_eq_degree, Finset.card_pair hab.ne] at hd
  let H := G.induce (G.neighborSet z)
  let x : G.neighborSet z := ⟨a.val,(hz _).2 (Or.inl rfl)⟩
  let y : G.neighborSet z := ⟨b.val,(hz _).2 (Or.inr rfl)⟩
  have hxy : H.Adj x y := hab
  have he : 0 < H.edgeFinset.card := Finset.card_pos.mpr ⟨s(x,y),H.mem_edgeFinset.mpr hxy⟩
  have h := indepNeighborsCard_eq_degree_sub_neighborhood_edges h4 z
  change G.indepNeighborsCard z = G.degree z - H.edgeFinset.card at h
  omega

omit [Fintype V] in
/-- Independent neighbors can be represented by distinct neighbors in the
retained graph. An outside neighbor is represented by the opposite endpoint
of its attached edge. -/
private theorem indep_le_retained_degree (h4 : NoFourCycle G) (S : Finset V)
    (tips : ∀ z ∉ S, IsTriangleTipOver G S z) (x : S) :
    G.indepNeighborsCard x.val ≤ (G.induce (S : Set V)).degree x := by
  classical
  let H := G.induce (S : Set V)
  let N := G.induce (G.neighborSet x.val)
  have reps (z : G.neighborSet x.val) :
      ∃ w : H.neighborSet x, z.val = w.val.val ∨ G.Adj z.val w.val.val := by
    by_cases hi : z.val ∈ S
    · exact ⟨⟨⟨z.val,hi⟩,z.property⟩,Or.inl rfl⟩
    · obtain ⟨a,b,hab,hz⟩ := tips z.val hi
      rcases (hz _).1 z.property.symm with h | h
      · exact ⟨⟨b,show G.Adj x.val b.val from h ▸ hab⟩,Or.inr ((hz _).2 (Or.inr rfl))⟩
      · exact ⟨⟨a,show G.Adj x.val a.val from h ▸ hab.symm⟩,Or.inr ((hz _).2 (Or.inl rfl))⟩
  choose f hf using reps
  obtain ⟨I,hI⟩ := exists_isNIndepSet_indepNum (G := N)
  let proj (z : I) := f z.val
  have injective : Function.Injective proj := by
    intro y z eq
    change f y.val = f z.val at eq
    have hz := hf z.val
    rw [←eq] at hz
    apply Subtype.ext
    apply Subtype.ext
    rcases hf y.val with hy | hy <;> rcases hz with hz | hz
    · exact hy.trans hz.symm
    · have hadj : N.Adj z.val y.val := show G.Adj z.val.val y.val.val from hy ▸ hz
      exact False.elim (hI.isIndepSet z.property y.property hadj.ne hadj)
    · have hadj : N.Adj y.val z.val := show G.Adj y.val.val z.val.val from hz ▸ hy
      exact False.elim (hI.isIndepSet y.property z.property hadj.ne hadj)
    · have hw : G.Adj x.val (f y.val).val.val := (f y.val).property
      exact h4 hw.ne y.val.property hy.symm z.val.property hz.symm
  have hcard := Fintype.card_le_of_injective proj injective
  change N.indepNum ≤ H.degree x
  simpa only [Fintype.card_coe, hI.card_eq, H.card_neighborSet_eq_degree] using hcard

private theorem sum_indep_le_of_triangle_tips (h4 : NoFourCycle G) (S : Finset V)
    (tips : ∀ z ∉ S, IsTriangleTipOver G S z) :
    (∑ z, G.indepNeighborsCard z) ≤ (∑ u : S, (G.induce (S : Set V)).degree u) + Sᶜ.card := by
  classical
  let H := G.induce (S : Set V)
  have low : ∑ z ∈ Sᶜ, G.indepNeighborsCard z ≤ Sᶜ.card := by
    simpa using Finset.sum_le_sum (s := Sᶜ) (f := fun z => G.indepNeighborsCard z)
      (g := fun _ => 1) (fun z hz => tip_indep_le_one h4 (tips z (Finset.mem_compl.mp hz)))
  have high : ∑ z ∈ S, G.indepNeighborsCard z ≤ ∑ u : S, H.degree u := by
    rw [← Finset.sum_attach]
    exact Finset.sum_le_sum (fun u _ => indep_le_retained_degree h4 S tips u)
  have total := Finset.sum_add_sum_compl S (fun z => G.indepNeighborsCard z)
  change (∑ z, G.indepNeighborsCard z) ≤ (∑ u : S,H.degree u) + Sᶜ.card
  omega

omit [DecidableRel G.Adj] in
/-- An attached triangle tip stays within the radius of the retained bipartite graph. -/
theorem radius_le_of_triangle_tips (hc : G.Connected) (S : Finset V)
    (hcH : (G.induce (S : Set V)).Connected) (c : (G.induce (S : Set V)).Coloring (Fin 2))
    (tips : ∀ z ∉ S, IsTriangleTipOver G S z) :
    G.radius.toNat ≤ (G.induce (S : Set V)).radius.toNat := by
  apply radius_le_of_neighbors_in_both_colors hc S hcH c
  intro z hz
  obtain ⟨a,b,hab,hadj⟩ := tips z hz
  exact ⟨a,b,c.valid hab, (hadj _).2 (Or.inl rfl), (hadj _).2 (Or.inr rfl)⟩

/-- WOWII 133 for all radii when deleting degree-two triangle tips leaves
a connected bipartite induced subgraph. The attached triangles may lie
on an arbitrary number of edges in that subgraph. -/
theorem radius_add_floor_le_path_of_triangle_tips (hc : G.Connected) (h4 : NoFourCycle G)
    (S : Finset V) (hcH : (G.induce (S : Set V)).Connected)
    (hb : (G.induce (S : Set V)).IsBipartite) (tips : ∀ z ∉ S, IsTriangleTipOver G S z) :
    G.radius.toNat + ⌊l G⌋₊ ≤ G.path := by
  classical
  let H := G.induce (S : Set V)
  let : Nonempty S := hcH.nonempty
  let : Nonempty V := hc.nonempty
  let k := ⌊l G⌋₊
  change G.radius.toNat+k ≤ _
  by_cases hk : k ≤ 1
  · have := radius_add_one_le_path G hc
    omega
  obtain ⟨c⟩ := hb
  have hav : (k : ℝ) ≤ l G := Nat.floor_le (div_nonneg
    (Finset.sum_nonneg (fun v _ => Nat.cast_nonneg (G.indepNeighborsCard v))) (Nat.cast_nonneg _))
  have count : k * Fintype.card V ≤ ∑ z, G.indepNeighborsCard z := by
    have hh := (le_div_iff₀ (by exact_mod_cast Fintype.card_pos : 0 < (Fintype.card V : ℝ))).mp hav
    simp only [indepNeighbors] at hh
    exact_mod_cast hh
  have total := sum_indep_le_of_triangle_tips h4 S tips
  change (∑ x,G.indepNeighborsCard x) ≤ (∑ u : S,H.degree u) + Sᶜ.card at total
  have sizes := Finset.card_add_card_compl S
  rw [←sizes,Nat.mul_add] at count
  have hmul := Nat.mul_le_mul_right Sᶜ.card (show 1 ≤ k by omega)
  have hdeg : k*Fintype.card S ≤ ∑ u : S, H.degree u := by
    rw [Fintype.card_coe]
    omega
  apply radius_add_threshold_le_path_of_dense_bipartite_core hc h4 S hcH c _ hdeg
  intro z hz
  obtain ⟨a,b,hab,hadj⟩ := tips z hz
  exact ⟨a,b,c.valid hab,(hadj _).2 (Or.inl rfl),(hadj _).2 (Or.inr rfl)⟩


/-- The real-valued bound follows whenever an integer separates the
ambient average and the retained average. Each triangle tip contributes
at most one to the sum of neighborhood independence numbers. -/
theorem radius_add_l_le_path_of_triangle_tips (hc : G.Connected) (h4 : NoFourCycle G)
    (S : Finset V) (hcH : (G.induce (S : Set V)).Connected)
    (hb : (G.induce (S : Set V)).IsBipartite) (tips : ∀ z ∉ S, IsTriangleTipOver G S z)
    {d : ℕ} (hd : d * S.card ≤ ∑ u : S, (G.induce (S : Set V)).degree u)
    (hcount : (∑ u : S, (G.induce (S : Set V)).degree u) + Sᶜ.card ≤ d * Fintype.card V) :
    (G.radius.toNat : ℝ) + l G ≤ G.path := by
  classical
  let H := G.induce (S : Set V)
  let : Nonempty S := hcH.nonempty
  let : Nonempty V := hc.nonempty
  obtain ⟨c⟩ := hb
  have hg : (∑ v, G.indepNeighborsCard v) ≤ d * Fintype.card V :=
    (sum_indep_le_of_triangle_tips h4 S tips).trans hcount
  have hav : l G ≤ (d : ℝ) := by
    unfold l averageIndepNeighbors
    apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos : 0 < (Fintype.card V : ℝ))).2
    simp only [indepNeighbors]
    exact_mod_cast hg
  have hdH : d * Fintype.card S ≤ ∑ u : S, H.degree u := by simpa using hd
  have hpath : G.radius.toNat + d ≤ G.path := by
    apply radius_add_threshold_le_path_of_dense_bipartite_core hc h4 S hcH c _ hdH
    intro z hz
    obtain ⟨a,b,hab,hadj⟩ := tips z hz
    exact ⟨a,b,c.valid hab,(hadj _).2 (Or.inl rfl),(hadj _).2 (Or.inr rfl)⟩
  calc
    _ ≤ (G.radius.toNat : ℝ) + d := by gcongr
    _ ≤ G.path := by exact_mod_cast hpath

/-- The unrounded conjecture holds for all triangle-tip extensions of
bipartite graphs with positive integral average degree. -/
theorem radius_add_l_le_path_of_triangle_tips_integer_average (hc : G.Connected) (h4 : NoFourCycle G)
    (S : Finset V) (hcH : (G.induce (S : Set V)).Connected)
    (hb : (G.induce (S : Set V)).IsBipartite) (tips : ∀ z ∉ S, IsTriangleTipOver G S z)
    {d : ℕ} (hd : 1 ≤ d) (havg : (∑ u : S, (G.induce (S : Set V)).degree u) = d * S.card) :
    (G.radius.toNat : ℝ) + l G ≤ G.path := by
  apply radius_add_l_le_path_of_triangle_tips hc h4 S hcH hb tips havg.ge
  rw [havg,← Finset.card_add_card_compl S,Nat.mul_add]
  have := Nat.mul_le_mul_right Sᶜ.card hd
  omega

end Wall133
