import Erdos617.IndependentSets
import Erdos617.ColorCounts

namespace Erdos617

open SimpleGraph Finset

private theorem independent_three_of_high_compl_degree {r : ℕ} (hr : 3 ≤ r)
    {V : Type*} [Fintype V] [DecidableEq V] (hV : Fintype.card V = 2*r+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r)
    (hdeg : ∃ x, r ≤ (colorGraph c k)ᶜ.degree x) :
    ∃ I, (colorGraph c k).IsNIndepSet 3 I := by
  classical
  let G := colorGraph c k
  by_contra! hn
  obtain ⟨x, hdeg⟩ := hdeg
  obtain ⟨Q, hQN, hQcard⟩ := Finset.exists_subset_card_eq (s := Gᶜ.neighborFinset x)
    (show r ≤ (Gᶜ.neighborFinset x).card by rwa [Gᶜ.card_neighborFinset_eq_degree])
  have hQ : G.IsNClique r Q := by
    refine ⟨?_, hQcard⟩
    intro a ha b hb hab
    have ha' := (Gᶜ.mem_neighborFinset x a).mp (hQN ha)
    have hb' := (Gᶜ.mem_neighborFinset x b).mp (hQN hb)
    by_contra h
    exact hn {x,a,b} (G.isNClique_compl.mp
      (Gᶜ.is3Clique_triple_iff.mpr ⟨ha', hb', hab, h⟩))
  have outside : G.IsClique (↑(Qᶜ : Finset V) : Set V) := by
    intro a ha b hb' hab
    by_contra hnab
    have hpair : G.IsNIndepSet 2 {a,b} := by
      refine ⟨?_, by simp [hab]⟩
      change (↑({a,b} : Finset V) : Set V).Pairwise fun i j => ¬ G.Adj i j
      simpa only [Finset.coe_insert, Finset.coe_singleton, Set.pairwise_pair] using (show a ≠ b → (¬ G.Adj a b) ∧ (¬ G.Adj b a) from fun _ => ⟨hnab, fun h => hnab h.symm⟩)
    have hdisj : Disjoint Q {a,b} := by
      simp [Finset.disjoint_insert_right, Finset.mem_compl.mp ha, Finset.mem_compl.mp hb']
    obtain ⟨I, hi⟩ := extend_across_clique G Q {a,b} hQ hpair hdisj (by omega)
      (fun z hz _ hu _ hv => exterior_clique_neighbor_unique c hb k Q hQ z hz hu hv)
    exact hn I hi
  have hQc : (Qᶜ : Finset V).card = r+1 := by rw [Finset.card_compl, hV, hQcard]; omega
  let : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨j, hj⟩ := exists_ne k
  obtain ⟨a, ha, b, hb', hab, hcol⟩ := hb Qᶜ hQc j
  exact hj (hcol.symm.trans (outside ha hb' hab).2)

/-- A balanced coloring on 2r+1 vertices has an independent triple in each prescribed color. -/
theorem independent_three_of_balanced {r : ℕ} (hr : 3 ≤ r)
    {V : Type*} [Fintype V] [DecidableEq V] (hV : Fintype.card V = 2*r+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r) :
    ∃ I, (colorGraph c k).IsNIndepSet 3 I := by
  apply independent_three_of_high_compl_degree hr hV c hb k
  have hl (j : Fin r) (_ : j ≠ k) : r + 2 ≤ (colorGraph c j).edgeFinset.card := by
    simpa using color_edge_count_of_balanced (by omega) hV c hb j
  have hcount : (2*r+1)*(r-1) < 2*((r-1)*(r+2)) := by
    obtain ⟨a,rfl⟩ : ∃ a, r = a+3 := ⟨r-3, by omega⟩
    simp only [show ∀ a : ℕ, a + 3 - 1 = a + 2 by omega]
    nlinarith
  obtain ⟨x, hx⟩ := exists_compl_degree_ge c k hV hl hcount
  exact ⟨x, by omega⟩

/-- The independent triple can be found inside any specified 2r+1 vertex set. -/
theorem independent_three_in_subset {r : ℕ} (hr : 3 ≤ r)
    {V : Type*} [DecidableEq V] (c : Sym2 V → Fin r) (hb : Balanced c)
    (k : Fin r) (S : Finset V) (hS : S.card = 2*r+1) :
    ∃ I ⊆ S, (colorGraph c k).IsNIndepSet 3 I := by
  apply lift_independent_subset c k S
  exact independent_three_of_balanced hr ((Fintype.card_coe S).trans hS)
    _ (balanced_pullback c hb (Function.Embedding.subtype (· ∈ S))) k

end Erdos617
