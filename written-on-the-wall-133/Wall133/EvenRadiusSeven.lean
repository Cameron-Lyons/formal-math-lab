import Wall133.OddSmallSix

namespace Wall133
open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- When the average degree is at least h, two vertices of degree at least h
have a common neighbor. Otherwise the neighborhoods of all such vertices
would be disjoint. -/
theorem high_pair_at_distance_two [Nonempty V] {h : ℕ} (hh : 2 ≤ h)
    (havg : h * Fintype.card V ≤ ∑ v, G.degree v) :
    ∃ v w a, v ≠ w ∧ G.Adj a v ∧ G.Adj w a ∧ h ≤ G.degree v ∧ h ≤ G.degree w := by
  classical
  let T := (Finset.univ : Finset V).filter fun v => h ≤ G.degree v
  let L := (Finset.univ : Finset V).filter fun v => ¬h ≤ G.degree v
  have part : T.card+L.card = Fintype.card V := Finset.card_filter_add_card_filter_not (s := Finset.univ) _
  have split : ∑ v ∈ T, G.degree v + ∑ v ∈ L, G.degree v = ∑ v, G.degree v :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have small : ∑ v ∈ L, G.degree v ≤ L.card*(h-1) := by
    simpa using Finset.sum_le_sum (s := L) (g := fun _ => h-1) (f := fun v => G.degree v)
      (fun v hv => by have := (Finset.mem_filter.mp hv).2; omega)
  have tnon : T.Nonempty := by
    by_contra! ht
    rw [ht, Finset.sum_empty, zero_add] at split
    rw [ht, Finset.card_empty, zero_add] at part
    have := Fintype.card_pos (α := V)
    rw [part,split,Nat.mul_comm] at small
    have := Nat.mul_lt_mul_of_pos_right (by omega : h-1 < h) this
    omega
  by_contra! bad
  have dis : (T : Set V).PairwiseDisjoint (fun v => G.neighborFinset v) := by
    intro v hv w hw hne
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (bad v w a hne ((G.mem_neighborFinset _ _).mp ha).symm
      ((G.mem_neighborFinset _ _).mp hb) (Finset.mem_filter.mp hv).2).not_ge
        (Finset.mem_filter.mp hw).2
  have big : ∑ v ∈ T, G.degree v ≤ Fintype.card V := by
    have bd := Finset.card_le_card (Finset.subset_univ (T.biUnion (fun v => G.neighborFinset v)))
    simpa [Finset.card_biUnion dis, G.card_neighborFinset_eq_degree] using bd
  have cardlt : L.card < Fintype.card V := by have := tnon.card_pos; omega
  have strict := Nat.mul_lt_mul_of_pos_right cardlt (by omega : 0 < h-1)
  have eq : Fintype.card V*(h-1) + Fintype.card V = h*Fintype.card V := by
    rw [← Nat.mul_succ, show (h-1).succ = h by omega, Nat.mul_comm]
  omega

variable [DecidableEq V]

/-- An induced path of 2d+1 edges whose starting vertex has degree d+3
extends or admits detours yielding a path on 2d+5 vertices. -/
theorem path_of_odd_chain_high_root {d : ℕ} (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    (hd : 5 ≤ d) (hmin : ∀ v, d ≤ G.degree v) (P : Chain G (2*d+1))
    (hv : d+3 ≤ G.degree (P.vertex 0)) : 2*d+5 ≤ G.path := by
  by_cases hs : ∀ x (hx : Good P x) z, ¬Good (grow P x hx) z
  · exact three_row_stalls P c h4 (by omega) hmin hv hs
  push Not at hs
  obtain ⟨x,hx,z,hz⟩ := hs
  obtain ⟨a,b,ha,hb,hab⟩ := two_good P c h4 (by omega) (by omega)
  have other : ∃ y, Good P y ∧ x ≠ y := by
    by_cases he : x=a
    · exact ⟨b,hb,he ▸ hab⟩
    · exact ⟨a,ha,he⟩
  obtain ⟨y,hy,hxy⟩ := other
  apply secondLevel P c h4 (by omega) hx hy hxy hz
  have := hmin z
  exact Or.inr ⟨Or.inl (by omega),by omega⟩

/-- At every even density threshold at least eight, a four-cycle-free bipartite
graph has an induced path on at least seven more vertices than the threshold. -/
theorem add_seven_le_path_of_even_bipartite_density [Nonempty V]
    (hb : G.IsBipartite) (h4 : NoFourCycle G) {m : ℕ} (hm : 4 ≤ m)
    (hav : (2*m : ℕ) ≤ l G) : 2*m+7 ≤ G.path := by
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
  have avg : (m+1+3)*Fintype.card S ≤ ∑ v : S, H.degree v := by
    have ht : (2*m)*Fintype.card S ≤ ∑ v : S, H.degree v := by
      simpa [Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_comm] using hsum
    exact (Nat.mul_le_mul_right _ (by omega)).trans ht
  obtain ⟨v,w,a,hvw,ha,hw,hv,hwd⟩ := high_pair_at_distance_two (G := H) (by omega) avg
  obtain ⟨R,hR⟩ := exists_odd_chain_of_common_neighbor C h4' (by omega) hmin ha hw hvw.symm
    (hw := by omega)
  have hroot : R.reverse.vertex 0 = v := by simpa [Chain.reverse] using hR
  have hp := path_of_odd_chain_high_root C h4' (by omega) hmin R.reverse (hroot ▸ hv)
  have transfer := G.path_induce_le (S : Set V)
  change H.path ≤ _ at transfer
  omega

end Wall133
