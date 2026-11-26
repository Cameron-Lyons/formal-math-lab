module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace Erdos617

open SimpleGraph

def colorGraph {V : Type*} {r : ℕ} (c : Sym2 V → Fin r) (k : Fin r) : SimpleGraph V where
  Adj x y := x ≠ y ∧ c s(x, y) = k
  symm.symm x y h := ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

instance {V : Type*} [DecidableEq V] {r : ℕ} (c : Sym2 V → Fin r) (k : Fin r) :
    DecidableRel (colorGraph c k).Adj :=
  fun x y ↦ inferInstanceAs (Decidable (x ≠ y ∧ c s(x, y) = k))

@[simp] theorem colorGraph_adj {V : Type*} {r : ℕ} (c : Sym2 V → Fin r)
    (k : Fin r) (x y : V) : (colorGraph c k).Adj x y ↔ x ≠ y ∧ c s(x, y) = k := Iff.rfl

/-- The colors partition the edges incident to a vertex. -/
theorem sum_colorGraph_degree {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (c : Sym2 V → Fin r) (x : V) :
    ∑ k : Fin r, (colorGraph c k).degree x = Fintype.card V - 1 := by
  let U := Finset.univ.erase x
  have hfilter (k : Fin r) : (colorGraph c k).neighborFinset x =
      U.filter fun y ↦ c s(x,y) = k := by
    ext y
    simp [U, mem_neighborFinset, ne_comm]
  simp_rw [degree, hfilter, Finset.sum_card_fiberwise_eq_card_filter]
  simp [U]


variable {V : Type*} {r : ℕ}

/-- Every (r+1)-vertex subset spans an edge in every color. -/
abbrev Balanced (c : Sym2 V → Fin r) : Prop :=
  ∀ S : Finset V, S.card = r + 1 → ∀ k, ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ c s(u,v) = k

theorem balanced_of_no_witness (c : Sym2 V → Fin r)
    (h : ¬ ∃ (S : Finset V) (k : Fin r), S.card = r + 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u,v) ≠ k) : Balanced c := by
  intro S hS k
  by_contra hn
  exact h ⟨S, k, hS, fun u hu v hv huv he => hn ⟨u, hu, v, hv, huv, he⟩⟩

/-- An outside vertex has at most one spoke of color k to a k-colored r-clique.
The other r−1 colors must all be represented among the spokes. -/
theorem exterior_clique_neighbor_count (c : Sym2 V → Fin r) (balanced : Balanced c)
    (k : Fin r) (C : Finset V) (hC : (colorGraph c k).IsNClique r C)
    (x : V) (hx : x ∉ C) :
    (C.filter fun v => c s(x,v) = k).card ≤ 1 := by
  classical
  let other := C.filter fun v => c s(x,v) ≠ k
  have hcard : (insert x C).card = r + 1 := by rw [Finset.card_insert_of_notMem hx, hC.card_eq]
  have hcover : Finset.univ.erase k ⊆ other.image (fun v => c s(x,v)) := by
    intro l hl
    have hlk := (Finset.mem_erase.mp hl).1
    obtain ⟨u, hu, v, hv, huv, hcol⟩ := balanced (insert x C) hcard l
    have spoke (z : V) (hz : z ∈ C) (e : c s(x,z) = l) :
        l ∈ other.image (fun v => c s(x,v)) :=
      Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hz, e ▸ hlk⟩, e⟩
    rcases Finset.mem_insert.mp hu with hux | huC
    · rcases Finset.mem_insert.mp hv with hvx | hvC
      · exact (huv (hux.trans hvx.symm)).elim
      · exact spoke v hvC (hux ▸ hcol)
    · rcases Finset.mem_insert.mp hv with hvx | hvC
      · apply spoke u huC
        rw [Sym2.eq_swap, ← hvx]
        exact hcol
      · exact (hlk (hcol.symm.trans (hC.isClique huC hvC huv).2)).elim
  have hcount := (Finset.card_le_card hcover).trans Finset.card_image_le
  rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin] at hcount
  have hsum := C.card_filter_add_card_filter_not (fun v => c s(x,v) = k)
  rw [hC.card_eq] at hsum
  change r - 1 ≤ (C.filter fun v => c s(x,v) ≠ k).card at hcount
  change (C.filter fun v => c s(x,v) = k).card + (C.filter fun v => c s(x,v) ≠ k).card = r at hsum
  omega

theorem exterior_clique_neighbor_unique (c : Sym2 V → Fin r) (balanced : Balanced c)
    (k : Fin r) (C : Finset V) (hC : (colorGraph c k).IsNClique r C)
    (x : V) (hx : x ∉ C) {a b : V} (ha : a ∈ C) (hb : b ∈ C)
    (hxa : (colorGraph c k).Adj x a) (hxb : (colorGraph c k).Adj x b) : a = b := by
  classical
  apply Finset.card_le_one.mp (exterior_clique_neighbor_count c balanced k C hC x hx)
  · exact Finset.mem_filter.mpr ⟨ha, hxa.2⟩
  · exact Finset.mem_filter.mpr ⟨hb, hxb.2⟩

/-- Balance descends along every injective map of vertices. -/
theorem balanced_pullback {V W : Type*} {r : ℕ} (c : Sym2 V → Fin r) (hb : Balanced c)
    (f : W ↪ V) : Balanced (fun e : Sym2 W => c (Sym2.map f e)) := by
  intro A hA j
  obtain ⟨u, hu, v, hv, huv, he⟩ := hb (A.map f) ((Finset.card_map _).trans hA) j
  obtain ⟨u', hu', rfl⟩ := Finset.mem_map.mp hu
  obtain ⟨v', hv', rfl⟩ := Finset.mem_map.mp hv
  exact ⟨u', hu', v', hv', fun h => huv (congrArg f h), he⟩

/-- Lift an independent set for a restricted coloring back into its specified vertex set. -/
theorem lift_independent_subset {V : Type*} {n r : ℕ} (c : Sym2 V → Fin r)
    (k : Fin r) (S : Finset V)
    (hex : ∃ I, (colorGraph (fun e : Sym2 S => c (Sym2.map Subtype.val e)) k).IsNIndepSet n I) :
    ∃ I ⊆ S, (colorGraph c k).IsNIndepSet n I := by
  let incl := Function.Embedding.subtype (· ∈ S)
  obtain ⟨I, hI⟩ := hex
  refine ⟨I.map incl, ?_, ?_, (Finset.card_map _).trans hI.card_eq⟩
  · intro a ha
    obtain ⟨w, _, rfl⟩ := Finset.mem_map.mp ha
    exact w.property
  · intro a ha b hb hab hadj
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hb
    have huv : u ≠ v := fun h => hab (congrArg incl h)
    exact hI.isIndepSet hu hv huv ⟨huv, hadj.2⟩

end Erdos617
