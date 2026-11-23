import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Erdos835

open Finset

/-- On eleven points the 55 pairs cannot be partitioned among triples,
each of which accounts for exactly three pairs. -/
theorem no_triple_packing_11 {V : Type*} [Fintype V] [DecidableEq V]
    (hv : Fintype.card V = 11) (P : Finset V → Prop)
    (cover : ∀ e : Finset V, e.card = 2 → ∃! t : Finset V, t.card = 3 ∧ P t ∧ e ⊆ t) :
    False := by
  classical
  let B := ((univ : Finset V).powersetCard 3).filter P
  have memB (t : Finset V) : t ∈ B ↔ t.card = 3 ∧ P t := by simp [B]
  have partition : B.biUnion (powersetCard 2) = (univ : Finset V).powersetCard 2 := by
    ext e
    rw [mem_biUnion, mem_powersetCard]
    constructor
    · rintro ⟨t, _, he⟩
      exact ⟨subset_univ _, (mem_powersetCard.mp he).2⟩
    · rintro ⟨_, he⟩
      obtain ⟨t, ⟨ht, hp, hsub⟩, _⟩ := cover e he
      exact ⟨t, (memB t).mpr ⟨ht, hp⟩, mem_powersetCard.mpr ⟨hsub, he⟩⟩
  have disjoint : (B : Set (Finset V)).PairwiseDisjoint (powersetCard 2) := by
    intro t ht s hs hts
    apply disjoint_left.mpr
    intro e he hs'
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp he
    exact hts ((cover e hcard).unique ⟨((memB t).mp ht).1, ((memB t).mp ht).2, hsub⟩
      ⟨((memB s).mp hs).1, ((memB s).mp hs).2, (mem_powersetCard.mp hs').1⟩)
  have count := card_biUnion disjoint
  rw [partition, card_powersetCard, card_univ, hv] at count
  have three : ∀ t ∈ B, (t.powersetCard 2).card = 3 := by
    intro t ht
    rw [card_powersetCard, ((memB t).mp ht).1]
    decide
  rw [sum_congr rfl three, sum_const, Nat.nsmul_eq_mul] at count
  change 55 = B.card * 3 at count
  omega

/-- A coloring of the 8-subsets of eleven points cannot show every color
exactly once on the faces of every 9-set. Complement the sets of one color
to obtain the impossible triple packing above. -/
theorem no_rainbow_eight_on_eleven {V I : Type*} [Fintype V] [DecidableEq V] [Nonempty I]
    (hv : Fintype.card V = 11) (col : {s : Finset V // s.card = 8} → I)
    (hfaces : ∀ (A : Finset V) (hA : A.card = 9), Function.Bijective
      (fun x : A => col ⟨A.erase x.val, by simp [card_erase_of_mem x.property, hA]⟩)) : False := by
  classical
  let i : I := Classical.choice inferInstance
  let P (t : Finset V) := ∃ h : tᶜ.card = 8, col ⟨tᶜ, h⟩ = i
  apply no_triple_packing_11 hv P
  intro e he
  have hc : eᶜ.card = 9 := by rw [card_compl, hv, he]
  let f (x : ↥(eᶜ)) := col ⟨eᶜ.erase x.val, by simp [card_erase_of_mem x.property, hc]⟩
  have hf : Function.Bijective f := hfaces eᶜ hc
  have hP (x : ↥(eᶜ)) : P (insert x.val e) ↔ f x = i := by
    simp only [P, compl_insert]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨by simp [card_erase_of_mem x.property, hc], h⟩⟩
  obtain ⟨x, hx⟩ := hf.2 i
  have hxe := mem_compl.mp x.property
  refine ⟨insert x.val e, ⟨by simp [hxe, he], (hP x).mpr hx, subset_insert _ _⟩, ?_⟩
  rintro t ⟨ht, hp, hsub⟩
  obtain ⟨y, hy, rfl⟩ := exists_eq_insert_iff.mpr ⟨hsub, by rw [he, ht]⟩
  let z : ↥(eᶜ) := ⟨y, mem_compl.mpr hy⟩
  have hz := hf.1 (((hP z).mp hp).trans hx.symm)
  exact congrArg (fun a : ↥(eᶜ) => insert a.val e) hz

end Erdos835
