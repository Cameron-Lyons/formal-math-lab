import Cycles
import Edges

namespace Erdos835

open Finset

/-- A Steiner system `S(15,16,32)` has 16-point blocks and covers each
15-point set by a unique block. -/
structure IsSteinerSystem (D : Set (Finset (Fin 32))) : Prop where
  block_card : ∀ B ∈ D, B.card = 16
  covers : ∀ T : Finset (Fin 32), T.card = 15 → ∃! B, B ∈ D ∧ T ⊆ B

/-- Deriving at the 14 points outside an invariant 18-set gives an invariant
perfect matching on the 18-set. Its fixed points therefore come in pairs. -/
theorem IsSteinerSystem.even_fixed_on_18 {D : Set (Finset (Fin 32))}
    (hD : IsSteinerSystem D) (g : Equiv.Perm (Fin 32))
    (hInv : ∀ B ∈ D, B.map g.toEmbedding ∈ D)
    (W : Finset (Fin 32)) (hw : W.card = 18) (hW : W.map g.toEmbedding = W) :
    Even (W.filter fun x => g x = x).card := by
  let K := Wᶜ
  have hK : K.card = 14 := by simp [K, card_compl, hw]
  have hKg : K.map g.toEmbedding = K := by
    change (univ \ W).map g.toEmbedding = univ \ W
    rw [map_sdiff, map_univ_equiv, hW]
  let R (x y : Fin 32) := x ≠ y ∧ insert y (insert x K) ∈ D
  apply even_fixed_of_matching W g hW R
  · intro x y h
    exact ⟨h.1.symm, by simpa only [insert_comm x y] using h.2⟩
  · exact fun x h => h.1 rfl
  · intro x hx
    let T := insert x K
    have ht : T.card = 15 := by simp [T, K, hx, card_compl, hw]
    obtain ⟨B, ⟨hB, hTB⟩, huniq⟩ := hD.covers T ht
    obtain ⟨y, hy, hyB⟩ := exists_eq_insert_iff.mpr ⟨hTB, by rw [ht, hD.block_card B hB]⟩
    have hyinfo : y ≠ x ∧ y ∈ W := by simpa [T, K] using hy
    refine ⟨⟨y, hyinfo.2⟩, ⟨hyinfo.1.symm, hyB ▸ hB⟩, ?_⟩
    intro z hz
    have heq : insert z.val T = insert y T :=
      (huniq (insert z.val T) ⟨hz.2, subset_insert _ _⟩).trans hyB.symm
    have hzmem : z.val ∈ insert y T := heq ▸ mem_insert_self z.val T
    apply Subtype.ext
    exact (mem_insert.mp hzmem).resolve_right (by simp [T, K, hz.1.symm, z.property])
  · intro x y h
    refine ⟨g.injective.ne h.1, ?_⟩
    simpa only [map_insert, Equiv.coe_toEmbedding, hKg] using hInv _ h.2

/-- A single Steiner system `S(15,16,32)` cannot admit an automorphism
of order 11 or 13. -/
theorem IsSteinerSystem.no_order11_or_13 {D : Set (Finset (Fin 32))}
    (hD : IsSteinerSystem D) (g : Equiv.Perm (Fin 32))
    (hInv : ∀ B ∈ D, B.map g.toEmbedding ∈ D) :
    ¬ (orderOf g = 11 ∨ orderOf g = 13) := by
  intro h
  have hp : (orderOf g).Prime := by rcases h with h | h <;> rw [h] <;> decide
  obtain ⟨W, hw, hW, hf⟩ := primeOrder_witness18 hp (by omega) (by omega) g rfl
  obtain ⟨n, hn⟩ := hD.even_fixed_on_18 g hInv W hw hW
  omega

end Erdos835
