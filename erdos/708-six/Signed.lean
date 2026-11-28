module

public import Slots
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.BigOperators.ModEq
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace IntervalSix
open Erdos708Slots

/-- Translate by a multiple of the target. Every site, and hence the whole
product, keeps its residue modulo the target. -/
theorem integer_starts {M k target : ℕ} (h : ∀ L : ℕ, Cover L M k target)
    (ht : 0 < target) (L : ℤ) :
    ∃ B : Finset ℤ, B ⊆ Finset.Ico L (L+(M:ℤ)) ∧ B.card≤k ∧ (target:ℤ) ∣ ∏ b ∈ B, b := by
  let K := (L % target).toNat
  have hK : (K : ℤ) = L % target := Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  let f (a : ℕ) := (a : ℤ) + (L-K)
  obtain ⟨C,hC,hcard,hprod⟩ := h K
  refine ⟨C.image f, ?_, Finset.card_image_le.trans hcard, ?_⟩
  · intro b hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨h₁,h₂⟩ := Finset.mem_Ico.mp (hC ha)
    exact Finset.mem_Ico.mpr (by dsimp [f]; omega)
  · rw [Finset.prod_image (fun _ _ _ _ he => by dsimp [f] at he; omega)]
    have heq (a : ℕ) : (a : ℤ) ≡ f a [ZMOD target] := by
      apply Int.modEq_iff_dvd.mpr
      simpa [f,hK] using Int.modEq_iff_dvd.mp (Int.mod_modEq L (target:ℤ))
    apply (Int.ModEq.prod fun a (_ : a ∈ C) => heq a).dvd_iff.mp
    simpa only [Nat.cast_prod] using Int.natCast_dvd_natCast.mpr hprod

end IntervalSix
