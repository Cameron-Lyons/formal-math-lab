module

public import SymmetricProduct
public import Mathlib.Data.Nat.Find

/-! The symmetric palette minima, their factor-three comparison, and sharpness. -/
public section

namespace Erdos160.SymmetricTransfer

def HasIntervalPalette (n k : ℕ) : Prop := n = 0 ∨ ∃ f : ℕ → Fin k, IntervalValid n f
def HasCyclicPalette (n k : ℕ) : Prop := n = 0 ∨ ∃ f : ℕ → Fin k, CyclicValid n f

private theorem exists_intervalPalette (n : ℕ) : ∃ k, HasIntervalPalette n k := by
  let f (x : ℕ) : Fin (n+1) := ⟨min x n, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  refine ⟨n+1, Or.inr ⟨f, ?_⟩⟩
  intro a s hs ha
  rintro ⟨_,bc⟩
  have eq := congrArg Fin.val bc
  simp [f, Nat.min_eq_left (by omega : a+s≤n), Nat.min_eq_left (by omega : a+2*s≤n)] at eq
  omega

private theorem exists_cyclicPalette (n : ℕ) : ∃ k, HasCyclicPalette n k := by
  obtain ⟨k,he | ⟨f,hf⟩⟩ := exists_intervalPalette n
  · exact ⟨0,Or.inl he⟩
  · exact ⟨3*k,Or.inr (interval_to_cyclic f hf)⟩

noncomputable def intervalMinimum (n : ℕ) := @Nat.find _ (Classical.decPred _) (exists_intervalPalette n)
noncomputable def cyclicMinimum (n : ℕ) := @Nat.find _ (Classical.decPred _) (exists_cyclicPalette n)

theorem intervalMinimum_spec (n : ℕ) : HasIntervalPalette n (intervalMinimum n) := by
  classical exact Nat.find_spec (exists_intervalPalette n)

theorem cyclicMinimum_spec (n : ℕ) : HasCyclicPalette n (cyclicMinimum n) := by
  classical exact Nat.find_spec (exists_cyclicPalette n)

theorem intervalMinimum_le {n k : ℕ} (h : HasIntervalPalette n k) : intervalMinimum n ≤ k := by
  classical exact Nat.find_min' (exists_intervalPalette n) h

theorem cyclicMinimum_le {n k : ℕ} (h : HasCyclicPalette n k) : cyclicMinimum n ≤ k := by
  classical exact Nat.find_min' (exists_cyclicPalette n) h

/-- The zero-length and zero-modulus conventions give both minima value zero. -/
theorem cyclicMinimum_le_three (m : ℕ) : cyclicMinimum m ≤ 3 * intervalMinimum m := by
  obtain he | ⟨f,hf⟩ := intervalMinimum_spec m
  · exact cyclicMinimum_le (Or.inl he)
  · exact cyclicMinimum_le (Or.inr (interval_to_cyclic f hf))

theorem intervalMinimum_le_cyclicMinimum (m : ℕ) : intervalMinimum m ≤ cyclicMinimum m := by
  obtain he | ⟨f,hf⟩ := cyclicMinimum_spec m
  · exact intervalMinimum_le (Or.inl he)
  · exact intervalMinimum_le (Or.inr ⟨f,restrict_cyclic hf (Nat.le_refl m)⟩)

theorem intervalMinimum_le_power {m : ℕ} (hm : 0<m) (t N : ℕ) (size : N≤m^t) :
    intervalMinimum N ≤ (cyclicMinimum m)^t := by
  obtain he | ⟨f,hf⟩ := cyclicMinimum_spec m
  · omega
  · obtain ⟨g,hg⟩ := cyclic_power hm f hf t
    exact intervalMinimum_le (Or.inr ⟨g,restrict_cyclic hg size⟩)

/-- Every interval progression has length at least four. -/
theorem intervalMinimum_three : intervalMinimum 3 = 1 := by
  have lo : 0 < intervalMinimum 3 := by
    obtain he | ⟨f,_⟩ := intervalMinimum_spec 3
    · omega
    · exact Nat.lt_of_le_of_lt (Nat.zero_le _) (f 0).isLt
  have hi : intervalMinimum 3 ≤ 1 := by
    refine intervalMinimum_le (Or.inr ⟨fun _ => 0, ?_⟩)
    intro a s hs size
    omega
  omega

/-- On the three-cycle a step-one progression repeats its endpoint, so
its two middle residues must have different colors. All three pairs arise. -/
theorem cyclicMinimum_three : cyclicMinimum 3 = 3 := by
  have hi := cyclicMinimum_le_three 3
  rw [intervalMinimum_three] at hi
  obtain he | ⟨f,hf⟩ := cyclicMinimum_spec 3
  · omega
  · have diff (a : ℕ) (ha : a<3) :
        f ((a+1)%3) ≠ f (((a+1)%3+1)%3) := by
      have q := hf a 1 ha (by decide) (by decide)
      have wrap : (((a+1)%3+1)%3+1)%3=a := by omega
      dsimp only at q
      rw [wrap] at q
      exact fun h => q ⟨rfl,h⟩
    have ab : f 0 ≠ f 1 := by simpa using diff 2 (by decide)
    have bc : f 1 ≠ f 2 := by simpa using diff 0 (by decide)
    have ca : f 2 ≠ f 0 := by simpa using diff 1 (by decide)
    have e01 : (f 0).val ≠ (f 1).val := fun h => ab (Fin.ext h)
    have e12 : (f 1).val ≠ (f 2).val := fun h => bc (Fin.ext h)
    have e20 : (f 2).val ≠ (f 0).val := fun h => ca (Fin.ext h)
    have h0 := (f 0).isLt
    have h1 := (f 1).isLt
    have h2 := (f 2).isLt
    omega

end Erdos160.SymmetricTransfer
#print axioms Erdos160.SymmetricTransfer.cyclicMinimum_le_three
#print axioms Erdos160.SymmetricTransfer.cyclicMinimum_three
