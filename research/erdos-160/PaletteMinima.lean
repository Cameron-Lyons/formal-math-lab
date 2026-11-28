module

public import CyclicProduct
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Monotone.Defs

/-! Least palette sizes for the interval and odd cyclic versions of Erdős problem 160. -/
public section

namespace Erdos160

open CyclicTransfer

/-- The empty interval admits the empty palette. On a nonempty interval any coloring
extends to all natural indices by putting an arbitrary existing color outside the interval. -/
def HasIntervalPalette (n k : ℕ) : Prop :=
  n = 0 ∨ ∃ f : ℕ → Fin k, IntervalValid n f

/-- A cyclic coloring with at most `k` colors in the representative convention. -/
def HasCyclicPalette (m k : ℕ) : Prop :=
  ∃ f : ℕ → Fin k, CyclicValid m f

private theorem exists_intervalPalette (n : ℕ) : ∃ k, HasIntervalPalette n k := by
  let f (x : ℕ) : Fin (n+1) := ⟨min x n, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  refine ⟨n+1, Or.inr ⟨f, ?_⟩⟩
  intro a s hs ha
  have inject {x y : ℕ} (hx : x ≤ n) (hy : y ≤ n) (eq : f x = f y) : x = y := by
    simpa [f, Nat.min_eq_left hx, Nat.min_eq_left hy] using congrArg Fin.val eq
  exact Or.inl ⟨fun eq => by have := inject (by omega) (by omega) eq; omega,
    fun eq => by have := inject (by omega) (by omega) eq; omega,
    fun eq => by have := inject (by omega) (by omega) eq; omega⟩

/-- The minimum number of colors of a valid coloring of `[0,n)`. -/
noncomputable def intervalPaletteMinimum (n : ℕ) : ℕ := by
  classical exact Nat.find (exists_intervalPalette n)

theorem intervalPaletteMinimum_spec (n : ℕ) :
    HasIntervalPalette n (intervalPaletteMinimum n) := by
  classical exact Nat.find_spec (exists_intervalPalette n)

theorem intervalPaletteMinimum_le {n k : ℕ} (h : HasIntervalPalette n k) :
    intervalPaletteMinimum n ≤ k := by
  classical exact Nat.find_min' (exists_intervalPalette n) h

@[simp] theorem intervalPaletteMinimum_zero : intervalPaletteMinimum 0 = 0 :=
  Nat.eq_zero_of_le_zero (intervalPaletteMinimum_le (Or.inl rfl))

theorem intervalPaletteMinimum_pos (n : ℕ) (hn : 0 < n) : 0 < intervalPaletteMinimum n := by
  obtain h | ⟨f, _⟩ := intervalPaletteMinimum_spec n
  · omega
  · exact Nat.lt_of_le_of_lt (Nat.zero_le _) (f 0).isLt

theorem intervalPaletteMinimum_mono : Monotone intervalPaletteMinimum := by
  intro n m h
  apply intervalPaletteMinimum_le
  obtain hm | ⟨f,hf⟩ := intervalPaletteMinimum_spec m
  · exact Or.inl (by omega)
  · exact Or.inr ⟨f, fun a s hs hbound => hf a s hs (Nat.lt_of_lt_of_le hbound h)⟩

private theorem exists_cyclicPalette {m : ℕ} (odd : m % 2 = 1) :
    ∃ k, HasCyclicPalette m k := by
  obtain hm | ⟨f,hf⟩ := intervalPaletteMinimum_spec m
  · omega
  · exact ⟨12 * intervalPaletteMinimum m, interval_to_odd_cyclic odd f hf⟩

/-- Minimum number of colors on an odd cycle, including the one-point cycle.
At even inputs this total function takes the sentinel value zero. -/
noncomputable def cyclicPaletteMinimum (m : ℕ) : ℕ := by
  classical exact if odd : m % 2 = 1 then Nat.find (exists_cyclicPalette odd) else 0

theorem cyclicPaletteMinimum_spec {m : ℕ} (odd : m % 2 = 1) :
    HasCyclicPalette m (cyclicPaletteMinimum m) := by
  classical
  simpa [cyclicPaletteMinimum, odd] using Nat.find_spec (exists_cyclicPalette odd)

theorem cyclicPaletteMinimum_le {m k : ℕ} (odd : m % 2 = 1) (h : HasCyclicPalette m k) :
    cyclicPaletteMinimum m ≤ k := by
  classical
  simpa [cyclicPaletteMinimum, odd] using Nat.find_min' (exists_cyclicPalette odd) h

theorem cyclicPaletteMinimum_pos {m : ℕ} (odd : m % 2 = 1) : 0 < cyclicPaletteMinimum m := by
  obtain ⟨f,_⟩ := cyclicPaletteMinimum_spec odd
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (f 0).isLt

theorem intervalPaletteMinimum_le_cyclicPaletteMinimum {m : ℕ} (odd : m % 2 = 1) :
    intervalPaletteMinimum m ≤ cyclicPaletteMinimum m := by
  obtain ⟨f,hf⟩ := cyclicPaletteMinimum_spec odd
  exact intervalPaletteMinimum_le (Or.inr ⟨f, restrict_cyclic hf (Nat.le_refl m)⟩)

theorem cyclicPaletteMinimum_le_twelve {m : ℕ} (odd : m % 2 = 1) :
    cyclicPaletteMinimum m ≤ 12 * intervalPaletteMinimum m := by
  obtain hm | ⟨f,hf⟩ := intervalPaletteMinimum_spec m
  · omega
  · exact cyclicPaletteMinimum_le odd (interval_to_odd_cyclic odd f hf)

theorem intervalPaletteMinimum_le_power {m : ℕ} (odd : m % 2 = 1)
    (t N : ℕ) (size : N ≤ m^t) : intervalPaletteMinimum N ≤ (cyclicPaletteMinimum m)^t := by
  obtain ⟨f,hf⟩ := cyclicPaletteMinimum_spec odd
  obtain ⟨g,hg⟩ := cyclic_power (by omega) f hf t
  exact intervalPaletteMinimum_le (Or.inr ⟨g, restrict_cyclic hg size⟩)

theorem cyclicPaletteMinimum_power_le {m : ℕ} (odd : m % 2 = 1) (t : ℕ) :
    cyclicPaletteMinimum (m^t) ≤ (cyclicPaletteMinimum m)^t := by
  have oddPower : (m^t)%2 = 1 := by
    induction t with
    | zero => rfl
    | succ t ih => simp [Nat.pow_succ, Nat.mul_mod, ih, odd]
  obtain ⟨f,hf⟩ := cyclicPaletteMinimum_spec odd
  exact cyclicPaletteMinimum_le oddPower (cyclic_power (by omega) f hf t)

end Erdos160

#print axioms Erdos160.intervalPaletteMinimum_le_power
#print axioms Erdos160.cyclicPaletteMinimum_le_twelve
