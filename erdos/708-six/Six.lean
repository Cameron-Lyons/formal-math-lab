module

public import SixFinite
public import SixLarge
public import Signed
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import SixLower

@[expose] public section

namespace IntervalSix
open Erdos708Slots

/-- Every translate of the window with length equal to the largest of the six originals. -/
theorem six_upper (A : Finset ℕ) (hc : A.card=6) (h2 : ∀ a∈A, 2 ≤ a) (L : ℕ) :
    Cover L (A.sup id) 8 (∏ a∈A,a) := by
  have hm : A.sup id ∈ A := by
    simpa using (Finset.sup_mem_of_nonempty (f := id) (Finset.card_pos.mp (by omega : 0 < A.card)))
  have hb (a : ℕ) (h : a∈A) : 2≤a ∧ a≤A.sup id := ⟨h2 a h,Finset.le_sup (f:=id) h⟩
  by_cases h : A.sup id < 70
  · exact FiniteCheck.finiteUpper A hc hm hb h
  · exact six_large A hc hb (by omega)

/-- The universal bound in the user's integer-start convention. -/
theorem six_integer (A : Finset ℕ) (hc : A.card=6) (h2 : ∀ a∈A, 2 ≤ a) (L : ℤ) :
    ∃ B : Finset ℤ, B ⊆ Finset.Ico L (L + ((A.sup id : ℕ) : ℤ)) ∧ B.card ≤ 8 ∧
      ((∏ a∈A, a : ℕ) : ℤ) ∣ ∏ b∈B,b := by
  exact integer_starts (six_upper A hc h2) (Finset.prod_pos fun a ha => lt_of_lt_of_le (by decide : 0 < 2) (h2 a ha)) L

end IntervalSix

namespace Erdos708

/-- Eight is the least universal at-most covering size for six moduli. -/
theorem isLeast_six : IsLeast {k | HasCoveringSize 6 k} 8 :=
  ⟨fun A hc h2 L _ => IntervalSix.six_upper A hc h2 L,
   fun _ hk => eight_le_of_hasCoveringSize_six hk⟩

theorem erdos_708.variants.g_six (g : ℕ → ℕ) (hg : IsMinCoveringSize g) : g 6 = 8 :=
  (hg 6).unique isLeast_six

end Erdos708

#print axioms Erdos708.isLeast_six
#print axioms IntervalSix.six_integer
