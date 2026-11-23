import Ramsey556.Lower

namespace Ramsey556.Split17

/-- The first eight vertices form one block. The next four cover every
edge of color one in the second block. Color two marks the missing edges
of the split graph. -/
def smallCoreColoring (n : Nat) : Coloring n where
  edge x y := if (x.val < 8) ↔ (y.val < 8) then
    (if x.val < 12 ∨ y.val < 12 then 1 else 2) else 0
  symm x y := by simp only [iff_comm (a := x.val < 8), or_comm (a := x.val < 12)]

theorem small_core_example (n : Nat) :
    ∃ c : Coloring n, (∀ i j, i ≠ j → (i.val<12 ∨ j.val<12) → c.edge i j=0 ∨ c.edge i j=1) ∧
      (¬ HasC9In c 0) ∧ ¬ HasC9In c 1 := by
  refine ⟨smallCoreColoring n,?_,?_,?_⟩
  · intro i j _ h
    simp only [smallCoreColoring,ite_eq_left h]
    split <;> decide
  · rintro ⟨p,pi,he⟩
    apply sum_ne_one_around_cycle (fun i => if (p i).val < 8 then 1 else 0)
    intro i
    have e := he i
    by_cases h : (p i).val < 8 <;> by_cases t : (p (i+1)).val < 8 <;>
      simp [h,t,smallCoreColoring] at e ⊢ <;> split at e <;> contradiction
  · rintro ⟨p,pi,he⟩
    let side (i : Fin 9) := decide ((p i).val < 8)
    have same (i : Fin 9) : side i = side (i+1) := by
      have e := he i
      by_cases h : (p i).val < 8 <;> by_cases t : (p (i+1)).val < 8 <;> simp_all [side,smallCoreColoring] <;> omega
    have fixed := constant_along_cycle side same
    by_cases zero : (p 0).val < 8
    · have bounds (i) : (p i).val < 8 := by simpa [side,zero] using fixed i
      let v (i : Fin 9) : Fin 8 := ⟨(p i).val,bounds i⟩
      exact no_injection_nine_eight v (fun {_ _} e => pi (Fin.ext (congrArg (fun u : Fin 8 => u.val) e)))
    · have lb (i) : 8 ≤ (p i).val := by simpa [side,zero] using fixed i
      have cover (i) : (p i).val < 12 ∨ (p (i+1)).val < 12 := by
        have e := he i
        by_cases h : (p i).val < 12 <;> by_cases t : (p (i+1)).val < 12 <;>
          simp_all [smallCoreColoring, Nat.not_lt_of_ge (lb i),Nat.not_lt_of_ge (lb (i+1))]
      let slot (i : Fin 9) : Fin 8 := if h : (p i).val < 12 then ⟨(p i).val-8,by omega⟩
        else ⟨4+((p (i+1)).val-8), by have := cover i; omega⟩
      apply no_injection_nine_eight slot
      intro i j eq
      have e := congrArg Fin.val eq
      have li := lb i; have lj := lb j
      have si := lb (i+1); have sj := lb (j+1)
      have ci := cover i; have cj := cover j
      change (slot i).val = (slot j).val at e
      by_cases hi : (p i).val<12 <;> by_cases hj : (p j).val<12 <;> simp [slot,hi,hj] at e
      · exact pi (Fin.ext (by omega))
      · omega
      · omega
      · have add : i+1 = j+1 := pi (Fin.ext (by omega))
        exact (show ∀ i j : Fin 9, i+1=j+1 → i=j by decide) _ _ add

end Ramsey556.Split17
