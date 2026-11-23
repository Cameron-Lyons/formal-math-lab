import Board

namespace Kings

/-- The first half or the last half supplies exactly k ones. -/
private theorem midpoint_sum (k : Nat) (descending : Bool) :
    sumPrefix (midpointBit k descending) (2*k) = k := by
  have count (m : Nat) : sumPrefix (midpointBit k descending) m =
      if descending then min m k else m - k := by
    induction m with
    | zero => cases descending <;> simp [sumPrefix]
    | succ m ih =>
      rw [sumPrefix, ih]
      cases descending <;> by_cases early : m < k <;> simp [midpointBit, early] <;> omega
  rw [count]
  cases descending <;> simp <;> omega

/-- Successive comparisons in one direction give the same comparison
between any two indices in their original order. -/
private theorem order_of_steps {f : Nat → Nat} {n : Nat} (descending : Bool)
    (steps : ∀ i, i+1 < n → if descending then f (i+1) ≤ f i else f i ≤ f (i+1))
    {a b : Nat} (hab : a ≤ b) (hb : b < n) :
    if descending then f b ≤ f a else f a ≤ f b := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst a
    cases descending <;> simp
  | succ b ih =>
    by_cases last : a = b+1
    · subst a
      cases descending <;> simp
    · have prev := ih (by omega) (by omega)
      have step := steps b hb
      cases descending <;> simp only [Bool.false_eq_true, ↓reduceIte] at prev step ⊢ <;> omega

/-- Compare a monotone string with the ideal midpoint string. If the middle
bit is zero, monotonicity forces zeros on the whole zero side, so the actual
string lies below the ideal one. If it is one, the actual string lies above.
Equal sums then force equality at every index. -/
private theorem monotone_profile {f : Nat → Nat} {k : Nat} (hk : 0 < k)
    (descending : Bool) (bits : ∀ i, i < 2*k → f i ≤ 1) (total : sumPrefix f (2*k) = k)
    (steps : ∀ i, i+1 < 2*k → if descending then f (i+1) ≤ f i else f i ≤ f (i+1)) :
    ∀ i, i < 2*k → f i = midpointBit k descending i := by
  have compareAt (i : Nat) (hi : i < 2*k) :
      (f k = 0 → f i ≤ midpointBit k descending i) ∧
      (f k ≠ 0 → midpointBit k descending i ≤ f i) := by
    have bit := bits i hi
    by_cases early : i < k
    · have before := order_of_steps descending steps (a := i) (b := k) (by omega) (by omega)
      cases descending <;> simp [midpointBit, early] at before ⊢ <;> omega
    · have after := order_of_steps descending steps (a := k) (b := i) (by omega) hi
      cases descending <;> simp [midpointBit, early] at after ⊢ <;> omega
  have sameSum := total.trans (midpoint_sum k descending).symm
  by_cases middle : f k = 0
  · exact eq_at_of_sum_eq (fun i hi => (compareAt i hi).1 middle) sameSum
  · exact fun i hi => (eq_at_of_sum_eq (fun j hj => (compareAt j hj).2 middle) sameSum.symm i hi).symm

private theorem midpoint_fall {f : Nat → Nat} {k : Nat} (hk : 0 < k)
    (profile : ∀ i, i < 2*k → f i = midpointBit k true i) :
    f (k-1+1) < f (k-1) := by
  rw [profile (k-1+1) (by omega), profile (k-1) (by omega)]
  simp [midpointBit, show ¬k-1+1 < k by omega, show k-1 < k by omega]

/-- Diagonal nonattacks force two balanced offset profiles to switch, in
opposite directions, at their common midpoint. -/
theorem classifyProfiles {k : Nat} (hk : 0 < k) (h v : Nat → Nat)
    (hb : ∀ i, i < 2*k → h i ≤ 1) (vb : ∀ i, i < 2*k → v i ≤ 1)
    (hs : sumPrefix h (2*k) = k) (vs : sumPrefix v (2*k) = k)
    (noRise : ∀ i j, i+1 < 2*k → j+1 < 2*k →
      h i < h (i+1) → v j < v (j+1) → False)
    (noFall : ∀ i j, i+1 < 2*k → j+1 < 2*k →
      h (i+1) < h i → v (j+1) < v j → False) :
    ((∀ i, i < 2*k → h i = midpointBit k false i) ∧
     (∀ i, i < 2*k → v i = midpointBit k true i)) ∨
    ((∀ i, i < 2*k → h i = midpointBit k true i) ∧
     (∀ i, i < 2*k → v i = midpointBit k false i)) := by
  by_cases rise : ∃ i, i+1 < 2*k ∧ h i < h (i+1)
  · obtain ⟨r, hr, rising⟩ := rise
    -- A rise in h forbids every rise in v. The resulting fall in v forbids every fall in h.
    have vDown := monotone_profile hk true vb vs (fun j hj => Nat.le_of_not_gt (noRise r j hr hj rising))
    have hUp := monotone_profile hk false hb hs (fun i hi => Nat.le_of_not_gt
      (fun fall => noFall i (k-1) hi (by omega) fall (midpoint_fall hk vDown)))
    exact Or.inl ⟨hUp, vDown⟩
  · -- With no rise, h falls at its midpoint. Now v can only rise.
    have hDown := monotone_profile hk true hb hs (fun i hi =>
      Nat.le_of_not_gt (fun step => rise ⟨i, hi, step⟩))
    have vUp := monotone_profile hk false vb vs (fun j hj => Nat.le_of_not_gt
      (noFall (k-1) j (by omega) hj (midpoint_fall hk hDown)))
    exact Or.inr ⟨hDown, vUp⟩

end Kings
