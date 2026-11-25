import Std

namespace Erdos64

/-- Count set bits, stopping when the requested limit is reached. -/
def countBitsUpTo : Nat → Nat → Nat
  | 0, _ => 0
  | k+1, bits => if bits == 0 then 0 else 1 + countBitsUpTo k (bits &&& (bits-1))

def lowestBitIndex (bits : Nat) : Nat := (bits ^^^ (bits &&& (bits-1))).log2

/-- Enumerate both choices for every compatible vertex, maintaining the
candidate set by a single bitwise intersection when a vertex is included. -/
private def maskScan (row : Nat → Nat) (test : Nat → Bool) :
    Nat → Nat → Nat → Bool
  | 0, chosen, _ => test chosen
  | k + 1, chosen, candidates =>
    if candidates = 0 then test chosen
    else if candidates.testBit k then
      let bit := 1 <<< k
      let rest := candidates ^^^ bit
      maskScan row test k chosen rest &&
        maskScan row test k (chosen ||| bit) (rest &&& row k)
    else maskScan row test k chosen candidates

/-- Test the compatible subsets of the first n bits containing a. A one at
position j of row i means that choosing i allows j. -/
def allMasks (n a : Nat) (row : Nat → Nat) (test : Nat → Bool) : Bool :=
  let anchor := 1 <<< a
  let other := ((1 <<< n) - 1) ^^^ anchor
  maskScan row test n anchor (row a &&& other)

private theorem singletonBit (i j : Nat) : (1 <<< i : Nat).testBit j = decide (i = j) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

private theorem sameMask {m chosen : Nat}
    (sub : ∀ i, chosen.testBit i = true → m.testBit i = true)
    (complete : ∀ i, m.testBit i = true → chosen.testBit i = true) : m = chosen := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases hm : m.testBit i <;> cases hc : chosen.testBit i <;> grind

private theorem maskScan_sound {row : Nat → Nat} {test : Nat → Bool} {m : Nat}
    (compat : ∀ i j, i ≠ j → m.testBit i = true → m.testBit j = true →
      (row i).testBit j = true)
    (k chosen candidates : Nat)
    (sub : ∀ i, chosen.testBit i = true → m.testBit i = true)
    (unseen : ∀ i, m.testBit i = true → chosen.testBit i = false →
      i < k ∧ candidates.testBit i = true)
    (h : maskScan row test k chosen candidates = true) : test m = true := by
  induction k generalizing chosen candidates with
  | zero =>
    have eq : m = chosen := sameMask sub (by
      intro i hi
      cases hc : chosen.testBit i with
      | false => have := (unseen i hi hc).1; omega
      | true => rfl)
    simpa [maskScan, eq] using h
  | succ k ih =>
    by_cases empty : candidates = 0
    · have eq := sameMask sub (by
        intro i hi
        cases hc : chosen.testBit i with
        | false => have := (unseen i hi hc).2; simp [empty] at this
        | true => rfl)
      simpa [maskScan, empty, eq] using h
    · by_cases active : candidates.testBit k = true
      · simp only [maskScan, ite_eq_right empty, ite_eq_left active, Bool.and_eq_true] at h
        by_cases present : m.testBit k = true
        · apply ih _ _ ?_ ?_ h.2
          · intro i hi
            simp only [Nat.testBit_or, singletonBit, Bool.or_eq_true, decide_eq_true_eq] at hi
            rcases hi with hi | hi
            · exact sub i hi
            · exact hi ▸ present
          · intro i hi notChosen
            have hc : chosen.testBit i = false := by
              rw [Nat.testBit_or, Bool.or_eq_false_iff] at notChosen
              exact notChosen.1
            have ne : k ≠ i := by
              intro e
              subst i
              simp only [Nat.testBit_or, singletonBit, decide_true, Bool.or_true] at notChosen
              cases notChosen
            obtain ⟨hik,hcan⟩ := unseen i hi hc
            exact ⟨by omega, by rw [Nat.testBit_and, Nat.testBit_xor, singletonBit, decide_eq_false ne, hcan, compat k i ne present hi]; rfl⟩
        · apply ih _ _ sub ?_ h.1
          intro i hi hc
          obtain ⟨hik,hcan⟩ := unseen i hi hc
          have ne : k ≠ i := by grind
          exact ⟨by omega, by rw [Nat.testBit_xor, singletonBit, decide_eq_false ne, hcan]; rfl⟩
      · apply ih _ _ sub ?_ (by simpa [maskScan, empty, active] using h)
        intro i hi hc
        obtain ⟨hik,hcan⟩ := unseen i hi hc
        exact ⟨by grind, hcan⟩

theorem allMasks_sound {n a m : Nat} {row : Nat → Nat} {test : Nat → Bool}
    (checked : allMasks n a row test = true) (anchorBound : a < n) (bound : m < 2^n)
    (hasAnchor : m.testBit a = true)
    (compatible : ∀ i j, i < n → j < n → i ≠ j → m.testBit i = true →
      m.testBit j = true → (row i).testBit j = true) : test m = true := by
  have inRange (i : Nat) (hi : m.testBit i = true) : i < n := by
    apply Classical.byContradiction
    intro h
    have hi' := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le bound
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : n ≤ i)))
    simp [hi] at hi'
  apply maskScan_sound (m := m)
    (fun i j ne hi hj => compatible i j (inRange i hi) (inRange j hj) ne hi hj) n _ _ ?_ ?_ checked
  · intro i hi
    have eq : a = i := by simpa only [singletonBit, decide_eq_true_eq] using hi
    simpa [← eq] using hasAnchor
  · intro i hi hc
    have ne : a ≠ i := by simpa only [singletonBit, decide_eq_false_iff_not] using hc
    have range := inRange i hi
    have pair := compatible a i anchorBound range ne hasAnchor hi
    exact ⟨range, by simp [Nat.one_shiftLeft, ne, range, pair]⟩

end Erdos64
