import Std

namespace SubtractionGame

/-- The third move in the game with parameter `k`. -/
def largeMove (k : Nat) : Nat := 11 * k + 7

/-- The least natural number missing from three entries. The value 4 can stand
for an illegal move since three entries can only have mex 0, 1, 2, or 3. -/
def mex (a b c : Nat) : Nat :=
  if a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 then 0
  else if a ≠ 1 ∧ b ≠ 1 ∧ c ≠ 1 then 1
  else if a ≠ 2 ∧ b ≠ 2 ∧ c ≠ 2 then 2
  else 3

theorem mex_spec (a b c : Nat) :
    (mex a b c ≠ a ∧ mex a b c ≠ b ∧ mex a b c ≠ c) ∧
      (∀ j < mex a b c, j = a ∨ j = b ∨ j = c) := by
  unfold mex
  repeat' split
  all_goals constructor
  all_goals first | omega | (intro j hj; omega)

/-- One evaluation of the subtraction recurrence for a putative value function. -/
def step (k : Nat) (f : Nat → Nat) (n : Nat) : Nat :=
  mex (if 3 ≤ n then f (n - 3) else 4)
      (if 8 ≤ n then f (n - 8) else 4)
      (if largeMove k ≤ n then f (n - largeMove k) else 4)

/-- Grundy value of a single heap. -/
def grundy (k n : Nat) : Nat :=
  mex (if 3 ≤ n then grundy k (n - 3) else 4)
      (if 8 ≤ n then grundy k (n - 8) else 4)
      (if largeMove k ≤ n then grundy k (n - largeMove k) else 4)
termination_by n
decreasing_by
  all_goals try unfold largeMove at *
  all_goals omega

theorem grundy_eq_step (k n : Nat) : grundy k n = step k (grundy k) n := by
  rw [grundy]
  rfl

/-- A one-move follower of heap `n` has value `v`. -/
def reachableValue (k n v : Nat) : Prop :=
  ∃ d, (d = 3 ∨ d = 8 ∨ d = largeMove k) ∧ d ≤ n ∧ v = grundy k (n - d)

theorem grundy_lt_four (k n : Nat) : grundy k n < 4 := by
  rw [grundy_eq_step]
  have bound (a b c : Nat) : mex a b c < 4 := by
    unfold mex
    repeat' split
    all_goals decide
  exact bound _ _ _

/-- The recurrence agrees with the game-theoretic definition using only legal moves. -/
theorem grundy_spec (k n : Nat) :
    ¬reachableValue k n (grundy k n) ∧ ∀ v < grundy k n, reachableValue k n v := by
  let value (d : Nat) := if d ≤ n then grundy k (n - d) else 4
  have eqMex : grundy k n = mex (value 3) (value 8) (value (largeMove k)) :=
    grundy_eq_step k n
  have ⟨absent, below⟩ := mex_spec (value 3) (value 8) (value (largeMove k))
  rw [← eqMex] at absent below
  have legal (d v : Nat) (hv : v < 4) :
      v = value d ↔ d ≤ n ∧ v = grundy k (n - d) := by
    by_cases hd : d ≤ n <;> simp [value, hd] <;> omega
  constructor
  · rintro ⟨d, hd, hn, heq⟩
    have he := (legal d _ (grundy_lt_four k n)).mpr ⟨hn, heq⟩
    rcases hd with rfl | rfl | rfl
    · exact absent.1 he
    · exact absent.2.1 he
    · exact absent.2.2 he
  · intro v hv
    have small := Nat.lt_trans hv (grundy_lt_four k n)
    rcases below v hv with h | h | h
    · exact ⟨3, Or.inl rfl, (legal 3 v small).mp h⟩
    · exact ⟨8, Or.inr (Or.inl rfl), (legal 8 v small).mp h⟩
    · exact ⟨largeMove k, Or.inr (Or.inr rfl), (legal _ v small).mp h⟩

/-- Equal windows of length equal to the largest move propagate to the right. -/
theorem periodic_from_window {k q p : Nat}
    (h : ∀ n, q ≤ n → n < q + largeMove k → grundy k (n + p) = grundy k n)
    (hk : 1 ≤ k) : ∀ n, q ≤ n → grundy k (n + p) = grundy k n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hqn
    by_cases hn : n < q + largeMove k
    · exact h n hqn hn
    have hmax : 8 ≤ largeMove k := by unfold largeMove; omega
    have shift (d : Nat) (hd : 0 < d) (hle : d ≤ largeMove k) :
        grundy k (n + p - d) = grundy k (n - d) := by
      rw [show n + p - d = (n - d) + p by omega]
      exact ih _ (by omega) (by omega)
    rw [grundy_eq_step k (n + p), grundy_eq_step k n]
    simp (disch := omega) only [step, ite_eq_left]
    rw [shift 3 (by decide) (by omega), shift 8 (by decide) hmax,
        shift (largeMove k) (by omega) (Nat.le_refl _)]

end SubtractionGame
