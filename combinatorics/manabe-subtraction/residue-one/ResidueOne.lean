import Pattern

namespace SubtractionGame.ResidueOne

def largeMove (k : Nat) : Nat := 11 * k + 1
def period (k : Nat) : Nat := 11 * k + 4

/-- Entry r of the repeating block, numbered from 1 to p. -/
private def tailEntry (p r : Nat) : Nat :=
  if r = 3 ∨ r = p - 2 then 2 else base r

/-- The prefix ends at p. The next two copies of the tail start at p+1 and 2p+1. -/
private def sample (k n : Nat) : Nat :=
  let p := period k
  if n ≤ p then
    if n = p then 3 else if n = p - 3 ∨ n = p - 2 then 2 else base n
  else if n ≤ 2 * p then tailEntry p (n - p)
  else tailEntry p (n - 2 * p)

/-- The letters of 00011100211, written as conditions on the residue. -/
private theorem base_eq (n : Nat) : base n =
    (if n % 11 = 8 then 2 else if n % 11 ≤ 2 ∨ n % 11 = 6 ∨ n % 11 = 7 then 0 else 1) := by
  unfold base digit
  split <;> grind

/- After unfolding the two rows, the mex rule is a statement about linear
   inequalities and residues modulo 11. It holds for symbolic k and n. -/
set_option maxHeartbeats 2000000 in
private theorem sample_step (k n : Nat) (hk : 1 ≤ k) (hn : n < 3 * period k) :
    sample k n = ThirdMove.step (largeMove k) (sample k) n := by
  simp only [ThirdMove.step, sample, tailEntry, largeMove, period, base_eq, mex] at *
  grind (splits := 1000)

private theorem grundy_eq_sample (k n : Nat) (hk : 1 ≤ k) (hn : n < 3 * period k) :
    ThirdMove.grundy (largeMove k) n = sample k n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [ThirdMove.grundy_eq_step, sample_step k n hk hn]
    have hc : 0 < largeMove k := by unfold largeMove; omega
    unfold ThirdMove.step
    congr 1 <;> split <;> first | rfl | apply ih <;> omega

/-- From the heap after the exceptional 3, a shift of 11k+4 preserves the value. -/
theorem tail_period (k : Nat) (hk : 1 ≤ k) :
    ∀ n, period k + 1 ≤ n →
      ThirdMove.grundy (largeMove k) (n + period k) = ThirdMove.grundy (largeMove k) n := by
  apply ThirdMove.periodic_from_window (by unfold largeMove; omega)
  intro n hlo hhi
  have hcp : largeMove k + 3 = period k := by unfold largeMove period; omega
  rw [grundy_eq_sample k _ hk (by omega), grundy_eq_sample k _ hk (by omega)]
  -- Both positions read the same entry of the repeating row.
  grind [sample]

/-- The only heap with Grundy value 3 for moves 3, 8, and 11k+1 is 11k+4. -/
theorem grundy_eq_three_iff (k n : Nat) (hk : 1 ≤ k) :
    ThirdMove.grundy (largeMove k) n = 3 ↔ n = 11 * k + 4 := by
  change ThirdMove.grundy (largeMove k) n = 3 ↔ n = period k
  have hp : 0 < period k := by unfold period; omega
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n < 3 * period k
    · rw [grundy_eq_sample k n hk hn]
      grind [sample, tailEntry, base_eq]
    · have h := tail_period k hk (n - period k) (by omega)
      rw [Nat.sub_add_cancel (by omega)] at h
      have := ih (n - period k) (by omega)
      omega

/-- No positive period can start at or before the unique 3. Together with
`tail_period`, this gives the least preperiod 11k+5. -/
theorem lower_bound_on_preperiod (k s d : Nat) (hk : 1 ≤ k) (hd : 0 < d)
    (h : ∀ n, s ≤ n →
      ThirdMove.grundy (largeMove k) (n + d) = ThirdMove.grundy (largeMove k) n) :
    period k + 1 ≤ s := by
  apply Classical.byContradiction
  intro hs
  have three := (grundy_eq_three_iff k (period k) hk).2 rfl
  have again := (grundy_eq_three_iff k (period k + d) hk).1 ((h _ (by omega)).trans three)
  change period k + d = period k at again
  omega

/-- Exactly the heaps at or after 11k+5 can serve as the start of a periodic tail. -/
theorem periodic_from_iff (k s : Nat) (hk : 1 ≤ k) :
    (∃ d > 0, ∀ n, s ≤ n →
      ThirdMove.grundy (largeMove k) (n + d) = ThirdMove.grundy (largeMove k) n) ↔
      11 * k + 5 ≤ s := by
  change _ ↔ period k + 1 ≤ s
  constructor
  · rintro ⟨d, hd, h⟩
    exact lower_bound_on_preperiod k s d hk hd h
  · intro hs
    exact ⟨period k, by unfold period; omega,
      fun n hn => tail_period k hk n (Nat.le_trans hs hn)⟩

end SubtractionGame.ResidueOne
