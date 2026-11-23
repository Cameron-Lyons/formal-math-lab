import Window

/-!
# The only 3 is at heap 11k+10

Put q = 11(k+1). Write the candidate values in three rows of width q,
starting at heap zero. With A = 00011100211, row j reads the repeated word
A shifted left by j digits. Make just these changes (offsets start at zero):

| Row | Changes |
| --- | --- |
| 0 | Put 2 at q−4 and 3 at q−1. |
| 1 | Put 2 at offset 2. |
| 2 | Put 2 at offset 1. |

The moves read columns r−3 and r−8 in the same row and r+4 in the preceding
row, wrapping at the edges. Divide each row into blocks of 11. In an interior
block, these lookups depend only on the row and residue. In an edge block,
they also depend on the distance to that edge. Since q ≥ 22, the opposite
edge contributes no exceptional digit to those lookups. Thus it suffices to
check k=2, whose rows have one first, one interior, and one last block.
`Window` proves the reduction and checks all 99 entries by computation.

Rows 1 and 2 agree after a shift of q−1 starting at heap q. This gives
more than q−4 consecutive matches, enough to determine the whole tail.
The single 3 in row 0 therefore never recurs.
-/

namespace SubtractionGame

/-- Strong induction turns the local mex check into the actual Grundy sequence. -/
theorem grundy_eq_sample (k n : Nat) (hk : 1 ≤ k) (hn : n < 3 * period k) :
    grundy k n = sample k n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [grundy_eq_step, window_step k n hk hn]
    have hc : 0 < largeMove k := by unfold largeMove; omega
    unfold step
    congr 1 <;> split <;> first | rfl | apply ih <;> omega

private theorem base_lt_three (n : Nat) : base n < 3 := by
  unfold base digit
  split <;> decide

/-- Two equal windows begin at p+1 and 2p+1, where p = 11k+10. -/
theorem tail_period (k : Nat) (hk : 1 ≤ k) :
    ∀ n, period k + 1 ≤ n → grundy k (n + period k) = grundy k n := by
  apply periodic_from_window (hk := hk)
  intro n hlo hhi
  have hcp : largeMove k + 3 = period k := by unfold largeMove period; omega
  rw [grundy_eq_sample k _ hk (by omega), grundy_eq_sample k _ hk (by omega)]
  have seam : digit 0 = digit 1 := rfl
  grind [sample, base, largeMove, period]

/-- For every positive k, the value 3 occurs precisely at heap size 11k+10. -/
theorem grundy_eq_three_iff (k n : Nat) (hk : 1 ≤ k) :
    grundy k n = 3 ↔ n = 11 * k + 10 := by
  change grundy k n = 3 ↔ n = period k
  have hp : 0 < period k := by unfold period; omega
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n < 3 * period k
    · rw [grundy_eq_sample k n hk hn]
      grind [sample, base_lt_three]
    · have h := tail_period k hk (n - period k) (by omega)
      rw [Nat.sub_add_cancel (by omega)] at h
      have hsmall := ih (n - period k) (by omega)
      omega

private theorem reduce_tail (k t : Nat) (hk : 1 ≤ k) :
    grundy k (period k + 1 + t) = grundy k (period k + 1 + t % period k) := by
  let p := period k
  have drop (a j : Nat) : grundy k (p + 1 + a + j * p) = grundy k (p + 1 + a) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.succ_mul, ← Nat.add_assoc, tail_period k hk _ (by omega), ih]
  simpa [p, Nat.mul_comm, Nat.mod_add_div, Nat.add_assoc] using drop (t % p) (t / p)

/-- The prefix consists of k base words followed by 00011102213. -/
theorem prefix_formula (k n : Nat) (hk : 1 ≤ k) (hn : n ≤ period k) :
    grundy k n = if n = period k then 3 else if n = largeMove k then 2 else base n := by
  rw [grundy_eq_sample k _ hk (by unfold period at *; omega)]
  grind [sample, period, largeMove]

/-- In each tail block, read the base word starting at position one and
change its digit at offset two to 2. This spells 0021100211 followed by k
copies of the base word. -/
theorem tail_formula (k t : Nat) (hk : 1 ≤ k) :
    grundy k (period k + 1 + t) =
      if t % period k = 2 then 2 else base (t % period k + 1) := by
  rw [reduce_tail k t hk]
  generalize hr : t % period k = r
  have hp : 20 < period k := by unfold period; omega
  have hlt : r < period k := hr ▸ Nat.mod_lt t (by omega)
  rw [grundy_eq_sample k _ hk (by omega)]
  grind [sample, base, largeMove, period]

/-- Every positive eventual period must start strictly after the unique 3. -/
theorem lower_bound_on_preperiod (k s d : Nat) (hk : 1 ≤ k) (hd : 0 < d)
    (h : ∀ n, s ≤ n → grundy k (n + d) = grundy k n) : period k + 1 ≤ s := by
  apply Classical.byContradiction
  intro hs
  have h₃ := (grundy_eq_three_iff k (period k) hk).2 rfl
  have heq := (grundy_eq_three_iff k (period k + d) hk).1 ((h _ (by omega)).trans h₃)
  change period k + d = period k at heq
  omega

theorem not_purely_periodic (k : Nat) (hk : 1 ≤ k) :
    ¬ ∃ d, 0 < d ∧ ∀ n, grundy k (n + d) = grundy k n := by
  rintro ⟨d, hd, h⟩
  have := lower_bound_on_preperiod k 0 d hk hd (fun n _ => h n)
  omega

private theorem base_two_iff (r : Nat) : base (r + 1) = 2 ↔ r % 11 = 7 := by
  unfold base digit
  split <;> simp_all <;> omega

/-- Two tail entries ten apart both equal 2 exactly once in each block. -/
private theorem pair_of_twos (k t : Nat) (hk : 1 ≤ k) :
    grundy k (period k + 1 + t) = 2 ∧ grundy k (period k + 1 + (t + 10)) = 2 ↔
    t % period k = period k - 3 := by
  have two (x : Nat) : grundy k (period k + 1 + x) = 2 ↔
      x % period k = 2 ∨ (x % period k) % 11 = 7 := by
    rw [tail_formula k x hk]
    split <;> rename_i hr
    · simp [hr]
    · simp [hr, base_two_iff]
  rw [two, two, ← Nat.mod_add_mod t (period k) 10]
  generalize hr : t % period k = r
  have hp : 20 < period k := by unfold period; omega
  have hlt : r < period k := hr ▸ Nat.mod_lt t (by omega)
  by_cases h : r + 10 < period k
  · rw [Nat.mod_eq_of_lt h]
    unfold period at *
    omega
  · rw [Nat.mod_eq_sub_mod (by omega : period k ≤ r + 10),
      Nat.mod_eq_of_lt (by omega : r + 10 - period k < period k)]
    unfold period at *
    omega

/-- Every eventual period is a multiple of 11k+10. Together with `tail_period`
this identifies the least positive eventual period. -/
theorem period_dvd_eventual_period (k s d : Nat) (hk : 1 ≤ k)
    (h : ∀ n, s ≤ n → grundy k (n + d) = grundy k n) : period k ∣ d := by
  let p := period k
  let t := s * p + (p - 3)
  have hp : 20 < p := by dsimp [p, period]; omega
  have hts : s ≤ p + 1 + t := by
    have := Nat.le_mul_of_pos_right s (by omega : 0 < p)
    dsimp [t]
    omega
  have ht : t % p = p - 3 := by
    simp [t, Nat.add_mod, Nat.mod_eq_of_lt (show p - 3 < p by omega)]
  have ⟨first, second⟩ := (pair_of_twos k t hk).2 ht
  have hu := (pair_of_twos k (t + d) hk).1 (by
    constructor
    · simpa only [← Nat.add_assoc] using (h _ hts).trans first
    · rw [show period k + 1 + (t + d + 10) = (period k + 1 + (t + 10)) + d by omega]
      exact (h _ (by change s ≤ p + 1 + (t + 10); omega)).trans second)
  apply Nat.dvd_of_mod_eq_zero
  simpa using Nat.sub_mod_eq_zero_of_mod_eq (hu.trans ht.symm)

end SubtractionGame
