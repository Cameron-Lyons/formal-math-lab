import Pattern

namespace SubtractionGame

/-- Read a legal option, using the same out-of-range value as `step`. -/
private def readAt (k n d : Nat) := if d ≤ n then sample k (n - d) else 4

set_option maxHeartbeats 2000000 in
/-- Match columns with the same residue. If either lies in the first or last
block of 11, their distances from that edge must also agree. This preserves
the current entry (d = 0) and each move, including whether it is legal. -/
private theorem readAt_eq (k j r s : Nat)
    (hk : 1 ≤ k) (hj : j < 3) (hr : r < period k + 1) (hs : s < 33)
    (hmod : r % 11 = s % 11)
    (hleft : r = s ∨ 11 ≤ r ∧ 11 ≤ s)
    (hright : r + 33 = s + (period k + 1) ∨ r + 11 < period k + 1 ∧ s + 11 < 33)
    (d e : Nat) (hd : (d = e ∧ d ≤ 8) ∨ (d = largeMove k ∧ e = 29)) :
    readAt k (j * (period k + 1) + r) d = readAt 2 (j * 33 + s) e := by
  have rows : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases rows with rfl | rfl | rfl <;> rcases hd with ⟨rfl, hd⟩ | ⟨rfl, rfl⟩
  all_goals simp only [readAt, sample, period, largeMove, base, Nat.reduceMul,
    Nat.reduceAdd, Nat.zero_mul, Nat.zero_add, Nat.one_mul] at *
  all_goals grind (splits := 256)

/-- At k = 2 each row has one first, one middle, and one last block. -/
private theorem check_width_33 : ∀ m : Fin 99, sample 2 m = step 2 (sample 2) m := by
  decide

/-- The candidate satisfies the mex recurrence throughout the first three rows. -/
theorem first_three_rows (k n : Nat) (hk : 1 ≤ k) (hn : n < 3 * (period k + 1)) :
    sample k n = step k (sample k) n := by
  let q := period k + 1
  have hq : 22 ≤ q := by dsimp [q, period]; omega
  let j := n / q
  let r := n % q
  have hj : j < 3 := (Nat.div_lt_iff_lt_mul (by omega : 0 < q)).2 hn
  have hr : r < q := Nat.mod_lt n (by omega)
  have hn' : n = j * q + r := by simpa [j, r, Nat.mul_comm] using (Nat.div_add_mod n q).symm
  -- Keep the two edge blocks. Send every interior block to the middle one.
  obtain ⟨s, hs, hmod, hl, he⟩ : ∃ s < 33, r % 11 = s % 11 ∧
      (r = s ∨ 11 ≤ r ∧ 11 ≤ s) ∧ (r + 33 = s + q ∨ r + 11 < q ∧ s + 11 < 33) := by
    refine ⟨if r < 11 then r else if r + 11 < q then 11 + r % 11 else r + 33 - q, ?_⟩
    dsimp [q, period] at *
    grind
  have move := readAt_eq k j r s hk hj hr hs hmod hl he
  have entry := move 0 0 (Or.inl ⟨rfl, by decide⟩)
  simp only [readAt, Nat.zero_le, ite_true, Nat.sub_zero] at entry
  rw [hn', entry]
  change sample 2 (j * 33 + s) = mex (readAt k _ 3) (readAt k _ 8) (readAt k _ (largeMove k))
  rw [move 3 3 (Or.inl ⟨rfl, by decide⟩), move 8 8 (Or.inl ⟨rfl, by decide⟩),
      move (largeMove k) 29 (Or.inr ⟨rfl, rfl⟩)]
  exact check_width_33 ⟨j * 33 + s, by omega⟩

theorem window_step (k n : Nat) (hk : 1 ≤ k) (hn : n < 3 * period k) :
    sample k n = step k (sample k) n :=
  first_three_rows k n hk (by omega)

end SubtractionGame
