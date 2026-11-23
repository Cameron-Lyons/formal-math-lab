import Board

namespace Kings

/-- Adding t pairs of adjacent columns to a prefix adds at most t kings. -/
private theorem appendPairs (f : Nat → Nat) (adj : ∀ j, f j + f (j+1) ≤ 1) (a t : Nat) :
    sumPrefix f (a+2*t) ≤ sumPrefix f a + t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have lastPair := adj (a+2*t)
    rw [show a+2*(t+1) = (a+2*t)+1+1 by omega]
    simp only [sumPrefix]
    omega

/-- Add the m inequalities f j + f (j+1) ≤ 1 for j = 0, …, m−1.
Every interior column is counted twice and each end column once. -/
private theorem countNeighbors (f : Nat → Nat) (adj : ∀ j, f j + f (j+1) ≤ 1) (m : Nat) :
    2 * sumPrefix f m + f m ≤ m + f 0 := by
  induction m with
  | zero => simp [sumPrefix]
  | succ m ih =>
    have next := adj m
    rw [sumPrefix]
    omega

/-- A two-row strip with s kings needs at least 2s−1 columns. -/
theorem spacingBound (f : Nat → Nat) (adj : ∀ j, f j + f (j+1) ≤ 1) (m : Nat) :
    2 * sumPrefix f m ≤ m + 1 := by
  have count := countNeighbors f adj m
  have first := adj 0
  omega

/-- Removing any even-indexed column 2i from a strip of length 2t+1 leaves
i pairs on its left and t−i pairs on its right. Thus a strip with t+1 kings
must have a king in column 2i. -/
theorem spacingForced (f : Nat → Nat) (adj : ∀ j, f j + f (j+1) ≤ 1) (t : Nat)
    (full : sumPrefix f (2*t+1) = t+1) (i : Nat) (hi : i ≤ t) : f (2*i) = 1 := by
  have leftPairs := appendPairs f adj 0 i
  have rightPairs := appendPairs f adj (2*i+1) (t-i)
  simp only [Nat.zero_add, sumPrefix] at leftPairs
  rw [show 2*i+1+2*(t-i) = 2*t+1 by omega, full, sumPrefix] at rightPairs
  have atMostOne := adj (2*i)
  omega

private theorem exists_positive {f : Nat → Nat} {n : Nat} (h : 0 < sumPrefix f n) :
    ∃ i, i < n ∧ 0 < f i := by
  induction n with
  | zero => simp [sumPrefix] at h
  | succ n ih =>
    by_cases last : 0 < f n
    · exact ⟨n, by omega, last⟩
    · rw [sumPrefix] at h
      obtain ⟨i, hi, pos⟩ := ih (by omega)
      exact ⟨i, by omega, pos⟩

/-- With at least two rows and a positive quota in every row and column,
a nonattacking placement needs a board of side at least 4k. -/
theorem lowerBound {b : Board} {n k : Nat} (p : IsPlacement b n k)
    (hn : 2 ≤ n) (hk : 1 ≤ k) : 4*k ≤ n := by
  -- Pick a king in column 1 (the second column) and a pair of rows containing it.
  have col := p.colCount 1 (by omega)
  obtain ⟨s, hs, king⟩ := exists_positive (f := fun r => b r 1) (n := n) (by omega)
  obtain ⟨r, hr, occupied⟩ : ∃ r, r+1 < n ∧ 0 < b r 1 + b (r+1) 1 := by
    cases s with
    | zero => exact ⟨0, by omega, by omega⟩
    | succ s => exact ⟨s, hs, by omega⟩

  let f := fun c => b r c + b (r+1) c
  have adj (j : Nat) : f j + f (j+1) ≤ 1 := by
    have block := p.block r j
    dsimp [f]
    omega
  have count : sumPrefix f n = 2*k := by
    dsimp [f]
    rw [sumPrefix_add, p.rowCount _ (by omega), p.rowCount _ hr]
    omega

  -- The first column is empty. Each of the 2k occupied columns therefore
  -- has its own empty left neighbor. Together they account for 4k columns.
  change 0 < f 1 at occupied
  have firstPair : f 0 + f 1 ≤ 1 := adj 0
  have firstEmpty : f 0 = 0 := by omega
  have room := countNeighbors f adj n
  omega

end Kings
