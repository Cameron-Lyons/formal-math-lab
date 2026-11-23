import Board

namespace Kings

/-- The row and column of a cell split into tile indices (division by two)
and offsets within that tile (remainders modulo two). The two profiles
select a single corner of each tile. -/
def pattern (k : Nat) (flip : Bool) : Board := fun r c =>
  if r < 4*k ∧ c < 4*k ∧
      r % 2 = midpointBit k (!flip) (c/2) ∧ c % 2 = midpointBit k flip (r/2)
    then 1 else 0

private theorem prefix_join (f : Nat → Nat) (a b : Nat) :
    sumPrefix f (a+b) = sumPrefix f a + sumPrefix (fun i => f (a+i)) b := by
  induction b with
  | zero => simp [sumPrefix]
  | succ b ih =>
    change sumPrefix f (a+b) + f (a+b) = _ + (_ + _)
    rw [ih, Nat.add_assoc]

/-- Pair neighboring cells, then match the j-th pair in the left half with
the j-th pair in the right half. -/
private theorem sum_by_quartets (f : Nat → Nat) (k : Nat) :
    sumPrefix f (4*k) = sumPrefix (fun j =>
      (f (2*j) + f (2*j+1)) + (f (2*(k+j)) + f (2*(k+j)+1))) k := by
  let pair := fun j => f (2*j) + f (2*j+1)
  calc
    _ = sumPrefix pair (2*k) := by
      rw [show 4*k = 2*(2*k) by omega, ← sum_pairs]
    _ = sumPrefix (fun j => pair j + pair (k+j)) k := by
      rw [show 2*k = k+k by omega, prefix_join, ← sumPrefix_add]

private theorem pattern_rows (k : Nat) (flip : Bool) (r : Nat) (hr : r < 4*k) :
    sumPrefix (pattern k flip r) (4*k) = k := by
  rw [sum_by_quartets]
  refine Eq.trans ?_ (sum_ones k)
  apply sumPrefix_congr
  intro j hj
  -- In the half selected by the row parity, one king appears in every column pair.
  cases flip <;> by_cases firstHalf : r/2 < k <;> by_cases even : r%2 = 0 <;>
    simp (disch := omega) [pattern, midpointBit, *, ite_eq_left, ite_eq_right]

/-- Transposing the board interchanges rising and descending profiles. -/
private theorem pattern_swap (k : Nat) (flip : Bool) (r c : Nat) :
    pattern k flip r c = pattern k (!flip) c r := by
  simp only [pattern, Bool.not_not]
  ac_rfl

private theorem same_cell {k r c s d : Nat} {flip : Bool}
    (pr : pattern k flip r c ≠ 0) (ps : pattern k flip s d ≠ 0)
    (hr : r ≤ s+1) (hs : s ≤ r+1) (hc : c ≤ d+1) (hd : d ≤ c+1) :
    r = s ∧ c = d := by
  simp [pattern] at pr ps
  obtain ⟨_, _, row₁, col₁⟩ := pr
  obtain ⟨_, _, row₂, col₂⟩ := ps
  -- In the same row half, both columns have the same parity. In the
  -- same column half, both rows have the same parity. A pair crossing
  -- both midlines would lie in the four central cells, all of which are empty.
  cases flip <;> simp [midpointBit] at row₁ col₁ row₂ col₂ <;>
    split at row₁ <;> split at col₁ <;> split at row₂ <;> split at col₂ <;> omega

private theorem pattern_le_one (k : Nat) (flip : Bool) (r c : Nat) :
    pattern k flip r c ≤ 1 := by
  change (if _ then 1 else 0) ≤ 1
  split <;> decide

private theorem pattern_blocks (k : Nat) (flip : Bool) (r c : Nat) :
    pattern k flip r c + pattern k flip r (c+1) +
      pattern k flip (r+1) c + pattern k flip (r+1) (c+1) ≤ 1 := by
  -- Two occupied corners would have to be the same cell.
  have bound := pattern_le_one k flip
  grind [→ same_cell]

theorem pattern_isPlacement (k : Nat) (flip : Bool) : IsPlacement (pattern k flip) (4*k) k where
  outside r c h := by
    apply ite_eq_right
    omega
  rowCount := pattern_rows k flip
  colCount c hc := by
    simpa only [pattern_swap k flip] using pattern_rows k (!flip) c hc
  block := pattern_blocks k flip

theorem patterns_ne {k : Nat} (hk : 0 < k) : pattern k false ≠ pattern k true := by
  intro same
  have h := congrFun (congrFun same 1) 0
  simp (disch := omega) [pattern, midpointBit, *, ite_eq_left] at h

end Kings
