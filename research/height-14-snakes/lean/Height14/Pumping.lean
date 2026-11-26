import Height14.Certificate

namespace Height14.Cert

private theorem shift_mono {v w : Nat} (c : Nat) (h : v ≤ w) :
    shift c v ≤ shift c w := by
  unfold shift
  split <;> split <;> omega

private theorem shift_comm (c d v : Nat) :
    shift c (shift d v) = shift d (shift c v) := by
  by_cases hv : v = 0
  · simp [shift, hv]
  · simp [shift, hv, Nat.add_comm d c, Nat.add_assoc]

private theorem back_entry (g : Graph) (r i : Nat) (a : Array Nat)
    (hi : i < (layer g r).edges.size) :
    (back g r a).getD i 0 =
      max (edgeValue a (dest g r i false) false) (edgeValue a (dest g r i true) true) := by
  simp [back, dest, Array.getD, hi]

/-- Each legal continuation is bounded by the larger of the two choices. -/
theorem back_get (g : Graph) (r i : Nat) (b : Bool) (a : Array Nat)
    (hi : i < (layer g r).edges.size) :
    edgeValue a (dest g r i b) b ≤ (back g r a).getD i 0 := by
  rw [back_entry _ _ _ _ hi]
  cases b
  · exact Nat.le_max_left ..
  · exact Nat.le_max_right ..

private theorem edge_le_shift {a d : Array Nat} {c : Nat}
    (h : ∀ i, a.getD i 0 ≤ shift c (d.getD i 0)) (j : Nat) (b : Bool) :
    edgeValue a j b ≤ shift c (edgeValue d j b) := by
  by_cases hj : j = 0
  · simp [edgeValue, hj, shift]
  · simp only [edgeValue, ite_eq_right hj]
    rw [shift_comm c b.toNat]
    exact shift_mono b.toNat (h _)

private theorem back_le_shift (g : Graph) (r : Nat) {a d : Array Nat} {c : Nat}
    (h : ∀ i, a.getD i 0 ≤ shift c (d.getD i 0)) (i : Nat) :
    (back g r a).getD i 0 ≤ shift c ((back g r d).getD i 0) := by
  by_cases hi : i < (layer g r).edges.size
  · rw [back_entry _ _ _ _ hi]
    apply Nat.max_le.mpr
    exact ⟨Nat.le_trans (edge_le_shift h _ false) (shift_mono c (back_get _ _ _ _ _ hi)),
           Nat.le_trans (edge_le_shift h _ true) (shift_mono c (back_get _ _ _ _ _ hi))⟩
  · simp [back, Array.getD, hi]

/-- Appending the same number of squares to both backward calculations
preserves the checked upper inequality. Their row phases agree since
the two widths differ by six whole columns. -/
private theorem later (k i : Nat) :
    (vals graph (644+k)).getD i 0 ≤ shift 52 ((vals graph (560+k)).getD i 0) := by
  induction k generalizing i with
  | zero => exact period i
  | succ k ih =>
    have hp : phase (644+k+1) = phase (560+k+1) := by
      simp only [phase]; congr 2 <;> omega
    change (back graph (phase (644+k+1)) (vals graph (644+k))).getD i 0 ≤
      shift 52 ((back graph (phase (560+k+1)) (vals graph (560+k))).getD i 0)
    rw [hp]
    exact back_le_shift _ _ ih i

theorem upperStart (n : Nat) : (vals graph (14*n)).getD 0 0 ≤ formula n + 1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n ≤ 46
    · exact base h
    · let m := n - 6
      have hn : n = m + 6 := by dsimp [m]; omega
      have hm : 40 ≤ m := by omega
      have smaller := ih m (by omega)
      have bound := later (14*m-560) 0
      have ha : 644 + (14*m-560) = 14*n := by omega
      have hb : 560 + (14*m-560) = 14*m := by omega
      rw [ha, hb] at bound
      have hf : formula n = formula m + 52 := hn ▸ formula_add_six (n := m) (by omega)
      unfold shift at bound
      split at bound <;> omega

end Height14.Cert
