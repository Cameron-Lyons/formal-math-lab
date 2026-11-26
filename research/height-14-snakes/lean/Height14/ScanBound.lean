import Height14.Pumping
import Height14.Refinement
import Height14.Cut

namespace Height14.Cert

/-- Any complete geometric scan follows table edges. Reading the score bound
    backwards gives an upper bound for its number of occupied squares. -/
theorem scanBound (g : Graph) (rows : ∀ r, GoodRow g r) (ends : GoodEnds g)
    (w : Nat) (p : Nat → Profile) (fill : Nat → Bool)
    (start : p 0 = Profile.empty) (finish : (p (14*w)).accept = true)
    (step : ∀ t, (p t).change (Ranked.row t) (fill t) = some (p (t+1))) :
    (List.range (14*w)).countP fill + 1 ≤ (vals g (14*w)).getD 0 0 := by
  let count t := (List.range t).countP fill
  have count_succ (t : Nat) : count (t+1) = count t + (fill t).toNat := by
    cases hb : fill t <;> simp [count, List.range_succ, List.countP_append, hb]
  have bound (left t i : Nat) (ht : t + left = 14*w)
      (hi : i < (layer g (t%14)).keys.size)
      (hp : p t = decode ((layer g (t%14)).keys.getD i 0)) :
      0 < (vals g left).getD i 0 ∧
      count (14*w) + 1 ≤ count t + (vals g left).getD i 0 := by
    induction left generalizing t i with
    | zero =>
      have he : t = 14*w := by omega
      have hr : t%14 = 0 := by omega
      rw [hr] at hp hi
      have ok := finish
      rw [←he,hp,ends.2.2 i hi] at ok
      have endval : (vals g 0).getD i 0 = 1 := by
        simpa [vals, initial, Array.getD, hi] using congrArg Bool.toNat ok
      rw [endval,he]
      omega
    | succ k ih =>
      let r := Ranked.row t
      obtain ⟨sizes, states⟩ := rows r
      have move := states i hi (fill t)
      change (decode ((layer g (t%14)).keys.getD i 0)).change (Ranked.row t) _ = _ at move
      change (layer g (t%14)).keys.size = (layer g (t%14)).edges.size at sizes
      rw [←hp,step] at move
      let j := dest g (t%14) i (fill t)
      change some (p (t+1)) = (if 0 < j ∧ j-1 < (layer g ((t%14+1)%14)).keys.size
        then some (decode ((layer g ((t%14+1)%14)).keys.getD (j-1) 0)) else none) at move
      split at move
      next hj =>
        have hr : (t%14+1)%14 = (t+1)%14 := by omega
        obtain ⟨positive, next⟩ := ih (t+1) (j-1) (by omega) (hr ▸ hj.2)
          (hr ▸ Option.some.inj move)
        have edge := back_get g (t%14) i (fill t) (vals g k) (sizes ▸ hi)
        change edgeValue _ j _ ≤ _ at edge
        have phase_eq : phase (k+1) = t%14 := by unfold phase; omega
        have recurrence : (vals g (k+1)).getD i 0 = (back g (t%14) (vals g k)).getD i 0 := by
          simp only [vals,phase_eq]
        rw [←recurrence] at edge
        simp only [edgeValue, shift, ite_eq_right (Nat.ne_of_gt hj.1),
          ite_eq_right (Nat.ne_of_gt positive)] at edge
        rw [count_succ] at next
        omega
      next => contradiction
  have b := bound (14*w) 0 0 (by omega) ends.1 (start.trans ends.2.1.symm)
  simpa [count] using b.2

end Height14.Cert
