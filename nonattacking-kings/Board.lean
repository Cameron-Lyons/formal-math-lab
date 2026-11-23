import Std

/-! A board is indexed from zero and extended by zeros outside its square.
The block inequality says precisely that every 2 × 2 square contains at most
one king. Every pair of attacking squares belongs to such a square. -/
namespace Kings

abbrev Board := Nat → Nat → Nat

/-- Sum of the entries at indices 0 through m−1. -/
def sumPrefix (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => sumPrefix f i + f i

structure IsPlacement (b : Board) (n k : Nat) : Prop where
  outside : ∀ r c, n ≤ r ∨ n ≤ c → b r c = 0
  rowCount : ∀ r, r < n → sumPrefix (b r) n = k
  colCount : ∀ c, c < n → sumPrefix (fun r => b r c) n = k
  block : ∀ r c, b r c + b r (c+1) + b (r+1) c + b (r+1) (c+1) ≤ 1

theorem sumPrefix_add (f g : Nat → Nat) (m : Nat) :
    sumPrefix (fun i => f i + g i) m = sumPrefix f m + sumPrefix g m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [sumPrefix, ih]; omega

/-- Group an even-length sum into pairs of consecutive entries. -/
theorem sum_pairs (f : Nat → Nat) (m : Nat) :
    sumPrefix (fun i => f (2*i) + f (2*i+1)) m = sumPrefix f (2*m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change sumPrefix _ m + _ = _
    rw [ih, show 2*(m+1) = 2*m+1+1 by omega]
    simp only [sumPrefix, Nat.add_assoc]

theorem sum_ones (m : Nat) : sumPrefix (fun _ => 1) m = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [sumPrefix, ih]

theorem sumPrefix_congr {f g : Nat → Nat} {m : Nat}
    (h : ∀ i, i < m → f i = g i) : sumPrefix f m = sumPrefix g m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [sumPrefix]
    rw [ih (fun i hi => h i (by omega)), h m (by omega)]

theorem sum_le {f g : Nat → Nat} {m : Nat}
    (h : ∀ i, i < m → f i ≤ g i) : sumPrefix f m ≤ sumPrefix g m := by
  induction m with
  | zero => exact Nat.le_refl _
  | succ m ih =>
    exact Nat.add_le_add (ih (fun i hi => h i (by omega))) (h m (by omega))

/-- Coordinatewise domination and equality of sums force equality at every index. -/
theorem eq_at_of_sum_eq {f g : Nat → Nat} {m : Nat}
    (hle : ∀ i, i < m → f i ≤ g i) (hs : sumPrefix f m = sumPrefix g m)
    (i : Nat) (hi : i < m) : f i = g i := by
  induction m with
  | zero => omega
  | succ m ih =>
    have earlier := fun j (hj : j < m) => hle j (by omega)
    have prefixBound := sum_le earlier
    have lastBound := hle m (by omega)
    simp only [sumPrefix] at hs
    by_cases e : i = m
    · subst i; omega
    · exact ih earlier (by omega) (by omega)

/-- A balanced string of 2k bits with one change at its midpoint.
The descending string starts with ones and the rising string starts with zeros. -/
def midpointBit (k : Nat) (descending : Bool) (i : Nat) : Nat :=
  if descending then (if i < k then 1 else 0) else (if i < k then 0 else 1)

end Kings
