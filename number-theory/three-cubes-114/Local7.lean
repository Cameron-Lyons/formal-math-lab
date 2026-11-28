import Std

namespace ThreeCubes114

/-- Signed pair sums admissible modulo 343 when the remaining coordinate is divisible by 7. -/
def pairSumAt7 (a : Int) : Bool :=
  [3, 5, 6].contains (a % 7) ||
    [23, 71, 102, 120, 121, 169, 170, 200, 219, 249, 298, 316].contains (a % 343)

private def residue (n : Nat) (hn : n > 0) (t : Int) : Fin n :=
  ⟨(t % n).toNat, by
    have := Int.emod_lt_of_pos t (show 0 < (n : Int) by omega)
    omega⟩

private theorem residue_val (n : Nat) (hn : n > 0) (t : Int) :
    ((residue n hn t).val : Int) = t % n := by
  simp only [residue]
  have := Int.emod_nonneg t (show (n : Int) ≠ 0 by omega)
  omega

private theorem mul_congr {m a b c d : Int}
    (ha : a % m = c % m) (hb : b % m = d % m) : (a*b) % m = (c*d) % m := by
  rw [Int.mul_emod a b, Int.mul_emod c d, ha, hb]

private theorem pow_congr {m a b : Int} (h : a % m = b % m) (n : Nat) :
    a ^ n % m = b ^ n % m := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Int.pow_succ]; exact mul_congr ih h

private theorem cube_sum_reduced (x y z m : Int) :
    ((x % m)^3 + (y % m)^3 + (z % m)^3) % m = (x^3 + y^3 + z^3) % m := by
  have cube (t : Int) : (t % m)^3 % m = t^3 % m := pow_congr (by simp) 3
  rw [Int.add_emod, Int.add_emod ((x%m)^3), cube, cube, cube]
  rw [← Int.add_emod (x^3) (y^3), ← Int.add_emod]

private theorem one_multiple_table : ∀ x y z : Fin 7,
    ((x.val : Int)^3 + (y.val : Int)^3 + (z.val : Int)^3) % 7 = 2 →
    ((x.val : Int) = 0 ∧ (y.val : Int) ≠ 0 ∧ (z.val : Int) ≠ 0) ∨
    ((x.val : Int) ≠ 0 ∧ (y.val : Int) = 0 ∧ (z.val : Int) ≠ 0) ∨
    ((x.val : Int) ≠ 0 ∧ (y.val : Int) ≠ 0 ∧ (z.val : Int) = 0) := by decide +kernel

/-- This ordering can be chosen for every integer solution. -/
theorem exactly_one_multiple_of_seven (x y z : Int) (h : x^3 + y^3 + z^3 = 114) :
    (x%7 = 0 ∧ y%7 ≠ 0 ∧ z%7 ≠ 0) ∨ (x%7 ≠ 0 ∧ y%7 = 0 ∧ z%7 ≠ 0) ∨
    (x%7 ≠ 0 ∧ y%7 ≠ 0 ∧ z%7 = 0) := by
  have ht := one_multiple_table (residue 7 (by decide) x) (residue 7 (by decide) y)
    (residue 7 (by decide) z)
  simp only [residue_val] at ht
  apply ht
  have hc := cube_sum_reduced x y z 7
  exact hc.trans (by rw [h]; decide)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem pair_table : ∀ a : Fin 343,
    pairSumAt7 a.val = true ↔ ∃ x : Fin 343,
      ((x.val : Int)^3 + ((a.val : Int) - x.val)^3) % 343 = 114 := by decide +kernel

/-- Normalizing the signed pair sum and one coordinate preserves the cubic congruence. -/
private theorem reduce_pair (a x : Int) :
    ((x%343)^3 + (a%343-x%343)^3) % 343 = (x^3 + (a-x)^3) % 343 := by
  rw [Int.add_emod, Int.add_emod (x^3), pow_congr (Int.emod_emod x 343) 3,
    pow_congr (Int.sub_emod a x 343).symm 3]

/-- Exact classification of signed pair sums when 7 divides the third coordinate.
Every passing residue even admits the local choice `z = 0` modulo 343. -/
theorem pair_sum_mod343_iff (a : Int) : pairSumAt7 a = true ↔
    ∃ x : Int, (x^3 + (a-x)^3) % 343 = 114 := by
  have ht := pair_table (residue 343 (by decide) a)
  simp only [residue_val] at ht
  have heq : pairSumAt7 (a%343) = pairSumAt7 a := by
    simp [pairSumAt7, show a%343%7 = a%7 by omega]
  change pairSumAt7 (a%343) = true ↔ ∃ x : Fin 343,
    ((x.val : Int)^3 + (a%343 - x.val)^3) % 343 = 114 at ht
  rw [← heq, ht]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v.val, ?_⟩
    rw [← reduce_pair]
    have hv' : (v.val : Int)%343 = v.val := by omega
    rwa [hv']
  · rintro ⟨x, hx⟩
    refine ⟨residue 343 (by decide) x, ?_⟩
    simp only [residue_val]
    change ((x%343)^3 + (a%343 - x%343)^3) % 343 = 114
    rwa [reduce_pair]

/-- A single test on `x+y` skips every multiple-of-seven `z` for a rejected sum. -/
theorem pair_sum_at_seven (x y z : Int) (h : x^3 + y^3 + z^3 = 114) (hz : 7 ∣ z) :
    pairSumAt7 (x+y) = true := by
  obtain ⟨w, hw⟩ := hz
  have hc : z^3 = 343*w^3 := by grind
  apply (pair_sum_mod343_iff _).mpr
  refine ⟨x, ?_⟩
  have hm := congrArg (fun v : Int => v%343) h
  rw [hc, Int.add_mul_emod_self_left] at hm
  simpa [show x+y-x=y by omega] using hm

end ThreeCubes114
