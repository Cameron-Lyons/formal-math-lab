module

public import ArctanBridge
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

@[expose] public section

namespace Arxiv.«2607.05739»

private def detMod (p r s : ℕ) : ZMod p :=
  ((coords r).1 : ZMod p) * (coords s).2 - ((coords r).2 : ZMod p) * (coords s).1

private theorem detMod_slide {p r s : ℕ} (h : (r + 1) + (s + 1) = p) :
    detMod p (r + 1) s = detMod p r (s + 1) := by
  have hzero : ((r + 1 : ℕ) : ZMod p) + ((s + 1 : ℕ) : ZMod p) = 0 := by
    rw [← Nat.cast_add, h, ZMod.natCast_self]
  have hs := eq_neg_of_add_eq_zero_right hzero
  simp only [detMod, coords, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  rw [hs]
  ring

private theorem detMod_eq_end {p : ℕ} (r s : ℕ) (h : r + s + 1 = p) :
    detMod p r s = ((coords (r + s)).2 : ZMod p) := by
  induction r generalizing s with
  | zero => simp [detMod, coords]
  | succ r ih =>
    rw [detMod_slide (p := p) (r := r) (s := s) (by omega), ih (s + 1) (by omega)]
    rw [Nat.succ_add, Nat.add_succ]

/-- At complementary indices modulo an odd modulus, the Gaussian coordinate
vectors have determinant zero. For a prime congruent to three modulo four,
both vectors are nonzero and consequently give the same projective point. -/
theorem coords_reflection (p r : ℕ) (hp : Odd p) (hr : r < p) :
    ((coords r).1 : ZMod p) * (coords (p - 1 - r)).2 =
    ((coords r).2 : ZMod p) * (coords (p - 1 - r)).1 := by
  obtain ⟨k, hk⟩ := hp
  apply sub_eq_zero.mp
  change detMod p r (p - 1 - r) = 0
  rw [detMod_eq_end _ _ (by omega), show r + (p - 1 - r) = k + k by omega,
    ← detMod_eq_end k k (by omega)]
  simp [detMod, mul_comm]

end Arxiv.«2607.05739»
