module

public import ArctanBridge
public import Mathlib.NumberTheory.LegendreSymbol.Basic

public section

namespace Arxiv.«2607.05739»

private def scalarMod (p : ℕ) (z : GaussianInt) : Prop :=
  (z.re : ZMod p) ≠ 0 ∧ (z.im : ZMod p) = 0

private theorem scalarMod_one (p : ℕ) [Fact p.Prime] : scalarMod p 1 := by
  simp [scalarMod]

private theorem scalarMod_mul {p : ℕ} [Fact p.Prime] {x y : GaussianInt}
    (hx : scalarMod p x) (hy : scalarMod p y) : scalarMod p (x * y) := by
  rcases hx with ⟨hxr, hxi⟩
  rcases hy with ⟨hyr, hyi⟩
  simp [scalarMod, Zsqrtd.re_mul, Zsqrtd.im_mul, hxr, hxi, hyr, hyi]

private def factor (k : ℕ) : GaussianInt := ⟨1, k⟩

/-- The factors indexed by complementary residues multiply to a nonzero scalar. -/
private theorem scalarMod_pair {p a b : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    (hab : a + b = p) : scalarMod p (factor a * factor b) := by
  have hzero : (a : ZMod p) + (b : ZMod p) = 0 := by
    rw [← Nat.cast_add, hab, ZMod.natCast_self]
  have hb : (b : ZMod p) = -(a : ZMod p) := by linear_combination hzero
  have hn : (a : ZMod p) ^ 2 ≠ -1 := fun h => ZMod.mod_four_ne_three_of_sq_eq_neg_one h hp
  constructor
  · simp only [factor, Zsqrtd.re_mul, Int.cast_add, Int.cast_mul, Int.cast_neg,
      Int.cast_one, Int.cast_natCast]
    rw [hb]
    intro h
    apply hn
    linear_combination h
  · simpa [factor, Zsqrtd.im_mul, add_comm] using hzero

/-- Peel off the two endpoints at each step. An odd endpoint sum excludes a singleton. -/
private theorem scalarMod_interval {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    (a b : ℕ) (hab : a + b = p) : scalarMod p (∏ k ∈ Finset.Icc a b, factor k) := by
  induction b generalizing a with
  | zero =>
      have ha : 0 < a := by omega
      simpa [Finset.Icc_eq_empty_of_lt ha] using scalarMod_one p
  | succ b ih =>
      by_cases h : a ≤ b
      · rw [Finset.prod_Icc_succ_top (by omega : a ≤ b + 1)]
        rw [← Finset.insert_Icc_succ_left_eq_Icc h, Finset.prod_insert (by simp)]
        rw [mul_right_comm]
        exact scalarMod_mul (scalarMod_pair hp hab) (ih (a + 1) (by omega))
      · have ha : b + 1 < a := by omega
        simpa [Finset.Icc_eq_empty_of_lt ha] using scalarMod_one p

/-- A complete block of factors modulo a prime congruent to three modulo four
has nonzero real coordinate and zero imaginary coordinate. -/
theorem inert_block (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    ((coords p).1 : ZMod p) ≠ 0 ∧ ((coords p).2 : ZMod p) = 0 := by
  rw [coords_eq]
  change scalarMod p (gaussProd p)
  cases p with
  | zero => omega
  | succ q =>
      rw [gaussProd_succ]
      apply scalarMod_mul (scalarMod_interval hp 1 q (by omega))
      exact ⟨by simp, by simpa only [Int.cast_natCast] using ZMod.natCast_self (q + 1)⟩

/-- The squared norm of the Gaussian product is a unit modulo every prime
congruent to three modulo four. -/
theorem coords_norm_ne_zero (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) (n : ℕ) :
    ((coords n).1 : ZMod p) ^ 2 + ((coords n).2 : ZMod p) ^ 2 ≠ 0 := by
  induction n with
  | zero => simp [coords]
  | succ n ih =>
      let k := ((n + 1 : ℕ) : ZMod p)
      have hk : 1 + k ^ 2 ≠ 0 := by
        intro h
        exact ZMod.mod_four_ne_three_of_sq_eq_neg_one (show k ^ 2 = -1 by linear_combination h) hp
      have norm_step (a b : ZMod p) :
          (a - k * b) ^ 2 + (b + k * a) ^ 2 = (a ^ 2 + b ^ 2) * (1 + k ^ 2) := by ring
      simpa only [coords, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast,
        ← norm_step] using mul_ne_zero ih hk

theorem coords_snd_ne_zero_of_fst_eq_zero (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3)
    (n : ℕ) (hr : ((coords n).1 : ZMod p) = 0) : ((coords n).2 : ZMod p) ≠ 0 := by
  intro hi
  simpa [hr, hi] using coords_norm_ne_zero p hp n

end Arxiv.«2607.05739»
