module

public import ArctanPrimeInterval
public import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorial.BigOperators

public section

namespace Arxiv.«2607.05739»

open Finset

private abbrev vp (p x : ℕ) := x.factorization p

private theorem sum_shift_val (p k n : ℕ) :
    (∑ j ∈ Icc 1 n, vp p (k + j)) = vp p ((k + 1).ascFactorial n) := by
  induction n with
  | zero => simp [vp]
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih, Nat.ascFactorial_succ]
    simp only [vp, Nat.factorization_mul (by omega : k + 1 + n ≠ 0)
      (Nat.ascFactorial_pos k n).ne', Finsupp.add_apply]
    rw [show k + (n+1) = k + 1 + n by omega, Nat.add_comm]

private theorem sum_dist_val {k n : ℕ} (p : ℕ) (hk : k ≤ n) :
    (∑ j ∈ Icc 1 n, (vp p (k - j) + vp p (j - k))) ≤
      vp p k.factorial + vp p (n - k).factorial := by
  induction n, hk using Nat.le_induction with
  | base =>
    have h : (∑ j ∈ Icc 1 k, (vp p (k - j) + vp p (j - k))) =
        ∑ j ∈ Icc 1 k, vp p (k - j) := by
      apply sum_congr rfl
      intro j hj
      simp [Nat.sub_eq_zero_of_le (mem_Icc.mp hj).2, vp]
    rw [h]
    have href : (∑ j ∈ Ico 0 (k + 1), vp p (k - j)) = ∑ j ∈ Ico 0 (k + 1), vp p j := by
      simpa using sum_Ico_reflect (vp p) 0 (m := k + 1) (n := k) le_rfl
    have hfac : (∑ j ∈ Ico 0 (k + 1), vp p j) = vp p k.factorial := by
      rw [Nat.Ico_zero_eq_range, sum_range_succ']
      simpa [vp] using (Nat.factorization_prod_apply
        (p := p) (S := range k) (g := fun i => i + 1) (by simp)).symm.trans
          (congrArg (vp p) (prod_range_add_one_eq_factorial k))
    have hsub : Icc 1 k ⊆ Ico 0 (k + 1) := fun j hj => mem_Ico.mpr ⟨Nat.zero_le _, Nat.lt_succ_of_le (mem_Icc.mp hj).2⟩
    grw [sum_le_sum_of_subset (f := fun j => vp p (k - j)) hsub, href, hfac]
    omega
  | succ n hk ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ n + 1), show n + 1 - k = (n-k) + 1 by omega,
      Nat.factorial_succ]
    simp only [Nat.sub_eq_zero_of_le (by omega : k ≤ n+1), vp,
      Nat.factorization_mul (by omega : n-k+1 ≠ 0) (Nat.factorial_ne_zero _), Nat.factorization_zero,
      Finsupp.zero_apply, zero_add, Finsupp.add_apply] at *
    omega

private theorem val_pair {p e x y : ℕ} (hp : p.Prime) (hxy : x < y)
    (hx : p ^ e ∣ 1 + x ^ 2) (hy : p ^ e ∣ 1 + y ^ 2) :
    e ≤ vp p (x + y) + vp p (y - x) := by
  have hd := Nat.dvd_sub hy hx
  rw [Nat.add_sub_add_left, Nat.sq_sub_sq, Nat.add_comm y x] at hd
  have he := (hp.pow_dvd_iff_le_factorization
    (mul_ne_zero (by omega : x+y ≠ 0) (by omega : y-x ≠ 0))).mp hd
  simpa [vp, Nat.factorization_mul (by omega : x+y ≠ 0) (by omega : y-x ≠ 0)] using he

/-- Bound the valuation of the norm product by comparing every factor with a
factor of maximal valuation, then applying the binomial-coefficient bound. -/
theorem normProduct_factorization_le {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    (normProduct n).factorization p ≤ 2 * n.factorial.factorization p +
      Nat.log p (n ^ 2 + 1) + Nat.log p (2 * n) := by
  let f := fun j : ℕ => vp p (1 + j ^ 2)
  obtain ⟨k, hk, hmax⟩ := (Icc 1 n).exists_max_image f ⟨n, mem_Icc.mpr ⟨hn, le_rfl⟩⟩
  obtain ⟨hkpos, hkn⟩ := mem_Icc.mp hk
  have hsum : (normProduct n).factorization p = ∑ j ∈ Icc 1 n, f j :=
    Nat.factorization_prod_apply (g := fun j : ℕ => 1 + j^2) (by intros; positivity)
  have hterm (j : ℕ) (hj : j ∈ Icc 1 n) : f j ≤
      (if j = k then f j else 0) + (vp p (k - j) + vp p (j - k)) + vp p (k + j) := by
    rcases lt_trichotomy j k with h | rfl | h
    · have hpair := val_pair hp h (Nat.ordProj_dvd (1 + j^2) p)
        ((hp.pow_dvd_iff_le_factorization (by positivity)).mpr (hmax j hj))
      simpa [f, h.ne, vp, Nat.sub_eq_zero_of_le h.le, add_comm] using hpair
    · simp [vp]
    · have hpair := val_pair hp h
        ((hp.pow_dvd_iff_le_factorization (by positivity)).mpr (hmax j hj))
        (Nat.ordProj_dvd (1 + j^2) p)
      simpa [f, h.ne', vp, Nat.sub_eq_zero_of_le h.le, add_comm] using hpair
  have hsum' := sum_le_sum hterm
  simp only [sum_add_distrib, sum_ite_eq', hk, ite_true] at hsum'
  have hdist := sum_dist_val p hkn
  rw [sum_add_distrib] at hdist
  have hfac := (Nat.factorization_le_iff_dvd
    (mul_ne_zero (Nat.factorial_ne_zero k) (Nat.factorial_ne_zero (n-k)))
    (Nat.factorial_ne_zero n)).mpr (Nat.factorial_mul_factorial_dvd_factorial hkn) p
  simp [Nat.factorization_mul (Nat.factorial_ne_zero k) (Nat.factorial_ne_zero (n-k))] at hfac
  have hshift := sum_shift_val p k n
  rw [Nat.ascFactorial_eq_factorial_mul_choose] at hshift
  simp only [vp, Nat.factorization_mul (Nat.factorial_ne_zero n)
    (Nat.choose_pos (by omega : n ≤ k+n)).ne', Finsupp.add_apply] at hshift
  have hc := (Nat.factorization_choose_le_log (p := p) (n := k+n) (k := n)).trans
    (Nat.log_mono_right (by omega : k + n ≤ 2*n))
  have hmaxlog : f k ≤ Nat.log p (n^2 + 1) := by
    apply Nat.le_log_of_pow_le hp.one_lt
    have hdiv := Nat.le_of_dvd (by positivity : 0 < 1+k^2) (Nat.ordProj_dvd (1+k^2) p)
    exact hdiv.trans (by nlinarith [Nat.pow_le_pow_left hkn 2])
  rw [hsum]
  dsimp [vp] at *
  omega

end Arxiv.«2607.05739»
