module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! A degree bound for both-ended Laurent solutions over a splitting field. -/
public section
namespace SmallCubic.PellDegreeRatio
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

private noncomputable def delta (p : K[X]) : K[X] := X*p.derivative

omit [CharZero K] in
private theorem delta_degree (p : K[X]) : (delta p).natDegree ≤ p.natDegree := by
  by_cases h : p.natDegree=0
  · rw [eq_C_of_natDegree_eq_zero h]; simp [delta]
  · apply natDegree_mul_le.trans
    rw [natDegree_X]
    have := natDegree_derivative_le p
    omega

/-- Wronskian degree estimate with a monomial removed from the right-hand
side. The unit constant coefficients ensure that the Wronskian is nonzero
and that the removed power of X is coprime to w. -/
theorem monomial_gap (a w h : K[X]) (k : ℕ) (hk : 0 < k)
    (ha : a.coeff 0 ≠ 0) (hw : w.coeff 0 ≠ 0) (hh : h.coeff 0 ≠ 0)
    (hf : w^2+4*a^3=X^k*h) : w.natDegree ≤ a.natDegree+h.natDegree := by
  let N := 3*h*delta a - a*(C (k:K)*h+delta h)
  have hprod (p q : K[X]) : delta (p*q) = delta p*q+p*delta q := by
    simp [delta,derivative_mul]; ring
  have hpow : delta (X^k : K[X])=C (k:K)*X^k := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [delta,derivative_X_pow_succ, pow_succ, Nat.cast_succ]
    ring
  have hd : 2*w*delta w+12*a^2*delta a =
      X^k*(C (k:K)*h+delta h) := by
    have eq := congrArg delta hf
    rw [hprod,hpow] at eq
    unfold delta at *
    simp [derivative_add,derivative_pow] at eq
    change X*(2*w*w.derivative+4*(3*a^2*a.derivative)) = _ at eq
    rw [map_natCast]
    linear_combination eq
  have hx : w ∣ X^k*N := by
    refine ⟨3*w*delta a-2*a*delta w, ?_⟩
    dsimp [N]
    linear_combination -3*delta a*hf + a*hd
  have hcop := (irreducible_X (R := K)).isCoprime_or_dvd w
  have cop : IsCoprime w X := (hcop.resolve_right (fun h => hw (X_dvd_iff.mp h))).symm
  have hN : N ≠ 0 := by
    intro hzero
    have eq := congrArg (fun p : K[X] => p.eval 0) hzero
    have hkk : (k:K) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
    rw [coeff_zero_eq_eval_zero] at ha hh
    simp [N,delta,ha,hh,hkk] at eq
  apply (natDegree_le_of_dvd (cop.pow_right.dvd_of_dvd_mul_left hx) hN).trans
  apply (natDegree_sub_le _ _).trans (max_le _ _)
  · apply natDegree_mul_le.trans
    have dh : (3*h).natDegree ≤ h.natDegree := natDegree_C_mul_le (3:K) _
    have da := delta_degree a
    omega
  · apply natDegree_mul_le.trans
    apply Nat.add_le_add_left
    apply (natDegree_add_le _ _).trans (max_le (natDegree_C_mul_le _ _) (delta_degree _))

/-- For a Laurent solution x=t^{-n}a, y=t^{-m}b,
w=t^{-3n/2}c with both ends of the indicated orders and 3n>4m, clearing
denominators yields these hypotheses and gives n≤8m. -/
theorem pole_bound (a b c : K[X]) (n m : ℕ) (hm : 0 < m) (hgap : 4*m < 3*n)
    (ha : a.coeff 0 ≠ 0) (hb : b.coeff 0 ≠ 0) (hc : c.coeff 0 ≠ 0)
    (da : a.natDegree = 2*n) (db : b.natDegree = 2*m) (dc : c.natDegree=3*n)
    (hf : c^2+4*a^3=X^(3*n-4*m)*(b^4+8*X^(4*m))) : n ≤ 8*m := by
  have h0 : (b^4+8*X^(4*m)).coeff 0 ≠ 0 := by
    rw [coeff_zero_eq_eval_zero] at hb ⊢
    simp [hm.ne',hb]
  have de := monomial_gap a c _ _ (by omega) ha hc h0 hf
  have de4 : (b^4+8*X^(4*m)).natDegree ≤ 8*m := by
    apply (natDegree_add_le _ _).trans (max_le _ _)
    · rw [natDegree_pow, db]; omega
    · exact (natDegree_C_mul_le (8:K) _).trans (by simp; omega)
  omega

end SmallCubic.PellDegreeRatio
