module

public import Fibers
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Topology.Algebra.Order.Polynomial
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

namespace SmallCubic

open Polynomial Filter
open scoped Polynomial

private def pellStep (R : Type*) [CommRing R] : Equiv.Perm (R × R) where
  toFun p := (3 * p.1 + 4 * p.2, 2 * p.1 + 3 * p.2)
  invFun p := (3 * p.1 - 4 * p.2, -2 * p.1 + 3 * p.2)
  left_inv := by rintro ⟨u, v⟩; apply Prod.ext <;> dsimp <;> ring
  right_inv := by rintro ⟨u, v⟩; apply Prod.ext <;> dsimp <;> ring

/-- The coefficients of (3 + 2√2)ⁿ. -/
def pellAmplificationOrbit : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => pellStep ℤ (pellAmplificationOrbit n)

theorem pellAmplificationOrbit_norm (n : ℕ) :
    (pellAmplificationOrbit n).1 ^ 2 - 2 * (pellAmplificationOrbit n).2 ^ 2 = 1 := by
  induction n with
  | zero => decide
  | succ n ih => dsimp [pellAmplificationOrbit, pellStep]; linear_combination ih

theorem pellAmplificationOrbit_growth (n : ℕ) :
    (n : ℤ) + 1 ≤ (pellAmplificationOrbit n).1 ∧ 0 ≤ (pellAmplificationOrbit n).2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    dsimp [pellAmplificationOrbit, pellStep]
    omega

private theorem orbit_mod (d n : ℕ) :
    (((pellAmplificationOrbit n).1 : ZMod d), ((pellAmplificationOrbit n).2 : ZMod d)) =
      (pellStep (ZMod d) ^ n) (1, 0) := by
  induction n with
  | zero => simp [pellAmplificationOrbit]
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ← ih]
    simp [pellAmplificationOrbit, pellStep]

/-- Simultaneous return to the seed modulo any given positive denominator. -/
theorem pellAmplificationOrbit_congruence (d : ℕ) (hd : 0 < d) :
    ∃ k : ℕ, 0 < k ∧ ∀ n, (d : ℤ) ∣ (pellAmplificationOrbit (k * n)).1 - 1 ∧
      (d : ℤ) ∣ (pellAmplificationOrbit (k * n)).2 := by
  let : NeZero d := ⟨hd.ne'⟩
  let g := pellStep (ZMod d)
  refine ⟨orderOf g, orderOf_pos _, fun n => ?_⟩
  have h := orbit_mod d (orderOf g * n)
  change _ = (g ^ (orderOf g * n)) _ at h
  rw [pow_mul, pow_orderOf_eq_one, one_pow] at h
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    have hu := congrArg Prod.fst h
    simpa using sub_eq_zero.mpr hu
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    exact congrArg Prod.snd h

private theorem clearDen (P : ℚ[X]) :
    ∃ d : ℕ, 0 < d ∧ ∀ u : ℤ, ∃ a : ℤ, (d : ℚ) * P.eval (u : ℚ) = (a : ℚ) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨d, hd, hP⟩ := hP
    obtain ⟨e, he, hQ⟩ := hQ
    refine ⟨d * e, Nat.mul_pos hd he, fun u => ?_⟩
    obtain ⟨a, ha⟩ := hP u
    obtain ⟨b, hb⟩ := hQ u
    refine ⟨(e : ℤ) * a + (d : ℤ) * b, ?_⟩
    rw [eval_add]
    push_cast
    linear_combination (e : ℚ) * ha + (d : ℚ) * hb
  | monomial n r =>
    refine ⟨r.den, r.den_pos, fun u => ⟨r.num * u ^ n, ?_⟩⟩
    have h := (div_eq_iff (show (r.den : ℚ) ≠ 0 by exact_mod_cast r.den_nz)).mp r.num_div_den
    rw [eval_monomial]
    push_cast
    linear_combination -(u : ℚ) ^ n * h

private theorem integralNearSeed (P : ℚ[X]) (hP : P.eval 1 = 1) :
    ∃ d : ℕ, 0 < d ∧ ∀ u : ℤ, (d : ℤ) ∣ u - 1 → ∃ a : ℤ, P.eval (u : ℚ) = (a : ℚ) := by
  obtain ⟨Q, hQ⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (p := P) (a := 1)
  obtain ⟨d, hd, h⟩ := clearDen Q
  refine ⟨d, hd, fun u ⟨k, hk⟩ => ?_⟩
  obtain ⟨a, ha⟩ := h u
  have he := congrArg (Polynomial.eval (u : ℚ)) hQ
  simp [hP] at he
  have hk' : (u : ℚ) - 1 = (d : ℚ) * (k : ℚ) := by exact_mod_cast hk
  refine ⟨1 + k * a, ?_⟩
  push_cast
  linear_combination he + Q.eval (u : ℚ) * hk' + (k : ℚ) * ha

/-- A rational polynomial ansatz with an integral seed returns integral triples
on every multiple of a single positive Pell index. -/
theorem pell_integral_subsequence (C J E : ℚ[X]) (hC : C.eval 1 = 1) (hJ : J.eval 1 = 1) :
    ∃ k : ℕ, 0 < k ∧ ∀ n, let p := pellAmplificationOrbit (k * n)
      ∃ x y z : ℤ, C.eval (p.1 : ℚ) = (x : ℚ) ∧ (p.2 : ℚ) * E.eval (p.1 : ℚ) = (y : ℚ) ∧
        J.eval (p.1 : ℚ) = (z : ℚ) := by
  obtain ⟨c, hc, hcx⟩ := integralNearSeed C hC
  obtain ⟨j, hj, hjz⟩ := integralNearSeed J hJ
  obtain ⟨e, he, hey⟩ := clearDen E
  let d := c * j * e
  have hc' : (c : ℤ) ∣ (d : ℤ) := ⟨(j : ℤ) * e, by dsimp [d]; ring⟩
  have hj' : (j : ℤ) ∣ (d : ℤ) := ⟨(c : ℤ) * e, by dsimp [d]; ring⟩
  have he' : (e : ℤ) ∣ (d : ℤ) := ⟨(c : ℤ) * j, by dsimp [d]; ring⟩
  obtain ⟨k, hk, hr⟩ := pellAmplificationOrbit_congruence d (Nat.mul_pos (Nat.mul_pos hc hj) he)
  refine ⟨k, hk, fun n => ?_⟩
  let p := pellAmplificationOrbit (k * n)
  have h := hr n
  obtain ⟨x, hx⟩ := hcx p.1 (hc'.trans h.1)
  obtain ⟨z, hz⟩ := hjz p.1 (hj'.trans h.1)
  obtain ⟨t, ht⟩ := he'.trans h.2
  obtain ⟨a, ha⟩ := hey p.1
  have ht' : (p.2 : ℚ) = (e : ℚ) * (t : ℚ) := by exact_mod_cast ht
  refine ⟨x, t * a, z, hx, ?_, hz⟩
  change (p.2 : ℚ) * E.eval (p.1 : ℚ) = _
  push_cast
  linear_combination E.eval (p.1 : ℚ) * ht' + (t : ℚ) * ha

/-- A nonconstant first coordinate in a seed-preserving polynomial identity
on the Pell conic gives integral points with unbounded first coordinate. -/
theorem pell_amplification_unbounded (C J E : ℚ[X]) (hC : C.eval 1 = 1)
    (hJ : J.eval 1 = 1) (hdeg : 0 < C.degree)
    (hid : ∀ u : ℚ, (J.eval u) ^ 2 + ((u ^ 2 - 1) / 2) * (E.eval u) ^ 2 * J.eval u + (C.eval u) ^ 3 = 2)
    (B : ℕ) : ∃ x y z : ℤ, B < x.natAbs ∧ z ^ 2 + y ^ 2 * z + x ^ 3 = 2 := by
  obtain ⟨k, hk, hi⟩ := pell_integral_subsequence C J E hC hJ
  obtain ⟨t, ht⟩ := eventually_atTop.mp ((C.abs_tendsto_atTop hdeg).eventually
    (eventually_gt_atTop (B : ℚ)))
  obtain ⟨n, hn⟩ := exists_nat_ge t
  let p := pellAmplificationOrbit (k * n)
  have hg := (pellAmplificationOrbit_growth (k * n)).1
  have hkn : n ≤ k * n := Nat.le_mul_of_pos_left n hk
  have hn' : (n : ℤ) ≤ p.1 := by dsimp [p]; omega
  have hbig := ht (p.1 : ℚ) (hn.trans (by exact_mod_cast hn'))
  obtain ⟨x, y, z, hx, hy, hz⟩ := hi n
  change C.eval (p.1 : ℚ) = (x : ℚ) at hx
  change (p.2 : ℚ) * E.eval (p.1 : ℚ) = (y : ℚ) at hy
  change J.eval (p.1 : ℚ) = (z : ℚ) at hz
  change (B : ℚ) < |C.eval (p.1 : ℚ)| at hbig
  rw [hx] at hbig
  have hnorm : (p.1 : ℚ) ^ 2 - 2 * (p.2 : ℚ) ^ 2 = 1 := by
    exact_mod_cast pellAmplificationOrbit_norm (k * n)
  have heq : ((p.1 : ℚ) ^ 2 - 1) / 2 = (p.2 : ℚ) ^ 2 := by linarith
  refine ⟨x, y, z, ?_, ?_⟩
  · have habs : (B : ℤ) < |x| := by exact_mod_cast hbig
    rw [← Int.natCast_natAbs] at habs
    exact_mod_cast habs
  · have h := hid (p.1 : ℚ)
    rw [heq, hx, hz, ← mul_pow, hy] at h
    exact_mod_cast h

theorem pell_amplification_infinite (C J E : ℚ[X]) (hC : C.eval 1 = 1)
    (hJ : J.eval 1 = 1) (hdeg : 0 < C.degree)
    (hid : ∀ u : ℚ, (J.eval u) ^ 2 + ((u ^ 2 - 1) / 2) * (E.eval u) ^ 2 * J.eval u + (C.eval u) ^ 3 = 2) :
    {p : ℤ × ℤ × ℤ | p.2.2 ^ 2 + p.2.1 ^ 2 * p.2.2 + p.1 ^ 3 = 2}.Infinite :=
  infinite_iff_unbounded_x.mpr (pell_amplification_unbounded C J E hC hJ hdeg hid)

/-- Clearing the factor of two gives a polynomial identity directly checkable by ring. -/
theorem pell_amplification_of_polynomial_identity (C J E : ℚ[X]) (hC : C.eval 1 = 1)
    (hJ : J.eval 1 = 1) (hdeg : 0 < C.degree)
    (hid : 2 * J ^ 2 + (X ^ 2 - 1) * E ^ 2 * J + 2 * C ^ 3 = 4) :
    {p : ℤ × ℤ × ℤ | p.2.2 ^ 2 + p.2.1 ^ 2 * p.2.2 + p.1 ^ 3 = 2}.Infinite := by
  apply pell_amplification_infinite C J E hC hJ hdeg
  intro u
  have h := congrArg (Polynomial.eval u) hid
  simp at h
  linear_combination h / 2

end SmallCubic
