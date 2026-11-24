module

public import Fibers
public import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Algebra.Order.Polynomial
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

namespace SmallCubic.MixedPell

open Polynomial Filter
open scoped Polynomial

private def pellStep (R : Type*) [CommRing R] : Equiv.Perm (R × R) where
  toFun p := (2 * p.1 + 3 * p.2, p.1 + 2 * p.2)
  invFun p := (2 * p.1 - 3 * p.2, -p.1 + 2 * p.2)
  left_inv := by rintro ⟨u, v⟩; apply Prod.ext <;> dsimp <;> ring
  right_inv := by rintro ⟨u, v⟩; apply Prod.ext <;> dsimp <;> ring

/-- The coefficients of (2 + √3)ⁿ. -/
def orbit : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => pellStep ℤ (orbit n)

theorem orbit_norm (n : ℕ) :
    (orbit n).1 ^ 2 - 3 * (orbit n).2 ^ 2 = 1 := by
  induction n with
  | zero => decide
  | succ n ih => dsimp [orbit, pellStep]; linear_combination ih

theorem orbit_growth (n : ℕ) :
    (n : ℤ) + 1 ≤ (orbit n).1 ∧ 0 ≤ (orbit n).2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    dsimp [orbit, pellStep]
    omega

private theorem orbit_mod (d n : ℕ) :
    (((orbit n).1 : ZMod d), ((orbit n).2 : ZMod d)) =
      (pellStep (ZMod d) ^ n) (1, 0) := by
  induction n with
  | zero => simp [orbit]
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ← ih]
    simp [orbit, pellStep]

/-- Simultaneous return to the seed modulo any given positive denominator. -/
theorem orbit_congruence (d : ℕ) (hd : 0 < d) :
    ∃ k : ℕ, 0 < k ∧ ∀ n, (d : ℤ) ∣ (orbit (k * n)).1 - 1 ∧
      (d : ℤ) ∣ (orbit (k * n)).2 := by
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

private theorem integralNearSeed (P : ℚ[X]) (c : ℤ) (hP : P.eval 1 = (c : ℚ)) :
    ∃ d : ℕ, 0 < d ∧ ∀ u : ℤ, (d : ℤ) ∣ u - 1 → ∃ a : ℤ, P.eval (u : ℚ) = (a : ℚ) := by
  obtain ⟨Q, hQ⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (p := P) (a := 1)
  obtain ⟨d, hd, h⟩ := clearDen Q
  refine ⟨d, hd, fun u ⟨k, hk⟩ => ?_⟩
  obtain ⟨a, ha⟩ := h u
  have he := congrArg (Polynomial.eval (u : ℚ)) hQ
  simp [hP] at he
  have hk' : (u : ℚ) - 1 = (d : ℚ) * (k : ℚ) := by exact_mod_cast hk
  refine ⟨c + k * a, ?_⟩
  push_cast
  linear_combination he + Q.eval (u : ℚ) * hk' + (k : ℚ) * ha

/-- The normal form of a polynomial function on u² − 3v² = 1. -/
structure Coord where
  a : ℚ[X]
  b : ℚ[X]

def Coord.val (F : Coord) (u v : ℚ) : ℚ := F.a.eval u + v * F.b.eval u

private theorem coord_integral (F : Coord) (c : ℤ) (hc : F.val 1 0 = c) :
    ∃ d : ℕ, 0 < d ∧ ∀ u v : ℤ, (d : ℤ) ∣ u-1 → (d : ℤ) ∣ v →
      ∃ a : ℤ, F.val u v = a := by
  obtain ⟨e, he, hA⟩ := integralNearSeed F.a c (by simpa [Coord.val] using hc)
  obtain ⟨f, hf, hB⟩ := clearDen F.b
  refine ⟨e*f, Nat.mul_pos he hf, fun u v hu hv => ?_⟩
  push_cast at hu hv
  obtain ⟨a, ha⟩ := hA u ((dvd_mul_right _ _).trans hu)
  obtain ⟨s, hs⟩ := (dvd_mul_left (f : ℤ) (e : ℤ)).trans hv
  obtain ⟨b, hb⟩ := hB u
  have hs' : (v : ℚ) = (f : ℚ) * s := by exact_mod_cast hs
  refine ⟨a+s*b, ?_⟩
  dsimp [Coord.val]
  push_cast
  linear_combination ha + F.b.eval (u : ℚ) * hs' + (s : ℚ)*hb

/-- Both conjugates of a fixed positive power of the Pell unit preserve
integrality of all three coordinate functions at every subsequent power. -/
theorem integral_subsequence (F G H : Coord) (x₀ y₀ z₀ : ℤ)
    (hF : F.val 1 0 = x₀) (hG : G.val 1 0 = y₀) (hH : H.val 1 0 = z₀) :
    ∃ k : ℕ, 0 < k ∧ ∀ n (s : ℤ), let p := orbit (k*n)
      ∃ x y z : ℤ, F.val p.1 (s*p.2 : ℤ) = x ∧ G.val p.1 (s*p.2 : ℤ) = y ∧
        H.val p.1 (s*p.2 : ℤ) = z := by
  obtain ⟨a, ha, hA⟩ := coord_integral F x₀ hF
  obtain ⟨b, hb, hB⟩ := coord_integral G y₀ hG
  obtain ⟨c, hc, hC⟩ := coord_integral H z₀ hH
  let d := a*b*c
  have ha' : (a : ℤ) ∣ (d : ℤ) := ⟨(b : ℤ)*c, by dsimp [d]; ring⟩
  have hb' : (b : ℤ) ∣ (d : ℤ) := ⟨(a : ℤ)*c, by dsimp [d]; ring⟩
  have hc' : (c : ℤ) ∣ (d : ℤ) := ⟨(a : ℤ)*b, by dsimp [d]; ring⟩
  obtain ⟨k, hk, hr⟩ := orbit_congruence d (Nat.mul_pos (Nat.mul_pos ha hb) hc)
  refine ⟨k, hk, fun n s => ?_⟩
  obtain ⟨hu, hv⟩ := hr n
  have hv' := dvd_mul_of_dvd_right hv s
  obtain ⟨x, hx⟩ := hA _ _ (ha'.trans hu) (ha'.trans hv')
  obtain ⟨y, hy⟩ := hB _ _ (hb'.trans hu) (hb'.trans hv')
  obtain ⟨z, hz⟩ := hC _ _ (hc'.trans hu) (hc'.trans hv')
  exact ⟨x,y,z,hx,hy,hz⟩

private theorem bound_forces_constant (P : ℚ[X]) (k : ℕ) (hk : 0 < k) (M : ℚ)
    (hM : ∀ n, |P.eval ((orbit (k*n)).1 : ℚ)| ≤ M) : P = C (P.coeff 0) := by
  apply Polynomial.eq_C_of_natDegree_eq_zero
  by_contra hnz
  have hdeg : 0 < P.degree := Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hnz)
  obtain ⟨t, ht⟩ := eventually_atTop.mp ((P.abs_tendsto_atTop hdeg).eventually
    (eventually_gt_atTop M))
  obtain ⟨n, hn⟩ := exists_nat_ge t
  have hg := (orbit_growth (k*n)).1
  have hkn : n ≤ k*n := Nat.le_mul_of_pos_left n hk
  have hn' : (n : ℤ) ≤ (orbit (k*n)).1 := by omega
  exact (not_lt_of_ge (hM n)) (ht _ (hn.trans (by exact_mod_cast hn')))

/-- A single mixed polynomial identity on the Pell conic yields infinitely
many integer solutions when its first coordinate differs at two rational points. -/
theorem infinite_of_distinct (F G H : Coord) (x₀ y₀ z₀ : ℤ)
    (hF : F.val 1 0 = x₀) (hG : G.val 1 0 = y₀) (hH : H.val 1 0 = z₀)
    (u₁ v₁ : ℚ) (hdist : F.val 1 0 ≠ F.val u₁ v₁)
    (hid : ∀ u v : ℚ, u ≠ -1 → u ^ 2 - 3*v ^ 2 = 1 →
      (H.val u v)^2 + (G.val u v)^2 * H.val u v + (F.val u v)^3 = 2) :
    {p : ℤ × ℤ × ℤ | p.2.2 ^ 2 + p.2.1 ^ 2 * p.2.2 + p.1 ^ 3 = 2}.Infinite := by
  apply infinite_iff_unbounded_x.mpr
  intro M
  by_contra no
  obtain ⟨k, hk, hi⟩ := integral_subsequence F G H x₀ y₀ z₀ hF hG hH
  have bound (n : ℕ) (s : ℤ) (hs : s^2 = 1) :
      |F.val (orbit (k*n)).1 (s*(orbit (k*n)).2 : ℤ)| ≤ (M : ℚ) := by
    let p := orbit (k*n)
    obtain ⟨x,y,z,hx,hy,hz⟩ := hi n s
    have hn : p.1 ^ 2 - 3 * (s * p.2) ^ 2 = 1 := by
      rw [mul_pow, hs, one_mul]
      exact orbit_norm _
    have hg := (orbit_growth (k*n)).1
    have hu : p.1 ≠ -1 := by dsimp [p]; omega
    have hr := hid (p.1 : ℚ) ((s*p.2 : ℤ) : ℚ) (by exact_mod_cast hu) (by exact_mod_cast hn)
    rw [hx, hy, hz] at hr
    have heq : z^2+y^2*z+x^3=2 := by exact_mod_cast hr
    have hnat : x.natAbs ≤ M := le_of_not_gt (fun h => no ⟨x,y,z,h,heq⟩)
    have hi' : |x| ≤ (M : ℤ) := by rw [← Int.natCast_natAbs]; exact_mod_cast hnat
    rw [hx]
    exact_mod_cast hi'
  have bounds (n : ℕ) : let p := orbit (k*n)
      |F.a.eval (p.1 : ℚ)| ≤ (M : ℚ) ∧ |(p.2 : ℚ)*F.b.eval (p.1 : ℚ)| ≤ (M : ℚ) := by
    have hp := (abs_le.mp (bound n 1 (by decide)))
    have hm := (abs_le.mp (bound n (-1) (by decide)))
    simp [Coord.val] at hp hm
    dsimp
    constructor <;> apply abs_le.mpr <;> constructor <;> linarith [hp.1, hp.2, hm.1, hm.2]
  have ha := bound_forces_constant F.a k hk (M : ℚ) (fun n => (bounds n).1)
  let P : ℚ[X] := (X^2-1)*F.b^2
  have hP := bound_forces_constant P k hk (3*(M : ℚ)^2) (by
    intro n
    let p := orbit (k*n)
    have hn : (p.1 : ℚ)^2-3*(p.2 : ℚ)^2=1 := by exact_mod_cast orbit_norm (k*n)
    have hb := (bounds n).2
    change |(p.2 : ℚ)*F.b.eval (p.1 : ℚ)| ≤ (M : ℚ) at hb
    have hv : P.eval (p.1 : ℚ) = 3*((p.2 : ℚ)*F.b.eval (p.1 : ℚ))^2 := by
      simp [P]
      linear_combination F.b.eval (p.1 : ℚ)^2 * hn
    rw [hv, abs_of_nonneg (by positivity)]
    have hsq := mul_self_le_mul_self (abs_nonneg _) hb
    rw [← sq, sq_abs, ← sq] at hsq
    linarith)
  have hz := congrArg (Polynomial.eval (1 : ℚ)) hP
  rw [eval_C] at hz
  have hzero : P.coeff 0 = 0 := hz.symm.trans (by simp [P])
  have he : (X^2-1 : ℚ[X])*F.b^2=0 := hP.trans (by rw [hzero, map_zero])
  have hne : (X^2-1 : ℚ[X]) ≠ 0 := by
    intro bad
    have h := congrArg (Polynomial.eval (0 : ℚ)) bad
    norm_num at h
  have hb : F.b=0 := by simpa using (mul_eq_zero.mp he).resolve_left hne
  apply hdist
  obtain ⟨c, hconst⟩ : ∃ c : ℚ, F.a = C c := ⟨_, ha⟩
  simp [Coord.val, hconst, hb]


/-- A polynomial in v with coefficients in ℚ[u], evaluated at (u,v). -/
noncomputable def bival (P : Polynomial (ℚ[X])) (u v : ℚ) : ℚ :=
  P.eval₂ (Polynomial.evalRingHom u) v

/-- Reducing powers of v gives a mixed normal form for every bivariate polynomial. -/
theorem exists_coord (P : Polynomial (ℚ[X])) :
    ∃ F : Coord, ∀ u v : ℚ, u^2-3*v^2=1 → F.val u v = bival P u v := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨F,hF⟩ := hP
    obtain ⟨G,hG⟩ := hQ
    refine ⟨⟨F.a+G.a,F.b+G.b⟩, fun u v hn => ?_⟩
    rw [bival, Polynomial.eval₂_add]
    change _ = bival P u v + bival Q u v
    rw [← hF u v hn, ← hG u v hn]
    simp [Coord.val]
    ring
  | monomial n r =>
    induction n with
    | zero =>
      refine ⟨⟨r,0⟩, fun u v _ => ?_⟩
      simp [Coord.val, bival]
    | succ n ih =>
      obtain ⟨F,hF⟩ := ih
      refine ⟨⟨C (1/3)*(X^2-1)*F.b,F.a⟩, fun u v hn => ?_⟩
      have h := hF u v hn
      simp [Coord.val, bival, Polynomial.eval₂_monomial] at h ⊢
      rw [pow_succ]
      linear_combination v*h + (F.b.eval u/3)*hn

/-- For any polynomial substitution, unequal endpoint x values certify the
nonconstancy needed for Pell amplification. -/
theorem infinite_of_bivariate_on_chart (F G H : Polynomial (ℚ[X])) (x₀ y₀ z₀ : ℤ)
    (hF : bival F 1 0 = x₀) (hG : bival G 1 0 = y₀) (hH : bival H 1 0 = z₀)
    (u₁ v₁ : ℚ) (hN : u₁^2-3*v₁^2=1) (hdist : bival F 1 0 ≠ bival F u₁ v₁)
    (hid : ∀ u v : ℚ, u ≠ -1 → u^2-3*v^2=1 →
      (bival H u v)^2 + (bival G u v)^2 * bival H u v + (bival F u v)^3 = 2) :
    {p : ℤ × ℤ × ℤ | p.2.2 ^ 2 + p.2.1 ^ 2 * p.2.2 + p.1 ^ 3 = 2}.Infinite := by
  obtain ⟨f,hf⟩ := exists_coord F
  obtain ⟨g,hg⟩ := exists_coord G
  obtain ⟨h,hh⟩ := exists_coord H
  have h₀ : (1:ℚ)^2-3*0^2=1 := by norm_num
  apply infinite_of_distinct f g h x₀ y₀ z₀ ((hf 1 0 h₀).trans hF)
    ((hg 1 0 h₀).trans hG) ((hh 1 0 h₀).trans hH) u₁ v₁
  · rwa [hf 1 0 h₀, hf u₁ v₁ hN]
  · intro u v hu hn
    simpa only [hh u v hn, hg u v hn, hf u v hn] using hid u v hu hn

/-- For any polynomial substitution, unequal endpoint x values certify the
nonconstancy needed for Pell amplification. -/
theorem infinite_of_bivariate (F G H : Polynomial (ℚ[X])) (x₀ y₀ z₀ : ℤ)
    (hF : bival F 1 0 = x₀) (hG : bival G 1 0 = y₀) (hH : bival H 1 0 = z₀)
    (u₁ v₁ : ℚ) (hN : u₁^2-3*v₁^2=1) (hdist : bival F 1 0 ≠ bival F u₁ v₁)
    (hid : ∀ u v : ℚ, u^2-3*v^2=1 →
      (bival H u v)^2 + (bival G u v)^2 * bival H u v + (bival F u v)^3 = 2) :
    {p : ℤ × ℤ × ℤ | p.2.2 ^ 2 + p.2.1 ^ 2 * p.2.2 + p.1 ^ 3 = 2}.Infinite :=
  infinite_of_bivariate_on_chart F G H x₀ y₀ z₀ hF hG hH u₁ v₁ hN hdist
    (fun u v _ hn => hid u v hn)


private noncomputable def liftBasis : ℕ → ℕ → Polynomial (ℚ[X])
  | 0, _ => 1
  | m+1, 0 => C ((X+1)*C (1/2)) * liftBasis m 0
  | m+1, 1 => (X*C (C (1/2))) * liftBasis m 0
  | m+1, j+2 => C ((X-1)*C (1/6)) * liftBasis m j

private theorem liftBasis_spec (u v t L : ℚ)
    (h₀ : ((u+1)/2)*L=1) (h₁ : (v/2)*L=t) (h₂ : ((u-1)/6)*L=t^2)
    (m j : ℕ) (hj : j≤2*m) : bival (liftBasis m j) u v * L^m = t^j := by
  induction m generalizing j with
  | zero =>
    have : j=0 := by omega
    simp [this, liftBasis, bival]
  | succ m ih =>
    cases j with
    | zero =>
      have h := ih 0 (by omega)
      simp only [liftBasis, bival, eval₂_mul, eval₂_C, coe_evalRingHom, eval_mul,
        eval_add, eval_X, eval_one, eval_C, pow_succ, pow_zero] at h ⊢
      linear_combination ((u+1)/2*L)*h + h₀
    | succ j =>
      cases j with
      | zero =>
        have h := ih 0 (by omega)
        simp only [liftBasis, bival, eval₂_mul, eval₂_X, eval₂_C, coe_evalRingHom,
          eval_C, pow_succ, pow_zero, one_mul] at h ⊢
        linear_combination (v/2*L)*h + h₁
      | succ j =>
        have h := ih j (by omega)
        simp only [liftBasis, bival, eval₂_mul, eval₂_C, coe_evalRingHom, eval_mul,
          eval_sub, eval_X, eval_one, eval_C, pow_succ] at h ⊢
        linear_combination ((u-1)/6*L)*h + t^j*h₂

/-- Homogenizing a numerator of degree ≤ 2m gives a polynomial in u and v
whose chart value is P(t)/(1−3t²)ᵐ. -/
noncomputable def chartLift (m : ℕ) (P : ℚ[X]) : Polynomial (ℚ[X]) :=
  ∑ i ∈ P.support, C (C (P.coeff i)) * liftBasis m i

private theorem chartLift_eval (m : ℕ) (P : ℚ[X]) (hP : P.natDegree ≤ 2*m) (u v t L : ℚ)
    (h₀ : ((u+1)/2)*L=1) (h₁ : (v/2)*L=t) (h₂ : ((u-1)/6)*L=t^2) :
    bival (chartLift m P) u v * L^m = P.eval t := by
  rw [bival, chartLift, eval₂_finsetSum, Finset.sum_mul, Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro j hj
  have he := liftBasis_spec u v t L h₀ h₁ h₂ m j ((le_natDegree_of_mem_supp _ hj).trans hP)
  simp only [bival] at he
  rw [eval₂_mul, eval₂_C, coe_evalRingHom, eval_C, mul_assoc, he]

/-- Any nonconstant first coordinate in a quartic chart with one integral seed
amplifies to infinitely many integral solutions. -/
theorem infinite_of_nonconstant_quartic_chart (A B J : ℚ[X])
    (hA : A.natDegree ≤ 8) (hB : B.natDegree ≤ 6) (hJ : J.natDegree ≤ 12)
    (x₀ y₀ z₀ : ℤ)
    (hx : A.eval 0 = x₀) (hy : B.eval 0 = y₀) (hz : J.eval 0 = z₀)
    (hd : A ≠ C (x₀ : ℚ)*(1-3*X^2)^4)
    (hid : J^2+B^2*J+A^3=2*(1-3*X^2)^12) :
    {p : ℤ × ℤ × ℤ | p.2.2 ^ 2 + p.2.1 ^ 2 * p.2.2 + p.1 ^ 3 = 2}.Infinite := by
  have seed (m : ℕ) (P : ℚ[X]) (hP : P.natDegree ≤ 2*m) :
      bival (chartLift m P) 1 0 = P.eval 0 := by
    simpa using chartLift_eval m P hP 1 0 0 1 (by norm_num) (by norm_num) (by norm_num)
  let D : ℚ[X] := 1-3*X^2
  have hD : D ≠ 0 := by
    intro h
    have h₀ := congrArg (Polynomial.eval 0) h
    norm_num [D] at h₀
  have hdiff : (A-C (x₀ : ℚ)*D^4)*D ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hd) hD
  obtain ⟨s, hs⟩ : ∃ s : ℚ, ((A-C (x₀ : ℚ)*D^4)*D).eval s ≠ 0 := by
    by_contra! h
    exact hdiff (Polynomial.funext (fun s => by simpa using h s))
  rw [eval_mul] at hs
  obtain ⟨hs₁,hs₂⟩ := mul_ne_zero_iff.mp hs
  let d : ℚ := 1-3*s^2
  have hd₀ : d ≠ 0 := by simpa [D,d] using hs₂
  let u₁ : ℚ := (1+3*s^2)/d
  let v₁ : ℚ := 2*s/d
  have eqD : d=1-3*s^2 := rfl
  have norm₁ : u₁^2-3*v₁^2=1 := by dsimp [u₁,v₁]; field_simp; rw [eqD]; ring
  have e₀ : ((u₁+1)/2)*d=1 := by dsimp [u₁]; field_simp; rw [eqD]; ring
  have e₁ : (v₁/2)*d=s := by dsimp [v₁]; field_simp
  have e₂ : ((u₁-1)/6)*d=s^2 := by dsimp [u₁]; field_simp; rw [eqD]; ring
  apply infinite_of_bivariate_on_chart (chartLift 4 A) (chartLift 3 B) (chartLift 6 J)
    x₀ y₀ z₀ ((seed 4 A hA).trans hx) ((seed 3 B hB).trans hy) ((seed 6 J hJ).trans hz)
    u₁ v₁ norm₁
  · intro heq
    rw [seed 4 A hA,hx] at heq
    apply hs₁
    rw [eval_sub,eval_mul,eval_C,eval_pow]
    have hds : D.eval s = d := by simp [D,d]
    rw [hds]
    rw [heq,chartLift_eval 4 A hA u₁ v₁ s d e₀ e₁ e₂]
    ring
  · intro u v hu hn
    let t := v/(u+1)
    let L := 2/(u+1)
    have hu' : u+1 ≠ 0 := by intro h; apply hu; linarith
    have h₀ : ((u+1)/2)*L=1 := by dsimp [L]; field_simp
    have h₁ : (v/2)*L=t := by dsimp [t,L]; ring
    have h₂ : ((u-1)/6)*L=t^2 := by dsimp [t,L]; field_simp; nlinarith [hn]
    have hL : 1-3*t^2=L := by dsimp [t,L]; field_simp; nlinarith [hn]
    have hnz : L ≠ 0 := div_ne_zero (by norm_num) hu'
    have get (m : ℕ) (P : ℚ[X]) (hP : P.natDegree ≤ 2*m) :
        bival (chartLift m P) u v = P.eval t/L^m :=
      (eq_div_iff (pow_ne_zero _ hnz)).mpr (chartLift_eval m P hP u v t L h₀ h₁ h₂)
    rw [get 6 J hJ, get 3 B hB, get 4 A hA]
    have he := congrArg (Polynomial.eval t) hid
    simp at he
    rw [hL] at he
    field_simp
    linear_combination he

/-- The two points (1,0) and (2,1) correspond to t=0 and t=1/3. An exact
quartic-chart polynomial identity through those points suffices for infinitude. -/
theorem infinite_of_quartic_chart (A B J : ℚ[X])
    (hA : A.natDegree ≤ 8) (hB : B.natDegree ≤ 6) (hJ : J.natDegree ≤ 12)
    (x₀ y₀ z₀ : ℤ)
    (hx : A.eval 0 = x₀) (hy : B.eval 0 = y₀) (hz : J.eval 0 = z₀)
    (hd : A.eval (1/3) ≠ (x₀ : ℚ)*(2/3)^4)
    (hid : J^2+B^2*J+A^3=2*(1-3*X^2)^12) :
    {p : ℤ × ℤ × ℤ | p.2.2 ^ 2 + p.2.1 ^ 2 * p.2.2 + p.1 ^ 3 = 2}.Infinite := by
  apply infinite_of_nonconstant_quartic_chart A B J hA hB hJ x₀ y₀ z₀ hx hy hz _ hid
  intro h
  apply hd
  rw [h]
  norm_num

end SmallCubic.MixedPell
