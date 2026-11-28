module

public import QuadraticIntegers
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The elementary descent for the Mordell equation in the ring of integers
of ℚ(√−2). -/

public section

namespace SmallCubic

private abbrev R := Zsqrtd (-2)

/-- Any solution makes the norms of the two factors congruent to three
modulo eight. This gives an explicit Bézout identity for the factors. -/
private theorem conjugate_coprime (u v : ℤ) (h : v^2 + 2 = u^3) :
    IsCoprime (⟨v, 1⟩ : R) (⟨v, -1⟩ : R) := by
  have hmod := congrArg (fun a : ℤ => (a : ZMod 8)) h
  push_cast at hmod
  have residue : ∀ a b : ZMod 8, b^2 + 2 = a^3 → 3 * (b^2+2) - 1 = 0 := by decide
  have hdiv : (8 : ℤ) ∣ 3*(v^2+2)-1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp
    push_cast
    exact residue _ _ hmod
  obtain ⟨k, hk⟩ := hdiv
  refine ⟨⟨3*v, -3+2*k⟩, ⟨0, -2*k⟩, ?_⟩
  ext <;> simp <;> nlinarith

/-- A unit in ℤ[√−2] is its own cube. -/
private theorem unit_cube (e : Rˣ) : (e : R)^3 = e := by
  have hn := (Zsqrtd.norm_eq_one_iff' (d := -2) (by decide) (e : R)).mpr e.isUnit
  rw [Zsqrtd.norm_def] at hn
  have him : (e : R).im = 0 := by
    by_contra h
    have := sq_pos_of_ne_zero h
    nlinarith [sq_nonneg (e : R).re]
  have hrsq : (e : R).re ^ 2 = 1 := by rw [him] at hn; nlinarith
  ext <;> simp [pow_succ, him]; nlinarith [congrArg (fun n : ℤ => n * (e : R).re) hrsq]

private theorem classify_cubic_factor (v : ℤ) (d : R) (hd : d^3 = ⟨v, 1⟩) :
    v = 5 ∨ v = -5 := by
  obtain ⟨a,b⟩ := d
  have hi := congrArg Zsqrtd.im hd
  have hr := congrArg Zsqrtd.re hd
  simp [pow_succ] at hi hr
  have hb : b ∣ (1 : ℤ) := ⟨3*a^2-2*b^2, by nlinarith⟩
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hb) with h | h <;> subst b
  · have ha : a = 1 ∨ a = -1 := by
      have hsq : (a-1)*(a+1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hsq with h | h <;> omega
    rcases ha with rfl | rfl <;> norm_num at hr <;> omega
  · have hs : 3 * a^2 = 1 := by nlinarith
    omega

local instance : EuclideanDomain (Zsqrtd (-2)) := sqrtNegTwoEuclidean
local instance : IsPrincipalIdealRing (Zsqrtd (-2)) :=
  @EuclideanDomain.instIsPrincipalIdealRing _ sqrtNegTwoEuclidean

/-- Descent in a Bézout domain gives the two integer points on v²=u³−2. -/
theorem mordell_classification
    (u v : ℤ) (h : v^2 + 2 = u^3) : u = 3 ∧ (v = 5 ∨ v = -5) := by
  have hp : (⟨v, 1⟩ : R) * ⟨v,-1⟩ = (u : R)^3 := by
    ext <;> simp [pow_succ]; nlinarith
  obtain ⟨d,e,he⟩ := exists_associated_pow_of_mul_eq_pow' (conjugate_coprime u v h) hp
  have heq : (d*(e:R))^3 = ⟨v,1⟩ := by rw [mul_pow, unit_cube, he]
  have hv := classify_cubic_factor v _ heq
  refine ⟨?_, hv⟩
  have hc : u^3 = 27 := by rcases hv with rfl | rfl <;> norm_num at h <;> omega
  have ht : (u-3)*(u^2+3*u+9) = 0 := by nlinarith
  rcases mul_eq_zero.mp ht with hu | hu
  · omega
  · nlinarith [sq_nonneg (2*u+3)]

end SmallCubic
