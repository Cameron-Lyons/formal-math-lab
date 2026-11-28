module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Set.Finite.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Osculating quadratics to v² = c⁴+8 give rational polynomial curves on
the original cubic surface. A local obstruction prevents all of these
parametrizations from having an integer second coordinate. -/

public section
namespace SmallCubic.Osculating

@[expose] def A {R : Type*} [CommRing R] (m n : R) : R :=
  3*m^8+48*m^4*n^4-64*n^8

@[expose] def B {R : Type*} [CommRing R] (m n : R) : R :=
  m^8-48*m^4*n^4-192*n^8

/-- Dividing by v³ gives the quadratic in y with second-order contact at (c,v). -/
def numerator (c y : ℚ) : ℚ :=
  c^2*(c^4+24)*y^2-32*c^3*y+8*(3*c^4+8)

theorem contact_factor (c v y : ℚ) (h : v^2=c^4+8) :
    v^6*(y^4+8)-(numerator c y)^2 =
      -8*(y-c)^3*(A c 1*y+c*B c 1) := by
  rw [show v^6=(v^2)^3 by ring, h]
  unfold numerator A B
  ring

private theorem int_of_pow (u : ℚ) (k : ℤ) (d : ℕ) (hd : d ≠ 0)
    (h : u^d=(k : ℚ)) : (u.num : ℚ)=u := by
  apply Rat.intCast_num_of_den_eq_one
  have hn : u.den^d=1 := by simpa [Rat.den_pow] using congrArg Rat.den h
  exact (pow_eq_one_iff_of_nonneg (Nat.zero_le _) hd).mp hn

theorem leading_ne_zero (c : ℚ) : A c 1 ≠ 0 := by
  intro h
  let q := (3*c^4+24)/16
  have hq : q^2=(3 : ℚ) := by
    dsimp [q]
    dsimp [A] at h
    linear_combination 3*h/256
  have hi := int_of_pow q 3 2 (by decide) hq
  have hz : q.num^2=(3 : ℤ) := by
    exact_mod_cast (show (q.num : ℚ)^2=3 by rw [hi]; exact hq)
  have hm := congrArg (fun k : ℤ => (k : ZMod 4)) hz
  push_cast at hm
  exact (by decide : ∀ a : ZMod 4, a^2 ≠ 3) _ hm

/-- The second coordinate is a cubic polynomial in t. -/
def yParam (c v t : ℚ) : ℚ := (-v^6*t^3/2-c*B c 1)/A c 1

theorem parameter_relation (c v t : ℚ) :
    v^6*t^3 = -2*(A c 1*yParam c v t+c*B c 1) := by
  unfold yParam
  field_simp [leading_ne_zero c]
  ring

/-- Every rational osculation point gives a rational polynomial substitution.
Here x=t(y−c), and w=2z+y² is the osculating quadratic. -/
theorem polynomial_family (c v t : ℚ) (h : v^2=c^4+8) :
    let y := yParam c v t
    let x := t*(y-c)
    let z := ((numerator c y)/v^3-y^2)/2
    z^2+y^2*z+x^3=2 := by
  have hv : v ≠ 0 := by intro hv; rw [hv] at h; nlinarith [sq_nonneg (c^2)]
  let y := yParam c v t
  have ht := parameter_relation c v t
  change v^6*t^3 = -2*(A c 1*y+c*B c 1) at ht
  change ((numerator c y/v^3-y^2)/2)^2+
    y^2*((numerator c y/v^3-y^2)/2)+(t*(y-c))^3=2
  field_simp [hv]
  linear_combination -contact_factor c v y h+4*(y-c)^3*ht

set_option maxHeartbeats 0 in
private theorem local13 : ∀ a b k : ZMod 13, k^2=a^4+8*b^4 →
    b*A a b=0 ∧ ((-2*a*B a b)^4=3 ∨ (a=0 ∧ b=0)) := by
  decide +kernel

theorem no_integral_y (c v t : ℚ) (y : ℤ) (h : v^2=c^4+8)
    (ht : v^6*t^3 = -2*(A c 1*(y : ℚ)+c*B c 1)) : False := by
  let m := c.num
  let n : ℤ := c.den
  have hn : (n : ℚ)*c=(m : ℚ) := by simp [m,n,mul_comm]
  let k := (n : ℚ)^2*v
  have hk : k^2=((m^4+8*n^4 : ℤ) : ℚ) := by
    push_cast
    rw [← hn]
    dsimp [k]
    linear_combination (n : ℚ)^4*h
  have hki := int_of_pow k _ 2 (by decide) hk
  have hkZ : k.num^2=m^4+8*n^4 := by
    exact_mod_cast (show (k.num : ℚ)^2=(((m^4+8*n^4 : ℤ)) : ℚ) by rw [hki]; exact hk)
  let s := t*v^2*(n : ℚ)^3
  have hs : s^3=((-2*(n*A m n*y+m*B m n) : ℤ) : ℚ) := by
    unfold A B
    push_cast
    rw [← hn]
    dsimp [s]
    dsimp [A,B] at ht
    linear_combination (n : ℚ)^9*ht
  have hsi := int_of_pow s _ 3 (by decide) hs
  have hsZ : s.num^3 = -2*(n*A m n*y+m*B m n) := by
    exact_mod_cast (show (s.num : ℚ)^3=((-2*(n*A m n*y+m*B m n) : ℤ) : ℚ) by
      rw [hsi]; exact hs)
  have hk13 := congrArg (fun j : ℤ => (j : ZMod 13)) hkZ
  have hs13 := congrArg (fun j : ℤ => (j : ZMod 13)) hsZ
  dsimp [A,B] at hs13
  push_cast at hk13 hs13
  change (s.num : ZMod 13)^3 =
    -2*((n : ZMod 13)*A (m : ZMod 13) (n : ZMod 13)*(y : ZMod 13)
      +(m : ZMod 13)*B (m : ZMod 13) (n : ZMod 13)) at hs13
  obtain ⟨ha,hb⟩ := local13 _ _ _ hk13
  rw [ha, zero_mul, zero_add, ← mul_assoc] at hs13
  rcases hb with hc | ⟨hm, hd⟩
  · rw [← hs13] at hc
    exact (by decide : ∀ j : ZMod 13, (j^3)^4 ≠ 3) _ hc
  · obtain ⟨p,q,hcop⟩ := c.isCoprime_num_den
    have hh := congrArg (fun j : ℤ => (j : ZMod 13)) hcop
    push_cast at hh
    change (p : ZMod 13)*(m : ZMod 13)+(q : ZMod 13)*(n : ZMod 13)=1 at hh
    simp [hm,hd] at hh
    exact (by decide : (0 : ZMod 13) ≠ 1) hh

/-- No rational parameter on any of these curves yields an integral y. -/
theorem parameter_not_integer (c v t : ℚ) (h : v^2=c^4+8) (n : ℤ) :
    yParam c v t ≠ (n : ℚ) := by
  intro hn
  apply no_integral_y c v t n h
  simpa [← hn] using parameter_relation c v t

/-- The osculating family at (c,v)=(1,3), with parameter u=9t. -/
def explicitPoint (u : ℚ) : ℚ × ℚ × ℚ :=
  let y := (u^3-478)/26
  (u*(y-1)/9, y, (44-16*y-y^2)/27)

theorem explicit_family (u : ℚ) :
    let p := explicitPoint u
    p.2.2^2+p.2.1^2*p.2.2+p.1^3=2 := by
  dsimp [explicitPoint]
  ring

theorem explicit_y_not_integer (u : ℚ) (n : ℤ) : (explicitPoint u).2.1 ≠ (n : ℚ) := by
  have he : (explicitPoint u).2.1 = yParam 1 3 (u/9) := by
    dsimp [explicitPoint,yParam,A,B]
    ring
  rw [he]
  exact parameter_not_integer 1 3 (u/9) (by norm_num) n

theorem infinitely_many_rational_solutions :
    {p : ℚ × ℚ × ℚ | p.2.2^2+p.2.1^2*p.2.2+p.1^3=2}.Infinite := by
  have hinj : Function.Injective explicitPoint := by
    intro a b h
    have he := congrArg (fun p : ℚ × ℚ × ℚ => p.2.1) h
    dsimp [explicitPoint] at he
    apply (show Odd 3 by decide).pow_injective
    linear_combination 26*he
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨u,rfl⟩
  exact explicit_family u

end SmallCubic.Osculating
