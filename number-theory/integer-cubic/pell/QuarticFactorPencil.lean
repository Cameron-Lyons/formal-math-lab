module

public import SmallCubic
public import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Cubic factors of 2 − x(s)³ for a quadratic polynomial x. Here a,b
are the coordinates of a generator a∛2 + b∛4. The discriminant obstruction
uses the two complementary cubic factors simultaneously. -/
public section

namespace SmallCubic.FactorPencil

local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

def D (a b : ℚ) := a^3 - 2*b^3
def P (a b s : ℚ) := s^3 - 6*a*b*s - 2*a^3 - 4*b^3
def G (a b s : ℚ) := a^2*s - b*s^2 + 4*a*b^2
def Q (a b s : ℚ) := b^3*s^3 - 3*a^2*b^2*s^2 +
  (3*a^4*b - 6*a*b^4)*s - a^6 + 8*a^3*b^3 + 4*b^6

theorem factor_identity (a b s : ℚ) :
    2*(D a b)^3 - (G a b s)^3 = P a b s * Q a b s := by
  unfold D G P Q
  ring

/-- The homogeneous equation for the sum of the two complementary scalars. -/
def cert {R : Type*} [CommRing R] (A B u v h : R) : R :=
  let d := A - 2*B
  let S := d^3*(u^2 + v^2)
  4*d^2*S^2 - 4*A*d*(A + 16*B)*S*h^2 +
    (A^4 - 32*A^3*B + 64*A^2*B^2 - 192*A*B^3 - 64*B^4)*h^4

private theorem residue_affine (A B u v : ZMod 13)
    (hA : A = 0 ∨ A = 1 ∨ A = 5 ∨ A = 8 ∨ A = 12)
    (hB : B = 0 ∨ B = 1 ∨ B = 5 ∨ B = 8 ∨ B = 12)
    (hn : A ≠ 0 ∨ B ≠ 0)
    (hp : (A-2*B)^3*u*v = B) (hc : cert A B u v 1 = 0) : False := by
  revert hp hc
  rcases hA with rfl | rfl | rfl | rfl | rfl <;>
    rcases hB with rfl | rfl | rfl | rfl | rfl <;>
    first | exact (hn.elim (· rfl) (· rfl)).elim | revert u v; decide

private theorem residue (a b u v h : ZMod 13) (hn : a ≠ 0 ∨ b ≠ 0)
    (hp : (a^3-2*b^3)^3*u*v = b^3*h^2)
    (hc : cert (a^3) (b^3) u v h = 0) : u = 0 ∧ v = 0 ∧ h = 0 := by
  have dn : a^3 - 2*b^3 ≠ 0 := (by decide :
    ∀ a b : ZMod 13, a ≠ 0 ∨ b ≠ 0 → a^3-2*b^3 ≠ 0) a b hn
  by_cases hh : h = 0
  · subst h
    simp [cert] at hc
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero] at hp
    have huv : u*v = 0 := by
      apply (mul_eq_zero.mp (show (a^3-2*b^3)^3 * (u*v) = 0 by
        simpa only [← mul_assoc] using hp)).resolve_left (pow_ne_zero _ dn)
    have hs : u^2+v^2 = 0 := by
      apply eq_zero_of_pow_eq_zero (n := 2)
      simpa [cert, mul_pow, mul_assoc, dn, show (4 : ZMod 13) ≠ 0 by decide] using hc
    rcases mul_eq_zero.mp huv with hu | hv
    · simp_all
    · simp_all
  · have cubes : ∀ t : ZMod 13, t^3=0 ∨ t^3=1 ∨ t^3=5 ∨ t^3=8 ∨ t^3=12 := by decide
    exfalso
    apply residue_affine (a^3) (b^3) (u/h) (v/h) (cubes a) (cubes b)
      (hn.imp (pow_ne_zero 3) (pow_ne_zero 3))
    · field_simp
      linear_combination hp
    · unfold cert at *
      field_simp
      linear_combination hc

/-- Clear a common rational denominator, then descend on it using the
projective residue obstruction. -/
private theorem no_integer_certificate (a b : ℤ)
    (hn : (a : ZMod 13) ≠ 0 ∨ (b : ZMod 13) ≠ 0) (h : ℕ) (hh : 0 < h)
    (u v : ℤ) (hp : (a^3-2*b^3)^3*u*v = b^3*(h:ℤ)^2)
    (hc : cert (a^3) (b^3) u v (h:ℤ) = 0) : False := by
  induction h using Nat.strong_induction_on generalizing u v with
  | ind h ih =>
    have rp := congrArg (fun k : ℤ => (k : ZMod 13)) hp
    have rc := congrArg (fun k : ℤ => (k : ZMod 13)) hc
    unfold cert at rc
    push_cast at rp rc
    obtain ⟨eu,ev,eh⟩ := residue _ _ _ _ _ hn rp rc
    obtain ⟨U,hU⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 13).mp eu
    obtain ⟨V,hV⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 13).mp ev
    obtain ⟨H,hH⟩ := (ZMod.natCast_eq_zero_iff h 13).mp eh
    apply ih H (by omega) (by omega) U V
    · rw [hU,hV,hH] at hp
      push_cast at hp
      apply mul_left_cancel₀ (show (169 : ℤ) ≠ 0 by decide)
      linear_combination hp
    · rw [hU,hV,hH] at hc
      unfold cert at *
      push_cast at hc
      apply mul_left_cancel₀ (show (28561 : ℤ) ≠ 0 by decide)
      linear_combination hc

private theorem no_rat_certificate (a b : ℤ)
    (hn : (a : ZMod 13) ≠ 0 ∨ (b : ZMod 13) ≠ 0) (u v : ℚ)
    (hp : (D a b)^3*u*v = (b:ℚ)^3)
    (hc : cert ((a:ℚ)^3) ((b:ℚ)^3) u v 1 = 0) : False := by
  let h := u.den * v.den
  let U := u.num * (v.den : ℤ)
  let V := v.num * (u.den : ℤ)
  have hu : (U:ℚ) = u*(h:ℚ) := by
    dsimp [U,h]; push_cast; rw [← Rat.mul_den_eq_num]; ring
  have hv : (V:ℚ) = v*(h:ℚ) := by
    dsimp [V,h]; push_cast; rw [← Rat.mul_den_eq_num]; ring
  apply no_integer_certificate a b hn h (Nat.mul_pos u.den_pos v.den_pos) U V
  · unfold D at hp
    exact_mod_cast (show ((a:ℚ)^3-2*(b:ℚ)^3)^3*U*V=(b:ℚ)^3*(h:ℚ)^2 by
      rw [hu,hv]; linear_combination (h:ℚ)^2*hp)
  · unfold cert at *
    apply (Int.cast_injective (α := ℚ))
    push_cast
    rw [hu,hv]
    linear_combination (h:ℚ)^4*hc

/-- Coefficients of Q − l P in descending degree. -/
def pencil (a b l : ℚ) : Cubic ℚ :=
  ⟨b^3 - l, -3*a^2*b^2, 3*a^4*b - 6*a*b^4 + 6*l*a*b,
    -a^6 + 8*a^3*b^3 + 4*b^6 + l*(2*a^3+4*b^3)⟩

theorem pencil_value (a b l s : ℚ) :
    (pencil a b l).a*s^3 + (pencil a b l).b*s^2 + (pencil a b l).c*s +
      (pencil a b l).d = Q a b s - l*P a b s := by
  unfold pencil Q P
  ring

private theorem discr_certificate (a b u : ℚ) (hu : u ≠ 0) (hd : D a b ≠ 0)
    (he : (pencil a b ((D a b)^3*u^2)).discr = 0) :
    cert (a^3) (b^3) u (b^3 / ((D a b)^3*u)) 1 = 0 := by
  let d := D a b
  let l := d^3*u^2
  let A := a^3
  let B := b^3
  let K := A^4 - 32*A^3*B + 64*A^2*B^2 - 192*A*B^3 - 64*B^4
  have hh : 4*d^2*(l^2+B^2)^2 -
      4*A*d*(A+16*B)*(l^2+B^2)*l + K*l^2 = 0 := by
    dsimp [l,d,A,B,K,D]
    unfold pencil Cubic.discr D at he
    linear_combination (-1/27 : ℚ)*he
  have hl : l ≠ 0 := mul_ne_zero (pow_ne_zero _ hd) (pow_ne_zero _ hu)
  have hj : d^3*(u^2 + (B/(d^3*u))^2) = (l^2+B^2)/l := by
    dsimp [l]; field_simp [show d ≠ 0 from hd,hu]
  change 4*d^2*(d^3*(u^2+(B/(d^3*u))^2))^2 -
    4*A*d*(A+16*B)*(d^3*(u^2+(B/(d^3*u))^2))*1^2 + K*1^4 = 0
  rw [hj]
  field_simp [hl]
  linear_combination hh

/-- For every normalized pair of generator coordinates, the cubic factor
pencil has nonzero discriminant at every nonzero rational scale. In
particular, a cubic of full degree in this family cannot lose a square
factor to leave a Pell equation. -/
theorem discriminant_ne_zero (a b : ℤ)
    (hn : (a : ZMod 13) ≠ 0 ∨ (b : ZMod 13) ≠ 0) (u : ℚ) (hu : u ≠ 0) :
    (pencil a b ((D a b)^3*u^2)).discr ≠ 0 := by
  have hd : D a b ≠ 0 := by
    intro hz
    unfold D at hz
    have eq : a^3-2*b^3 = (0 : ℤ) := by exact_mod_cast hz
    have red := congrArg (fun k : ℤ => (k : ZMod 13)) eq
    push_cast at red
    exact (by decide : ∀ a b : ZMod 13, a ≠ 0 ∨ b ≠ 0 → a^3-2*b^3 ≠ 0) _ _ hn red
  intro he
  apply no_rat_certificate a b hn u ((b:ℚ)^3 / ((D a b)^3*u))
  · field_simp [hd,hu]
  · exact discr_certificate _ _ _ hu hd he

private theorem scale_discr (a b k u : ℚ) :
    (pencil (k*a) (k*b) ((D (k*a) (k*b))^3*u^2)).discr =
      k^18*(pencil a b ((D a b)^3*(k^3*u)^2)).discr := by
  unfold pencil Cubic.discr D
  ring

/-- The obstruction holds over the whole rational pencil, including
generators with either coordinate zero and arbitrarily large denominators. -/
theorem rational_discriminant_ne_zero (a b u : ℚ) (hn : a ≠ 0 ∨ b ≠ 0)
    (hu : u ≠ 0) : (pencil a b ((D a b)^3*u^2)).discr ≠ 0 := by
  suffices H : ∃ A B : ℤ, ∃ k : ℚ, k ≠ 0 ∧
      ((A : ZMod 13) ≠ 0 ∨ (B : ZMod 13) ≠ 0) ∧ a=k*A ∧ b=k*B by
    obtain ⟨A,B,k,hk,hab,ha,hb⟩ := H
    rw [ha,hb,scale_discr]
    exact mul_ne_zero (pow_ne_zero _ hk)
      (discriminant_ne_zero A B hab _ (mul_ne_zero (pow_ne_zero _ hk) hu))
  by_cases ha : a=0
  · exact ⟨0,1,b,hn.resolve_left (not_not.mpr ha),Or.inr (by decide),by simp [ha],by simp⟩
  · let r := b/a
    have hr : ((r.den:ℤ) : ZMod 13) ≠ 0 ∨ (r.num : ZMod 13) ≠ 0 := by
      by_contra! h
      obtain ⟨p,q,hc⟩ := r.isCoprime_num_den
      have hc' := congrArg (fun n : ℤ => (n : ZMod 13)) hc
      push_cast at hc' h
      simp [h.1,h.2] at hc'
    have hd : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
    refine ⟨r.den,r.num,a/r.den,div_ne_zero ha hd,hr,by push_cast; field_simp,?_⟩
    rw [← Rat.mul_den_eq_num]
    dsimp [r]
    field_simp

/-- Leading-coefficient cancellation does give a conic, but every point of
it lies on an even quadratic tangent graph excluded for integer triples. -/
theorem no_integer_point_of_leading_zero (a b s u : ℚ) (hu : u ≠ 0)
    (hd : D a b ≠ 0) (hl : b^3 = (D a b)^3*u^2) (x y z : ℤ)
    (hx : (x:ℚ)*D a b = G a b s)
    (hy : u*(D a b)^3*(y:ℚ)^2 = Q a b s - b^3*P a b s)
    (hs : z^2+y^2*z+x^3=2) : False := by
  have hb : b ≠ 0 := by
    intro h; subst b; simp [hd,hu] at hl
  let U := a/b
  let V := u*(D a b)^2/b^3
  have hM : V^2 = U^3-2 := by
    dsimp [V,U]
    field_simp [hb]
    unfold D at *
    linear_combination -(a^3-2*b^3)*hl
  have ht : 3*U^2*(x:ℚ) = V*(y:ℚ)^2 + U^3+4 := by
    dsimp [U,V]
    field_simp [hb]
    apply mul_left_cancel₀ hd
    unfold P Q G D at *
    linear_combination 3*a^2*b*hx - hy
  obtain ⟨m,n,hm,hn⟩ := tangent_parameters_integral U V x y hM ht
  rw [← hm, ← hn] at hM ht
  have hh : n^2+2 = m^3 := by
    exact_mod_cast (show (n:ℚ)^2+2=(m:ℚ)^3 by linarith)
  obtain ⟨rfl, hh'⟩ := mordell_classification m n hh
  apply integral_tangent_branches_excluded x y z hs
  rcases hh' with rfl | rfl
  · right
    exact_mod_cast (show 27*(x:ℚ)=31+5*(y:ℚ)^2 by push_cast at ht; linarith)
  · left
    exact_mod_cast (show 27*(x:ℚ)=31-5*(y:ℚ)^2 by push_cast at ht; linarith)

end SmallCubic.FactorPencil
