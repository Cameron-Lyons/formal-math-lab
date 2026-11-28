module

public import CubicEliminantData
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! The root certificate for the degree-1148 eliminant.
The Python script checks the discriminants and the exact factor coefficients. -/
public section
namespace SmallCubic.Eliminant

/-- Evaluate the homogenization at (u,v), with lower coefficients in ascending order. -/
@[expose] def homog {R : Type*} [CommRing R] (lc : ℤ) (u v : R) : List ℤ → R
  | [] => lc
  | c :: cs => (c : R) * v ^ (cs.length+1) + u * homog lc u v cs

private theorem homog_scale {R : Type*} [CommRing R] (lc : ℤ) (u v k : R) (cs : List ℤ) :
    homog lc (k*u) (k*v) cs = k^cs.length * homog lc u v cs := by
  induction cs with
  | nil => simp [homog]
  | cons c cs ih => simp only [homog, List.length_cons, ih, mul_pow, pow_succ]; ring

private theorem homog_cast {R : Type*} [CommRing R] (lc u v : ℤ) (cs : List ℤ) :
    ((homog lc u v cs : ℤ) : R) = homog lc (u : R) (v : R) cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [homog, ih]

/-- A homogeneous polynomial with no projective zero modulo p has no rational root. -/
theorem no_rat_root (p : ℕ) [Fact p.Prime] (lc : ℤ) (cs : List ℤ)
    (h : ∀ u v : ZMod p, homog lc u v cs = 0 → u = 0 ∧ v = 0) (q : ℚ) :
    homog lc q 1 cs ≠ 0 := by
  intro hq
  have hnum : (q.den : ℚ)*q = q.num := by simp [mul_comm]
  have hZ : homog lc q.num (q.den : ℤ) cs = 0 := by
    apply (Int.cast_injective (α := ℚ))
    rw [homog_cast]
    push_cast
    simpa [hnum, hq] using homog_scale lc q 1 (q.den : ℚ) cs
  have hm := congrArg (fun n : ℤ => (n : ZMod p)) hZ
  rw [homog_cast, Int.cast_zero] at hm
  obtain ⟨hu, hv⟩ := h _ _ hm
  obtain ⟨a,b,hab⟩ := q.isCoprime_num_den
  have hab' := congrArg (fun n : ℤ => (n : ZMod p)) hab
  push_cast at hab' hv
  simp [hu,hv] at hab'

-- These tests cover every projective point, including a zero denominator after reduction.
set_option maxHeartbeats 0 in
private theorem cert37 : ∀ u v : ZMod 5, homog lead37 u v low37 = 0 → u = 0 ∧ v = 0 := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem cert62 : ∀ u v : ZMod 5, homog lead62 u v low62 = 0 → u = 0 ∧ v = 0 := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem cert44 : ∀ u v : ZMod 13, homog lead44 u v low44 = 0 → u = 0 ∧ v = 0 := by
  decide +kernel

/-- Primitive factors of the projected discriminant with their exact multiplicities.
An overall nonzero scalar has no effect on its roots. -/
def projected (W : ℚ) : ℚ :=
  W^195 * (2*W-1)^660 * homog lead37 W 1 low37 *
    (homog lead62 W 1 low62)^2 * (homog lead44 W 1 low44)^3

theorem projected_eq_zero_iff (W : ℚ) : projected W = 0 ↔ W = 0 ∨ W = 1/2 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 13) := ⟨by decide⟩
  have h37 := no_rat_root 5 lead37 low37 cert37 W
  have h62 := no_rat_root 5 lead62 low62 cert62 W
  have h44 := no_rat_root 13 lead44 low44 cert44 W
  have half : 2*W-1 = 0 ↔ W = 1/2 := by constructor <;> intro h <;> linarith
  simp [projected, h37, h62, h44, half]

/-- All six full-pole residue classes have W ≡ 1 modulo 7. -/
theorem no_rational_cubic_branch_parameter (W : ℚ)
    (h7 : (W.num : ZMod 7) = (W.den : ZMod 7)) : projected W ≠ 0 := by
  intro h
  rcases (projected_eq_zero_iff W).mp h with rfl | rfl
  · revert h7; decide
  · have hhalf : (1/2 : ℚ) = ((2 : ℕ) : ℚ)⁻¹ := by norm_num
    rw [hhalf, Rat.inv_natCast_num_of_pos (a := 2) (by decide),
        Rat.inv_natCast_den_of_pos (a := 2) (by decide)] at h7
    exact (by decide : ((1 : ℤ) : ZMod 7) ≠ ((2 : ℕ) : ZMod 7)) h7

/-- Change of variables used to recover the symmetric nine-variable system. -/
theorem reflection_identity (t b : ℚ) :
    (1+2*b*t+3*t^2)^2 =
      (1-3*t^2)^2 + 4*b*(t+b*t^2)*(1-3*t^2) + 12*(t+b*t^2)^2 := by ring

/-- The normalized cubic divisor and its interpolation polynomial evaluated
in the pure cubic field. The only relation needed here is α³=2. -/
theorem normalized_cubic_root {K : Type*} [Field K] (α w : K) (h : α^3 = 2) :
    let W := w^3
    let S := w*(α+w*α^2)
    S^3 - 6*W*S - 2*W - 4*W^2 = 0 ∧ S - S^2 + 4*W = w*(1-2*W)*α := by
  dsimp
  constructor
  · linear_combination (w^6*(α^3+2) + 3*w^5*α^2 + 3*w^4*α + w^3)*h
  · linear_combination -(w^4*α+2*w^3)*h

end SmallCubic.Eliminant
