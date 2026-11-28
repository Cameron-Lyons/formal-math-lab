module

public import Mathlib.Algebra.Field.ZMod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

public section

namespace SmallCubic.QuarticLift

abbrev F := ZMod 7
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The six free first-lift parameters, ordered by the free Jacobian columns. -/
structure Digits where
  a : F
  b : F
  c : F
  d : F
  e : F
  s : F
  deriving DecidableEq

private def monomials (v : Digits) : List F :=
  let ⟨a, b, c, d, e, s⟩ := v
  [1, a, b, c, d, e, s, a^2, b^2, c^2, d^2, e^2, s^2,
    a*b, a*c, a*d, a*e, a*s, b*c, b*d, b*e, b*s, c*d, c*e, c*s, d*e, d*s, e*s]

/-- The row-reduced quadratic obstruction forms for the representative X=3t⁴.
The accompanying checker derives these rows from the 24 full residual coefficients. -/
private def row (i : Fin 4) : List F := match i.val with
  | 0 => [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 1 => [0, 1, 0, 1, 2, 3, 4, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 2 => [0, 0, 1, 0, 1, 2, 3, 3, 0, 3, 5, 6, 4, 0, 6, 5, 4, 3, 0, 0, 0, 0, 5, 4, 3, 1, 6, 0]
  | _ => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

def pilotObstruction (v : Digits) (i : Fin 4) : F :=
  ((row i).zipWith (· * ·) (monomials v)).sum

private def compressed (v : Digits) (i : Fin 4) : F :=
  let ⟨a, b, c, d, e, s⟩ := v
  let A := a + c + 2*d + 3*e
  match i.val with
  | 0 => 1 - s^2
  | 1 => A + 4*s + 3*s^2
  | 2 => b + d + 2*e + 3*s + 3*A^2 + 4*s^2 + 3*s*A - 2*e*s
  | _ => e*s

private theorem compressed_eq (v : Digits) (i : Fin 4) :
    pilotObstruction v i = compressed v i := by
  rcases v with ⟨a,b,c,d,e,s⟩
  fin_cases i <;> simp [pilotObstruction, row, monomials, compressed] <;> ring_nf
  · rw [show (6:F) = -1 by decide]
    ring
  · simp [show (36:F) = 1 by decide, show (12:F) = 5 by decide, show (7:F) = 0 by decide,
      show (18:F) = 4 by decide, show (27:F) = 6 by decide]

def fromParameters (c d s : F) : Digits :=
  ⟨-c - 2*d - 4*s - 3, -d - 3*s - 4, c, d, 0, s⟩

/-- The last free digit is ±1, two digits are arbitrary, and the other three
are uniquely determined by the four quadratic equations. -/
theorem pilot_digits_iff (v : Digits) :
    (∀ i, pilotObstruction v i = 0) ↔
    (v.s = 1 ∨ v.s = -1) ∧ v = fromParameters v.c v.d v.s := by
  rcases v with ⟨a, b, c, d, e, s⟩
  simp only [compressed_eq]
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    simp [compressed] at h0 h1 h2 h3
    have hs : s^2 = 1 := by linear_combination -h0
    have hs' := sq_eq_one_iff.mp hs
    have he : e = 0 := h3.resolve_right (by intro hz; rw [hz] at hs; exact (by decide : (0:F)^2 ≠ 1) hs)
    subst e
    refine ⟨hs', ?_⟩
    have ha : a = -c - 2*d - 4*s - 3 := by linear_combination h1 - 3*hs
    have hb : b = -d - 3*s - 4 := by
      rw [ha] at h2
      rcases hs' with rfl | rfl <;> ring_nf at h2 ⊢ <;> grind
    simp [fromParameters, ha, hb]
  · rintro ⟨hs, h⟩ i
    change (s = 1 ∨ s = -1) at hs
    simp [fromParameters] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rcases hs with rfl | rfl <;> fin_cases i <;> simp [compressed] <;> ring_nf ; decide

private def parameterEquiv :
    {v : Digits // ∀ i, pilotObstruction v i = 0} ≃
      {s : F // s = 1 ∨ s = -1} × F × F where
  toFun v := (⟨v.val.s, ((pilot_digits_iff _).mp v.property).1⟩, v.val.c, v.val.d)
  invFun u := ⟨fromParameters u.2.1 u.2.2 u.1.val,
    (pilot_digits_iff _).mpr ⟨u.1.property, rfl⟩⟩
  left_inv v := Subtype.ext ((pilot_digits_iff _).mp v.property).2.symm
  right_inv _ := rfl

/-- Exactly 98 choices of the six first correction digits annul all four
projected equations. -/
theorem pilot_survivor_count :
    Nat.card {v : Digits // ∀ i, pilotObstruction v i = 0} = 98 := by
  rw [Nat.card_congr parameterEquiv, Nat.card_eq_fintype_card]
  decide

end SmallCubic.QuarticLift
