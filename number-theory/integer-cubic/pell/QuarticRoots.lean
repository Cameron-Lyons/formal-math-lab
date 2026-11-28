module

public import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! A repeated root of a monic quartic over ℚ either gives a rational
repeated root or forces the quartic to be a square in ℚ[X]. -/
public section

namespace SmallCubic

/-- Elimination for a quartic with vanishing cubic coefficient. -/
private theorem depressed_quartic (K : Type*) [Field K] [CharZero K]
    (p q r : ℚ) (x : K)
    (hf : x^4 + (p:K)*x^2 + (q:K)*x + (r:K) = 0)
    (hd : 4*x^3 + 2*(p:K)*x + (q:K) = 0) :
    (∃ v : ℚ, (v:K) = x) ∨ (q = 0 ∧ 4*r = p^2) := by
  have hg : 2*(p:K)*x^2 + 3*(q:K)*x + 4*(r:K) = 0 := by
    linear_combination 4*hf - x*hd
  by_cases hq : q = 0
  · subst q
    have hx : x * (4*x^2 + 2*(p:K)) = 0 := by
      linear_combination hd
    rcases mul_eq_zero.mp hx with hx | hx
    · exact Or.inl ⟨0, by simpa using hx.symm⟩
    · right
      refine ⟨rfl, ?_⟩
      exact_mod_cast (show 4*(r:K) = (p:K)^2 by linear_combination hg - (p:K)/2*hx)
  let l := 2*p^3 - 8*p*r + 9*q^2
  let m := (p^2 + 12*r)*q
  have hx : (l:K)*x + (m:K) = 0 := by
    dsimp [l,m]
    push_cast
    linear_combination (p:K)^2*hd + (3*(q:K) - 2*(p:K)*x)*hg
  by_cases hl : l = 0
  · have hm : m = 0 := by
      rw [hl] at hx
      simpa using hx
    have hr : p^2 + 12*r = 0 := (mul_eq_zero.mp hm).resolve_right hq
    have hp : p ≠ 0 := by
      intro h
      simp [l,h,hq] at hl
    have hs : 9*q^2 - 32*p*r = 0 := by
      dsimp [l] at hl
      linear_combination hl - 2*p*hr
    have hx' : (4*(p:K)*x + 3*(q:K))^2 = 0 := by
      have hsk : 9*(q:K)^2 - 32*(p:K)*(r:K) = 0 := by exact_mod_cast hs
      linear_combination 8*(p:K)*hg + hsk
    have hlin := eq_zero_of_pow_eq_zero hx'
    left
    refine ⟨-3*q/(4*p), ?_⟩
    push_cast
    have hp' : (p:K) ≠ 0 := by exact_mod_cast hp
    field_simp [hp']
    linear_combination -hlin
  · left
    refine ⟨-m/l, ?_⟩
    push_cast
    have hl' : (l:K) ≠ 0 := by exact_mod_cast hl
    field_simp [hl']
    linear_combination -hx

/-- The repeated-root dichotomy for an arbitrary monic quartic. -/
theorem quartic_repeated_root (K : Type*) [Field K] [CharZero K]
    (A B C D : ℚ) (t : K)
    (hf : t^4+(A:K)*t^3+(B:K)*t^2+(C:K)*t+(D:K)=0)
    (hd : 4*t^3+3*(A:K)*t^2+2*(B:K)*t+(C:K)=0) :
    (∃ r : ℚ, r^4+A*r^3+B*r^2+C*r+D=0 ∧ 4*r^3+3*A*r^2+2*B*r+C=0) ∨
    (∃ p q : ℚ, ∀ s : ℚ, s^4+A*s^3+B*s^2+C*s+D=(s^2+p*s+q)^2) := by
  let h := A/4
  let p := B-6*h^2
  let q := C-2*B*h+8*h^3
  let r := D-C*h+B*h^2-3*h^4
  let x := t+(h:K)
  have H : x^4+(p:K)*x^2+(q:K)*x+(r:K)=0 := by
    dsimp [x,p,q,r,h]
    push_cast
    linear_combination hf
  have H' : 4*x^3+2*(p:K)*x+(q:K)=0 := by
    dsimp [x,p,q,h]
    push_cast
    linear_combination hd
  rcases depressed_quartic K p q r x H H' with ⟨v,hv⟩ | ⟨hq,hr⟩
  · left
    have ht : ((v-h : ℚ):K)=t := by push_cast; dsimp [x] at hv; rw [hv]; ring
    refine ⟨v-h, ?_, ?_⟩
    · exact_mod_cast (show ((v-h : ℚ):K)^4+(A:K)*((v-h:ℚ):K)^3+
          (B:K)*((v-h:ℚ):K)^2+(C:K)*((v-h:ℚ):K)+(D:K)=0 by rwa [ht])
    · exact_mod_cast (show 4*((v-h : ℚ):K)^3+3*(A:K)*((v-h:ℚ):K)^2+
          2*(B:K)*((v-h:ℚ):K)+(C:K)=0 by rwa [ht])
  · right
    refine ⟨2*h, h^2+p/2, fun s => ?_⟩
    dsimp [q,r,p,h] at *
    linear_combination (s+A/4)*hq + (1/4 : ℚ)*hr

end SmallCubic
