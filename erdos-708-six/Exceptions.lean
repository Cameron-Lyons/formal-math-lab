module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Tactic

@[expose] public section

namespace Erdos708Slots

/-- The two exceptional originals have disjoint ranges of window lengths. -/
def MediumException (M a : ℕ) : Prop :=
  (a = 75 ∧ M ≤ 104) ∨ (a = 125 ∧ 125 ≤ M ∧ M ≤ 174)

/-- If all prime divisors are at most five, excluding 8, 9 and 25 bounds
the respective prime exponents by 2, 1 and 1. -/
private theorem dvd_sixty {a : ℕ} (hprime : ∀ p : ℕ, p.Prime → p ∣ a → p < 7)
    (h8 : ¬ 8 ∣ a) (h9 : ¬ 9 ∣ a) (h25 : ¬ 25 ∣ a) : a ∣ 60 := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd 60 a).mpr
  intro p k hp hd
  by_cases hk : k = 0
  · simp [hk]
  have hlt := hprime p hp ((dvd_pow_self p hk).trans hd)
  have hp2 := hp.two_le
  have cases : p = 2 ∨ p = 3 ∨ p = 5 := by interval_cases p <;> norm_num at *
  rcases cases with rfl | rfl | rfl
  · exact (pow_dvd_pow 2 (n:=2) (m:=k) (le_of_not_gt fun h => h8 ((pow_dvd_pow 2 h).trans hd))).trans
      (by decide : 2^2 ∣ 60)
  · exact (pow_dvd_pow 3 (n:=1) (m:=k) (le_of_not_gt fun h => h9 ((pow_dvd_pow 3 h).trans hd))).trans
      (by decide : 3^1 ∣ 60)
  · exact (pow_dvd_pow 5 (n:=1) (m:=k) (le_of_not_gt fun h => h25 ((pow_dvd_pow 5 h).trans hd))).trans
      (by decide : 5^1 ∣ 60)

/-- A hard original either carries a prime exceeding M/8 or is the unique
exception for its window length. -/
theorem classify {M a : ℕ} (hM : 70 ≤ M) (ha : 2 ≤ a) (haM : a ≤ M) :
    (∃ u v : ℕ, 0<u ∧ 0<v ∧ a=u*v ∧ 7*u≤M ∧ 8*v≤M) ∨
    (∃ p : ℕ, p.Prime ∧ p∣a ∧ M<8*p) ∨ MediumException M a := by
  let Split := ∃ u v : ℕ, 0<u ∧ 0<v ∧ a=u*v ∧ 7*u≤M ∧ 8*v≤M
  by_cases h : Split
  · exact Or.inl h
  right
  by_cases hb : ∃ p : ℕ, p.Prime ∧ p∣a ∧ M<8*p
  · exact Or.inl hb
  right
  have noFactor (d : ℕ) (hd : 8 ≤ d) (hfit : 7*d ≤ M) (hdvd : d ∣ a) : False := by
    obtain ⟨c,hc⟩ := hdvd
    have hcpos : 0 < c := by by_contra! hh; simp [show c=0 by omega] at hc; omega
    exact h ⟨d,c,by omega,hcpos,hc,hfit,(Nat.mul_le_mul_right c hd).trans (hc ▸ haM)⟩
  have noSeven (hdvd : 7 ∣ a) : False := by
    obtain ⟨c,hc⟩ := hdvd
    exact h ⟨c,7,by omega,by decide,by omega,by omega,by omega⟩
  have hprime (p : ℕ) (hp : p.Prime) (hpa : p ∣ a) : p < 7 := by
    by_contra! h7
    rcases eq_or_lt_of_le h7 with rfl | h8
    · exact noSeven hpa
    by_cases big : M < 8*p
    · exact hb ⟨p,hp,hpa,big⟩
    · exact noFactor p h8 (by omega) hpa
  by_cases h25 : 25 ∣ a
  · have hsmall : M < 175 := lt_of_not_ge (fun h175 => noFactor 25 (by decide) h175 h25)
    obtain ⟨c,hc⟩ := h25
    have c1 : 1 ≤ c := by omega
    have c6 : c ≤ 6 := by omega
    interval_cases c
    · exact False.elim (h ⟨5,5,by decide,by decide,by omega,by omega,by omega⟩)
    · exact False.elim (noFactor 10 (by decide) (by omega) (by omega))
    · left
      refine ⟨by omega, ?_⟩
      by_contra! h105
      exact noFactor 15 (by decide) (by omega) (by omega)
    · exact False.elim (noFactor 10 (by decide) (by omega) (by omega))
    · exact Or.inr ⟨by omega,by omega,by omega⟩
    · exact False.elim (noFactor 10 (by decide) (by omega) (by omega))
  · have hd := dvd_sixty hprime (noFactor 8 (by decide) (by omega))
      (noFactor 9 (by decide) (by omega)) h25
    obtain ⟨u,v,hu,hv,hfac⟩ := exists_dvd_and_dvd_of_dvd_mul (show a ∣ 10*6 from hd)
    have hu10 := Nat.le_of_dvd (by decide : 0<10) hu
    have hv6 := Nat.le_of_dvd (by decide : 0<6) hv
    exact False.elim (h ⟨u,v,Nat.pos_of_dvd_of_pos hu (by decide),Nat.pos_of_dvd_of_pos hv (by decide),
      hfac,by omega,by omega⟩)

end Erdos708Slots
