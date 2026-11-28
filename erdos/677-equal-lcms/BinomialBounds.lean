module

public import PrimePowers
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Erdos677

open Finset

/-- The falling product of a length-`k` interval divided by `(k-1)!` divides
its LCM. The induction subtracts multiples contributed by two overlapping
length-`k` subintervals. -/
theorem choose_mul_dvd_interval (n k : ℕ) (hk : 0 < k) :
    k * (n+k).choose k ∣ lcmInterval n k := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    by_cases hz : k = 0
    · subst k
      simp [lcmInterval]
    have hk' : 0 < k := by omega
    let L := lcmInterval n (k+1)
    let T := (k+1) * (n+k+1).choose (k+1)
    have left : k * (n+k).choose k ∣ L := by
      apply (ih n hk').trans
      apply Finset.lcm_mono
      intro x hx
      exact mem_Ioc.mpr ⟨(mem_Ioc.mp hx).1, by have := (mem_Ioc.mp hx).2; omega⟩
    have right : k * (n+k+1).choose k ∣ L := by
      have h := ih (n+1) hk'
      rw [show n+1+k = n+k+1 by omega] at h
      apply h.trans
      apply Finset.lcm_mono
      intro x hx
      have := mem_Ioc.mp hx
      exact mem_Ioc.mpr ⟨by omega, by omega⟩
    have hA : (n+k+1) * (k * (n+k).choose k) = k*T := by
      have h := Nat.add_one_mul_choose_eq (n+k) k
      unfold T
      calc
        _ = k * ((n+k+1) * (n+k).choose k) := by ring
        _ = _ := by rw [h]; ring
    have hB : (n+1) * (k * (n+k+1).choose k) = k*T := by
      have h := Nat.choose_succ_right_eq (n+k+1) k
      rw [show n+k+1-k = n+1 by omega] at h
      unfold T
      calc
        _ = k * ((n+k+1).choose k * (n+1)) := by ring
        _ = _ := by rw [← h]; ring
    have ha := Nat.mul_dvd_mul_left (n+k+1) left
    have hb := Nat.mul_dvd_mul_left (n+1) right
    rw [hA] at ha
    rw [hB] at hb
    have diff := Nat.dvd_sub ha hb
    rw [← Nat.sub_mul, show n+k+1-(n+1) = k by omega] at diff
    exact Nat.dvd_of_mul_dvd_mul_left hk' diff

private theorem entry_dvd_scaled_choose (x k t j : ℕ) (hx : 0 < x)
    (ht : t < j) (hj : j ≤ k) :
    x ∣ lcmInterval 0 k * (x+t).choose j := by
  induction t generalizing j with
  | zero =>
    cases j with
    | zero => omega
    | succ j =>
      cases x with
      | zero => omega
      | succ a =>
        have hjl : j+1 ∣ lcmInterval 0 k := by
          exact Finset.dvd_lcm (f := id) (mem_Ioc.mpr ⟨by omega, by omega⟩)
        have ha : a+1 ∣ (j+1) * (a+1).choose (j+1) := by
          rw [Nat.mul_comm, ← Nat.add_one_mul_choose_eq]
          exact dvd_mul_right _ _
        exact ha.trans (Nat.mul_dvd_mul_right hjl _)
  | succ t ih =>
    cases j with
    | zero => omega
    | succ j =>
      rw [show x+(t+1)=(x+t)+1 by omega, Nat.choose_succ_succ, Nat.mul_add]
      exact dvd_add (ih _ (by omega) (by omega)) (ih _ (by omega) hj)

/-- The LCM of a consecutive interval divides the indicated binomial
coefficient times the LCM of `1,…,k`. -/
theorem interval_dvd_lcm_mul_choose (n k : ℕ) :
    lcmInterval n k ∣ lcmInterval 0 k * (n+k).choose k := by
  apply Finset.lcm_dvd
  intro x hx
  obtain ⟨hl, hu⟩ := mem_Ioc.mp hx
  have h := entry_dvd_scaled_choose x k (n+k-x) k (by omega) (by omega) le_rfl
  rwa [show x+(n+k-x) = n+k by omega] at h

end Erdos677
