module

public import Mathlib.NumberTheory.Primorial
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

public section

namespace Arxiv.«2607.05739»

private theorem log_cost (k : ℕ) (hk : 9 ≤ k) : 4 * (9*k + 10) ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih => rw [pow_succ]; omega

/-- The contributions of all small-prime rounding errors in the two
factorial estimates have an elementary exponential upper bound. -/
theorem prime_power_overhead_le {n : ℕ} (hn : 2^27 ≤ n) :
    (∏ p ∈ (2*n).primesLE, p ^ (Nat.log p (n^2+1) + Nat.log p (2*n))) ≤ 2^(11*n) := by
  let k := Nat.log 2 n / 3
  have hn0 : n ≠ 0 := by omega
  have hk : 9 ≤ k := by
    have := Nat.le_log_of_pow_le (b := 2) (by decide) hn
    dsimp [k]; omega
  have hlow : 2 ^ (3*k) ≤ n :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) (show 3*k ≤ Nat.log 2 n by dsimp [k]; omega)).trans
      (Nat.pow_log_le_self 2 hn0)
  have hup : n < 2 ^ (3*k+3) :=
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).trans_le
      (Nat.pow_le_pow_right (by decide) (by dsimp [k]; omega))
  let t := 2 ^ (2*k+2)
  have h1 : n^2+1 < 2^(6*k+6) := by
    rw [show 6*k+6 = (3*k+3)*2 by omega, pow_mul]
    nlinarith [Nat.pow_le_pow_left (Nat.succ_le_of_lt hup) 2]
  have h2 : 2*n < 2^(3*k+4) := by
    rw [show 3*k+4 = (3*k+3)+1 by omega, pow_succ]
    omega
  have ht3 : t^3 = 2^(6*k+6) := by simp only [t, ← pow_mul]; congr 1; omega
  have ht2 : 2^(3*k+4) ≤ t^2 := by
    dsimp [t]; rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have htCost : (9*k+10)*t ≤ n := by
    calc
      (9*k+10)*t = (4*(9*k+10))*(2^k)^2 := by
        dsimp [t]; rw [pow_add, show 2*k = k*2 by omega, pow_mul]; ring
      _ ≤ 2^k * (2^k)^2 := Nat.mul_le_mul_right _ (log_cost k hk)
      _ = 2 ^ (3*k) := by rw [show 3*k = k*3 by omega, pow_mul]; ring
      _ ≤ n := hlow
  let overhead := fun p => p ^ (Nat.log p (n^2+1) + Nat.log p (2*n))
  let primes := (2*n).primesLE
  let small := primes.filter (· < t)
  let large := primes.filter (¬ · < t)
  have hscard : small.card ≤ t := by
    calc
      small.card ≤ (Finset.range t).card :=
        Finset.card_le_card (fun _ hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
      _ = t := Finset.card_range _
  have hsmall : (∏ p ∈ small, overhead p) ≤ 2^n := calc
    (∏ p ∈ small, overhead p) ≤ ∏ _p ∈ small, 2^(9*k+10) := by
      apply Finset.prod_le_prod
      intro p _
      dsimp [overhead]; rw [pow_add, show 9*k+10 = (6*k+6)+(3*k+4) by omega, pow_add]
      exact Nat.mul_le_mul ((Nat.pow_log_le_self p (by positivity)).trans h1.le)
        ((Nat.pow_log_le_self p (by positivity)).trans h2.le)
    _ = 2^((9*k+10)*small.card) := by simp [pow_mul]
    _ ≤ 2^n := Nat.pow_le_pow_right (by decide) ((Nat.mul_le_mul_left _ hscard).trans htCost)
  have hlarge : (∏ p ∈ large, overhead p) ≤ primorial (2*n)^2 * primorial n := calc
    (∏ p ∈ large, overhead p) ≤ ∏ p ∈ large, p^2 * (if p ≤ n then p else 1) := by
      apply Finset.prod_le_prod
      intro p hmem
      obtain ⟨hpp, hpt⟩ := Finset.mem_filter.mp hmem
      have hpos := (Nat.prime_of_mem_primesLE hpp).pos
      have hpt' : t ≤ p := by omega
      have hL : Nat.log p (n^2+1) < 3 :=
        Nat.log_lt_of_lt_pow (by positivity) (h1.trans_le (ht3 ▸ Nat.pow_le_pow_left hpt' 3))
      have hL' : Nat.log p (2*n) < 2 :=
        Nat.log_lt_of_lt_pow (by positivity) (h2.trans_le (ht2.trans (Nat.pow_le_pow_left hpt' 2)))
      by_cases hpn : p ≤ n
      · simp only [ite_eq_left hpn, ← pow_succ]
        exact Nat.pow_le_pow_right hpos (by omega)
      · simp only [ite_eq_right hpn, mul_one]
        have hLp : Nat.log p (n^2+1) < 2 :=
          Nat.log_lt_of_lt_pow (by positivity) (by nlinarith [Nat.pow_le_pow_left (by omega : n+1 ≤ p) 2])
        exact Nat.pow_le_pow_right hpos (by omega)
    _ = (∏ p ∈ large, p)^2 * ∏ p ∈ large with p ≤ n, p := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_filter (fun p => p ≤ n) (fun p => p)]
    _ ≤ primorial (2*n)^2 * primorial n := by
      simp only [primorial_eq_prod_primesLE]
      apply Nat.mul_le_mul
      · apply Nat.pow_le_pow_left
        exact Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _) (fun p hp _ =>
          (Nat.prime_of_mem_primesLE hp).one_le)
      · apply Finset.prod_le_prod_of_subset_of_one_le _ (fun p hp _ => (Nat.prime_of_mem_primesLE hp).one_le)
        intro p hp
        obtain ⟨hmem, hpn⟩ := Finset.mem_filter.mp hp
        exact Nat.mem_primesLE.mpr ⟨hpn, Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hmem).1⟩
  change (∏ p ∈ primes, overhead p) ≤ _
  rw [← Finset.prod_filter_mul_prod_filter_not primes (· < t)]
  calc
    _ ≤ 2^n * (primorial (2*n)^2 * primorial n) := Nat.mul_le_mul hsmall hlarge
    _ ≤ 2^n * ((4^(2*n))^2 * 4^n) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.pow_le_pow_left (primorial_le_four_pow _) 2) (primorial_le_four_pow _))
    _ = 2^(11*n) := by
      rw [show 4 = 2^2 by decide]
      simp only [← pow_mul, ← pow_add]; congr 1; omega

end Arxiv.«2607.05739»
