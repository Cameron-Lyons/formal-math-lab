module

public import PrimePowers
public import Mathlib.Data.Nat.GCD.Basic

@[expose] public section

namespace Erdos677
open Finset

theorem lcmInterval_two_eq (n : ℕ) :
    lcmInterval n 2 = (n + 1) * (n + 2) := by
  rw [lcmInterval_extend n 1]
  simp [lcmInterval, Nat.Ioc_succ_singleton, Nat.Coprime.lcm_eq_mul]

theorem lcmInterval_two_strictMono : StrictMono (fun n : ℕ => lcmInterval n 2) := by
  intro n m h
  simp only [lcmInterval_two_eq]
  exact Nat.mul_lt_mul_of_lt_of_lt (by omega) (by omega)

theorem erdos_677_two (m n : ℕ) (hm : m ≥ n + 2) :
    lcmInterval m 2 ≠ lcmInterval n 2 :=
  (lcmInterval_two_strictMono (show n < m by omega)).ne'

end Erdos677
