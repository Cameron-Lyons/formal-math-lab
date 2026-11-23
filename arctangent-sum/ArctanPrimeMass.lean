module

public import ArctanFactorial

public section

namespace Arxiv.«2607.05739»

local instance (p : ℕ) : Decidable p.Prime := Nat.decidablePrime' p

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Evaluate the full weight with the congruence test first, so only one
residue class needs the least-factor primality test. -/
theorem factorialWeight_certificate : 5700000 ≤ factorialWeight 1000000 := by
  let s := (Finset.range (32768+1)).filter (fun p => p % 4 = 3 ∧ p.Prime)
  have hs : inertPrimes = s := by
    ext p
    simp [inertPrimes, s, Nat.mem_primesLE, Nat.lt_succ_iff, and_assoc, and_comm, and_left_comm]
  rw [factorialWeight, hs]
  decide +kernel

end Arxiv.«2607.05739»
