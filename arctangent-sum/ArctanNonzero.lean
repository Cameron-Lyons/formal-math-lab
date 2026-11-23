module

public import ArctanBridge
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace Arxiv.«2607.05739»

/-- Modulo three, any three consecutive factors have product `-1`. -/
private theorem coords_three_step (n : ℕ) :
    ((coords (n + 3)).1 : ZMod 3) = -((coords n).1 : ZMod 3) := by
  let step (k : ZMod 3) (a b : ZMod 3) := (a - k * b, b + k * a)
  have h : ∀ k a b : ZMod 3,
      let p := step (k + 1) a b
      let q := step (k + 2) p.1 p.2
      (step (k + 3) q.1 q.2).1 = -a := by decide
  simpa [coords, step, Nat.cast_succ, add_assoc] using
    h n (coords n).1 (coords n).2

/-- The real coordinate is a unit modulo three at every index. -/
theorem coords_fst_ne_zero_mod_three : ∀ n : ℕ, ((coords n).1 : ZMod 3) ≠ 0
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | n + 3 => by rw [coords_three_step, neg_ne_zero]; exact coords_fst_ne_zero_mod_three n

theorem A_ne_zero (n : ℕ) : A n ≠ 0 := by
  intro h
  simpa [coords_eq, h] using coords_fst_ne_zero_mod_three n

end Arxiv.«2607.05739»
