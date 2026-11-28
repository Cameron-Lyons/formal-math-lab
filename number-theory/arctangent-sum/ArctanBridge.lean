/-
The definitions gaussProd, A, B and IsIntegerValue are from Formal Conjectures.
Copyright 2026 The Formal Conjectures Authors. Licensed under Apache 2.0.
https://github.com/google-deepmind/formal-conjectures/blob/main/LICENSE
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
The four definitions below reproduce the Gaussian product and integer-value
predicate in Formal Conjectures, `Arxiv/2607.05739/TanArctanSum.lean`.
The coordinate recurrence lets us compute the predicate without rational division.
-/

@[expose] public section

namespace Arxiv.«2607.05739»

def gaussProd (n : ℕ) : GaussianInt :=
  ∏ k ∈ Finset.Icc 1 n, (⟨1, (k : ℤ)⟩ : GaussianInt)

def A (n : ℕ) : ℤ := (gaussProd n).re

def B (n : ℕ) : ℤ := (gaussProd n).im

def IsIntegerValue (n : ℕ) : Prop := A n ∣ B n

/-- Integer coordinates after successively multiplying by `1 + k i`. -/
def coords : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 =>
    let (a, b) := coords n
    let k : ℤ := (n + 1 : ℕ)
    (a - k * b, b + k * a)

theorem gaussProd_succ (n : ℕ) :
    gaussProd (n + 1) = gaussProd n * (⟨1, ((n + 1 : ℕ) : ℤ)⟩ : GaussianInt) :=
  Finset.prod_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n)) _

theorem coords_eq (n : ℕ) : coords n = (A n, B n) := by
  induction n with
  | zero => simp [coords, A, B, gaussProd]
  | succ n ih =>
    rw [coords, ih]
    simp [A, B, gaussProd_succ, Zsqrtd.re_mul, Zsqrtd.im_mul, sub_eq_add_neg,
      mul_comm, add_comm]
    ring

theorem isIntegerValue_iff_coords (n : ℕ) :
    IsIntegerValue n ↔ (coords n).1 ∣ (coords n).2 := by
  rw [coords_eq]
  rfl

end Arxiv.«2607.05739»
