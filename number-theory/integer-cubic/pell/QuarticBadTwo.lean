module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

public section

namespace SmallCubic.QuarticBadTwo

private structure Branch where
  x : List ℤ
  y : List ℤ
  z : List ℤ
  rows : List ℕ
  deriving Inhabited

private def branches : Array Branch := #[
  ⟨[0, 0, 0, 0, 1], [1, 0, 0, 0, 0, 0, 1], [1], [6, 18]⟩,
  ⟨[0, 0, 0, 0, 1, 0, 1, 0, 1], [1, 1, 0, 1, 0, 1], [1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1], [1, 3, 5, 15, 19]⟩,
  ⟨[0, 0, 1], [1, 0, 0, 1], [1], [24]⟩,
  ⟨[0, 0, 1, 0, 0, 0, 1, 0, 1], [1, 0, 0, 1, 1, 1], [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1], [2, 4, 8, 14, 16, 18, 22]⟩,
  ⟨[0, 0, 1, 0, 1, 0, 0, 0, 1], [1, 0, 1, 1, 1], [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [2, 8, 12, 14, 16, 22]⟩,
  ⟨[0, 0, 1, 0, 1, 0, 1], [1, 0, 1, 1, 0, 1], [1, 0, 0, 0, 1, 0, 0, 0, 1], [24]⟩,
  ⟨[0, 0, 1, 0, 1, 0, 1], [1, 1, 0, 0, 0, 1, 1], [1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1], [1, 3, 5, 9, 17, 21, 23]⟩
]

private def plus : List ℤ → List ℤ → List ℤ
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: plus xs ys

private def mult : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | x :: xs, ys => plus (ys.map (x * ·)) (0 :: mult xs ys)

private def coeff (f : List ℤ) (n : ℕ) := f[n]?.getD 0
private def scale (a : ℤ) (f : List ℤ) := f.map (a * ·)

private def l2 := mult [1,0,-3] [1,0,-3]
private def l4 := mult l2 l2
private def target := scale 2 (mult l4 (mult l4 l4))

private def branch (k : Fin 7) := branches[k.val]!

/-- The coefficient of t^(i+1) in the indicated first-correction column,
in blocks of 8, 6 and 12 columns for X, Y and Z. -/
def jacobian (k : Fin 7) (i : Fin 24) (j : Fin 26) : ZMod 2 :=
  let b := branch k
  let (f, offset) := if j.val < 8 then (scale 3 (mult b.x b.x), j.val)
    else if j.val < 14 then (scale 2 (mult b.y b.z), j.val - 8)
    else (plus (mult b.y b.y) (scale 2 b.z), j.val - 14)
  if i.val < offset then 0 else (coeff f (i.val - offset) : ℤ)

/-- Negative residual coefficient divided by 2 for the selected integral lifts. -/
def correctionRhs (k : Fin 7) (i : Fin 24) : ZMod 2 :=
  let b := branch k
  let f := plus (mult b.x (mult b.x b.x)) (plus (mult b.z (mult b.y b.y))
    (plus (mult b.z b.z) (scale (-1) target)))
  ((-(coeff f (i.val + 1)) / 2 : ℤ) : ZMod 2)

private def witness (k : Fin 7) (i : Fin 24) : ZMod 2 :=
  if i.val + 1 ∈ (branch k).rows then 1 else 0

set_option maxHeartbeats 0 in
private theorem checks : ∀ k : Fin 7,
    (∀ j : Fin 26, ∑ i : Fin 24, witness k i * jacobian k i j = 0) ∧
    ∑ i : Fin 24, witness k i * correctionRhs k i ≠ 0 := by
  decide +kernel

/-- None of the seven full-pole chart residues admits a first correction.
The accompanying factor and square enumeration supplies the seven base residues. -/
theorem no_mod_four_correction (k : Fin 7) (v : Fin 26 → ZMod 2) :
    ¬ (∀ i : Fin 24, ∑ j : Fin 26, jacobian k i j * v j = correctionRhs k i) := by
  intro hv
  obtain ⟨hcols, hbad⟩ := checks k
  apply hbad
  calc
    ∑ i : Fin 24, witness k i * correctionRhs k i =
        ∑ i : Fin 24, ∑ j : Fin 26, (witness k i * jacobian k i j) * v j := by
          simp only [← hv, Finset.mul_sum, mul_assoc]
    _ = ∑ j : Fin 26, (∑ i : Fin 24, witness k i * jacobian k i j) * v j := by
          rw [Finset.sum_comm]
          simp only [Finset.sum_mul]
    _ = 0 := by simp [hcols]

end SmallCubic.QuarticBadTwo
