module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! First Hensel corrections for the six full-pole cubic branches through
(−2,3,1) on u²−3v²=1. The coefficient lists are in ascending order. -/
public section
namespace SmallCubic.CubicLift

private structure Branch where
  x : List ℤ
  y : List ℤ
  z : List ℤ
  witness : List ℤ
  deriving Inhabited

-- Explicit branch data and left-kernel witnesses checked below.
private def data : Array Branch := #[
  ⟨[-2, 1, 3, 3, 4, 4, 5], [3, 4, 0, 6, 0, 1, 4], [1, 5, 4, 3, 4, 6, 4], [2, 0, 1, 2, 2, 0, 3, 1, 2, 1, 2, 2, 5, 4, 5, 6, 0, 1]⟩,
  ⟨[-2, 2, 2, 2, 0, 2, 3], [3, 5, 1, 6, 3, 3, 4], [1, 4, 3, 0, 3, 5, 1], [1, 0, 2, 3, 3, 2, 0, 4, 5, 5, 0, 4, 1, 0, 1, 4, 1, 0]⟩,
  ⟨[-2, 3, 0, 6, 4, 5, 6], [3, 5, 1, 6, 3, 3, 4], [1, 1, 6, 0, 5, 6, 1], [2, 3, 5, 1, 1, 0, 5, 0, 3, 6, 4, 2, 5, 2, 4, 5, 1, 0]⟩,
  ⟨[-2, 4, 0, 1, 4, 2, 6], [3, 2, 1, 1, 3, 4, 4], [1, 6, 6, 0, 5, 1, 1], [2, 4, 5, 6, 1, 0, 5, 0, 3, 1, 4, 5, 5, 5, 4, 2, 1, 0]⟩,
  ⟨[-2, 5, 2, 5, 0, 5, 3], [3, 2, 1, 1, 3, 4, 4], [1, 3, 3, 0, 3, 2, 1], [1, 0, 2, 4, 3, 5, 0, 3, 5, 2, 0, 3, 1, 0, 1, 3, 1, 0]⟩,
  ⟨[-2, 6, 3, 4, 4, 3, 5], [3, 3, 0, 1, 0, 6, 4], [1, 2, 4, 4, 4, 1, 4], [5, 0, 6, 2, 5, 0, 4, 1, 5, 1, 5, 2, 2, 4, 2, 6, 0, 1]⟩
]

private def branch (k : Fin 6) : Branch := data[k.val]!

private def plus : List ℤ → List ℤ → List ℤ
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x+y) :: plus xs ys

private def mult : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | x :: xs, ys => plus (ys.map (x*·)) (0 :: mult xs ys)

private def scale (n : ℤ) (xs : List ℤ) := xs.map (n*·)
private def coeff (xs : List ℤ) (i : ℕ) : ℤ := xs[i]?.getD 0

private def l3 := mult [1,0,-3] (mult [1,0,-3] [1,0,-3])
private def l9 := mult l3 (mult l3 l3)

/-- Coefficient of t^(i+1) in column j. The three blocks of six columns
are t^h times 3X², 2YZ and Y²+2ZL³, respectively, for h=1,…,6. -/
def jacobian (k : Fin 6) (i j : Fin 18) : ZMod 7 :=
  let b := branch k
  let derivative := match j.val/6 with
    | 0 => scale 3 (mult b.x b.x)
    | 1 => scale 2 (mult b.y b.z)
    | _ => plus (mult b.y b.y) (scale 2 (mult b.z l3))
  if i.val < j.val%6 then 0 else (coeff derivative (i.val-j.val%6) : ℤ)

/-- The negative coefficient of X³+ZY²+Z²L³−2L⁹ divided by seven.
The integer representatives have constant coefficients −2, 3 and 1. -/
def correctionRhs (k : Fin 6) (i : Fin 18) : ZMod 7 :=
  let b := branch k
  let residual := plus (mult b.x (mult b.x b.x))
    (plus (mult b.z (mult b.y b.y)) (plus (mult l3 (mult b.z b.z)) (scale (-2) l9)))
  ((-(coeff residual (i.val+1)) / 7 : ℤ) : ZMod 7)

private def witness (k : Fin 6) (i : Fin 18) : ZMod 7 :=
  (coeff (branch k).witness i.val : ℤ)

set_option maxHeartbeats 0 in
private theorem witness_ok : ∀ k : Fin 6,
    (∀ j : Fin 18, ∑ i : Fin 18, witness k i * jacobian k i j = 0) ∧
    ∑ i : Fin 18, witness k i * correctionRhs k i ≠ 0 := by
  decide +kernel

/-- For each enumerated branch, every choice of the eighteen correction
digits modulo seven fails at least one of the first-lift equations. -/
theorem no_first_correction (k : Fin 6) (v : Fin 18 → ZMod 7) :
    ¬ (∀ i : Fin 18, ∑ j : Fin 18, jacobian k i j * v j = correctionRhs k i) := by
  intro hv
  obtain ⟨hz, hn⟩ := witness_ok k
  apply hn
  calc
    ∑ i : Fin 18, witness k i * correctionRhs k i =
        ∑ i : Fin 18, ∑ j : Fin 18, (witness k i * jacobian k i j) * v j := by
          simp only [← hv, Finset.mul_sum, mul_assoc]
    _ = ∑ j : Fin 18, (∑ i : Fin 18, witness k i * jacobian k i j) * v j := by
          rw [Finset.sum_comm]
          simp only [Finset.sum_mul]
    _ = 0 := by simp [hz]

end SmallCubic.CubicLift
