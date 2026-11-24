module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! The full-order residue through (0,1,−2) on the split conic at 13. -/
public section
namespace SmallCubic.CubicSeed13

private def add : List ℤ → List ℤ → List ℤ
  | [], b => b
  | a, [] => a
  | a :: as, b :: bs => (a+b) :: add as bs

private def mul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: as, b => add (b.map (a*·)) (0 :: mul as b)

private def coeff (a : List ℤ) (i : ℕ) := a[i]?.getD 0
private def x : List ℤ := [0,2,6,2,12,2,3]
private def y : List ℤ := [1,11,0,10,11,3,5]
private def z : List ℤ := [-2,7,6,3,5,6,6]
private def l3 := mul [1,0,-3] (mul [1,0,-3] [1,0,-3])

def jacobian (i j : Fin 18) : ZMod 13 :=
  let column := match j.val/6 with
    | 0 => (mul x x).map (3*·)
    | 1 => (mul y z).map (2*·)
    | _ => add (mul y y) ((mul z l3).map (2*·))
  if i.val < j.val%6 then 0 else (coeff column (i.val-j.val%6) : ℤ)

def correctionRhs (i : Fin 18) : ZMod 13 :=
  let error := add (mul x (mul x x)) (add (mul z (mul y y))
    (add (mul l3 (mul z z)) ((mul l3 (mul l3 l3)).map ((-2)*·))))
  ((- coeff error (i.val+1) / 13 : ℤ) : ZMod 13)

private def witness (i : Fin 18) : ZMod 13 :=
  (coeff [11,10,8,3,4,0,1,3,0,4,10,7,1,12,3,11,9,1] i.val : ℤ)

set_option maxHeartbeats 0 in
private theorem witness_ok :
    (∀ j : Fin 18, ∑ i : Fin 18, witness i * jacobian i j = 0) ∧
    ∑ i : Fin 18, witness i * correctionRhs i ≠ 0 := by
  decide +kernel

/-- The 18 first correction equations for this residue have no solution. -/
theorem no_first_correction (v : Fin 18 → ZMod 13) :
    ¬ (∀ i : Fin 18, ∑ j : Fin 18, jacobian i j * v j = correctionRhs i) := by
  intro hv
  obtain ⟨hz,hn⟩ := witness_ok
  apply hn
  calc
    ∑ i : Fin 18, witness i * correctionRhs i =
        ∑ i : Fin 18, ∑ j : Fin 18, (witness i * jacobian i j) * v j := by
          simp_rw [← hv, Finset.mul_sum, mul_assoc]
    _ = ∑ j : Fin 18, (∑ i : Fin 18, witness i * jacobian i j) * v j := by
          rw [Finset.sum_comm]; simp_rw [Finset.sum_mul]
    _ = 0 := by simp [hz]

end SmallCubic.CubicSeed13
