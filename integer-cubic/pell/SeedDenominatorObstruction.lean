module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Second-digit obstruction for the exceptional rescaled denominator branch
through (−2,3,1). All lists of polynomial coefficients are in ascending order. -/
public section
namespace SmallCubic.SeedDenominator

private def add : List ℤ → List ℤ → List ℤ
  | [], b => b
  | a, [] => a
  | a :: as, b :: bs => (a+b) :: add as bs

private def mul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: as, b => add (b.map (a*·)) (0 :: mul as b)

private def coeff (a : List ℤ) (i : ℕ) : ℤ := a[i]?.getD 0
private def x : List ℤ := [-2,1,2,1,5]
private def y : List ℤ := [3,2,5,3]
private def z : List ℤ := [1,1,3,4,2,2,2]

/-- The Jacobian row for a nonconstant coefficient of X³+ZY²+Z²−2. -/
def jacobian (i j : Fin 18) : ZMod 7 :=
  let derivative := match j.val/6 with
    | 0 => (mul x x).map (3*·)
    | 1 => (mul y z).map (2*·)
    | _ => add (mul y y) (z.map (2*·))
  if i.val < j.val%6 then 0 else (coeff derivative (i.val-j.val%6) : ℤ)

def firstRhs (i : Fin 18) : ZMod 7 :=
  let error := add (mul x (mul x x)) (add (mul z (mul y y)) (mul z z))
  ((-(coeff error (i.val+1)) / 7 : ℤ) : ZMod 7)

private def row (k : Fin 3) (i : Fin 18) : ZMod 7 :=
  let values : List ℤ := match k.val with
    | 0 => [0,0,0,0,6,2,6,2,2,2,2,1,4,4,4]
    | 1 => [0,0,0,0,1,5,1,5,5,5,5,6,3,6,2]
    | _ => [0,0,0,0,0,0,0,0,0,0,0,0,0,0,3]
  (coeff values i : ℤ)

private def pivot (k : Fin 3) : Fin 18 := match k.val with
  | 0 => 5 | 1 => 10 | _ => 11

private def fixedDigit (k : Fin 3) : ZMod 7 := match k.val with
  | 0 => 6 | 1 => 1 | _ => 0

set_option maxHeartbeats 0 in
private theorem row_certificate : ∀ k : Fin 3,
    (∀ j : Fin 18, ∑ i, row k i * jacobian i j = if j = pivot k then 1 else 0) ∧
    ∑ i, row k i * firstRhs i = fixedDigit k := by decide +kernel

/-- Every first correction has the same digits at X₆,Y₅,Y₆. -/
theorem determined_digits (d : Fin 18 → ZMod 7)
    (h : ∀ i, ∑ j, jacobian i j * d j = firstRhs i) :
    d 5 = 6 ∧ d 10 = 1 ∧ d 11 = 0 := by
  have fixed (k : Fin 3) : d (pivot k) = fixedDigit k := by
    obtain ⟨hr, hb⟩ := row_certificate k
    calc d (pivot k) = ∑ j, (∑ i, row k i * jacobian i j) * d j := by simp [hr, ite_mul]
         _ = ∑ i, row k i * (∑ j, jacobian i j * d j) := by
           simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
           rw [Finset.sum_comm]
         _ = fixedDigit k := by simpa only [h] using hb
  exact ⟨fixed 0, fixed 1, fixed 2⟩

/-- The coefficient of t¹⁶ in X³+ZY², divided by 49, when the coefficient
corrections are seven times d. The full integer digits d can include all
higher digits. The remaining summands Z²Q³−2Q⁹ contribute a multiple of
343 at t¹⁶ for every Q=1+49c t². -/
def quotient16 (d : Fin 18 → ℤ) : ℤ :=
  3*(5+7*d 3)*(d 5)^2 + 21*(d 4)^2*d 5 +
  (2+7*d 15)*(d 11)^2 + 2*(2+7*d 16)*d 10*d 11 +
  (2+7*d 17)*(2*d 9*d 11 + (d 10)^2)

/-- Already the degree-16 equation contradicts the first correction equations.
This covers every possible value of the three free digits. -/
theorem no_second_correction (d : Fin 18 → ℤ) (k : ℤ)
    (h : ∀ i, ∑ j, jacobian i j * (d j : ZMod 7) = firstRhs i) :
    ¬ (343 : ℤ) ∣ 49*quotient16 d + 343*k := by
  obtain ⟨hx, hy, hz⟩ := determined_digits (fun j => (d j : ZMod 7)) h
  change (d 5 : ZMod 7) = 6 at hx
  change (d 10 : ZMod 7) = 1 at hy
  change (d 11 : ZMod 7) = 0 at hz
  have hc : ((quotient16 d : ℤ) : ZMod 7) = 3 := by
    dsimp [quotient16]
    push_cast
    rw [hx, hy, hz]
    simp only [show (7 : ZMod 7) = 0 by decide, show (21 : ZMod 7) = 0 by decide,
      zero_mul, mul_zero, add_zero, zero_add]
    decide
  rintro ⟨l, hl⟩
  have hd : (7 : ℤ) ∣ quotient16 d := ⟨l-k, by omega⟩
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr hd
  rw [hc] at this
  exact (by decide : (3 : ZMod 7) ≠ 0) this

/-- With Q=1+49c t², the complete coefficient of t¹⁶ is impossible for
every c. Thus t ↦ u t with u a unit preserves the obstruction: it multiplies
this coefficient by the unit u¹⁶ and replaces c by c u². -/
theorem no_degree16_equation (d : Fin 18 → ℤ) (c : ℤ)
    (h : ∀ i, ∑ j, jacobian i j * (d j : ZMod 7) = firstRhs i) :
    let z₄ := 2 + 7*d 15
    let z₅ := 2 + 7*d 16
    let z₆ := 2 + 7*d 17
    ¬ (343 : ℤ) ∣ 49*quotient16 d + 3*(49*c)^2*z₆^2 +
      (49*c)^3*(2*z₄*z₆ + z₅^2) - 18*(49*c)^8 := by
  dsimp only
  convert no_second_correction d
    (21*c^2*(2+7*d 17)^2 +
      343*c^3*(2*(2+7*d 15)*(2+7*d 17)+(2+7*d 16)^2) - 18*7^13*c^8) h using 2
  ring

end SmallCubic.SeedDenominator
