module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

public section

namespace SmallCubic.TwoPointBadSeven

open scoped BigOperators

private abbrev R := ZMod 49
private abbrev Idx := Fin 24

private inductive Term where
  | lit (n : ℤ)
  | var (i : Idx)
  | add (a b : Term)
  | mul (a b : Term)
  deriving Inhabited

private def val (h : Idx → R) : Term → R
  | .lit n => n
  | .var i => h i
  | .add a b => val h a + val h b
  | .mul a b => val h a * val h b

private def grad (j : Idx) : Term → R
  | .lit _ => 0
  | .var i => if i = j then 1 else 0
  | .add a b => grad j a + grad j b
  | .mul a b => val 0 a * grad j b + val 0 b * grad j a

private theorem nil_product (r s A B : R) :
    (r+7*A)*(s+7*B) = r*s+7*(r*B+s*A) := by
  have hz : (7 : R)^2 = 0 := by decide
  linear_combination A*B*hz

private theorem first_order (e : Term) (h : Idx → R) :
    val (fun j => 7*h j) e = val 0 e + 7 * ∑ j, grad j e * h j := by
  induction e with
  | lit n => simp [val, grad]
  | var i => simp [val, grad, ite_mul]
  | add a b ha hb =>
    simp only [val, grad, ha, hb, add_mul, Finset.sum_add_distrib]
    ring
  | mul a b ha hb =>
    rw [val, ha, hb, nil_product]
    simp only [val, grad, add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]

-- Smart constructors reduce the size of the coefficient expression.
private def plus : Term → Term → Term
  | .lit 0, b => b
  | a, .lit 0 => a
  | a, b => .add a b

private def times : Term → Term → Term
  | .lit 0, _ | _, .lit 0 => .lit 0
  | .lit 1, b => b
  | a, .lit 1 => a
  | a, b => .mul a b

private abbrev Pol := List Term
private def sumPol : Pol → Pol → Pol
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => plus x y :: sumPol xs ys

private def prodPol : Pol → Pol → Pol
  | [], _ => []
  | x :: xs, ys => sumPol (ys.map (times x)) (.lit 0 :: prodPol xs ys)

private abbrev Pair := Pol × Pol
private def addPair (a b : Pair) : Pair := (sumPol a.1 b.1, sumPol a.2 b.2)

-- The product for w=u-1-v=2Hs, where v²=(1+2Hs)v + 2Hs + 2H²s².
private def multiply (a b : Pair) : Pair :=
  let h := Term.var 23
  let hh := times (.lit 2) h
  let q := prodPol a.2 b.2
  (sumPol (prodPol a.1 b.1) (prodPol [.lit 0, hh, times hh h] q),
   sumPol (sumPol (prodPol a.1 b.2) (prodPol a.2 b.1)) (prodPol [.lit 1, hh] q))

private def entry (coeffs : List ℤ) (start i : ℕ) : Term :=
  let base := Term.lit (coeffs[i]?.getD 0)
  if i = 0 then base else plus base (.var ⟨(start+i-1)%24, Nat.mod_lt _ (by decide)⟩)

private def coordinate (coeffs : List ℤ) (start degree : ℕ) : Pol :=
  (List.range (degree+1)).map (entry coeffs start)

private def coefficientPair (p q : List ℤ) (s t degree : ℕ) : Pair :=
  (coordinate p s degree, coordinate q t (degree-1))

-- Each marked coordinate fixes its two constant terms exactly.
private def residual (alternate : Bool) : Pair :=
  let x := coefficientPair [0,0,0,0,3] (if alternate then [-2,2,1,1] else [1,0,6]) 0 13 4
  let y := coefficientPair [1,0,0,3] (if alternate then [2,4,6] else [-1]) 4 16 3
  let z := coefficientPair [1,0,0,5,0,0,2] (if alternate then [0,2,5,6,4,1]
    else [-2,0,2,2,1]) 7 18 6
  addPair (multiply x (multiply x x)) (multiply z (addPair z (multiply y y)))

private def witness (alternate : Bool) : List ℤ :=
  if alternate then [0,0,0,5,4,5,0,0,0,0,1,2,0,0,0,2,4,5,1,0,0,0,1]
  else [0,6,2,0,3,0,0,0,0,0,0,3,0,6,0,0,0,3,0,1,0,0,0]

private def coefficients (alternate : Bool) : List Term :=
  let f := residual alternate
  ((List.range 12).map (fun i => f.1[i+1]?.getD (.lit 0))) ++
    ((List.range 11).map (fun i => f.2[i+1]?.getD (.lit 0)))

private def dot : List ℤ → List Term → Term
  | w :: ws, x :: xs => plus (times (.lit w) x) (dot ws xs)
  | _, _ => .lit 0

private def objective (b : Bool) := dot (witness b) (coefficients b)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem certificate (b : Bool) :
    val 0 (objective b) ≠ 0 ∧ ∀ j : Idx, 7 * grad j (objective b) = 0 := by
  cases b <;> decide +kernel

private theorem dot_zero (ws : List ℤ) (xs : List Term) (h : Idx → R)
    (hxs : ∀ x ∈ xs, val h x = 0) : val h (dot ws xs) = 0 := by
  induction ws generalizing xs with
  | nil => rfl
  | cons w ws ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      have hx := hxs x (List.mem_cons_self ..)
      have hrest := ih xs (fun e he => hxs e (List.mem_cons_of_mem _ he))
      have hp (a b : Term) : val h (plus a b) = val h a + val h b := by
        fun_cases plus a b <;> simp_all [val]
      have hm (a b : Term) : val h (times a b) = val h a * val h b := by
        fun_cases times a b <;> simp_all [val]
      simp only [dot, hp, hm, hx, hrest, mul_zero, add_zero]

/-- The reduced surface identity at either split branch, including the free H
correction in its quadratic algebra, is impossible modulo 49. The preceding
factor-and-square census identifies the two representatives. -/
def IsMod49Lift (alternate : Bool) (correction : Fin 24 → ZMod 49) : Prop :=
  ∀ e ∈ coefficients alternate, val (fun i => 7 * correction i) e = 0

theorem no_mod49_lift (alternate : Bool) (h : Fin 24 → ZMod 49) :
    ¬ IsMod49Lift alternate h := by
  intro hlift
  have he := dot_zero (witness alternate) (coefficients alternate) _ hlift
  change val _ (objective alternate) = 0 at he
  rw [first_order, Finset.mul_sum] at he
  have ⟨hn, hg⟩ := certificate alternate
  simp only [← mul_assoc, hg, zero_mul, Finset.sum_const_zero, add_zero] at he
  exact hn he

end SmallCubic.TwoPointBadSeven
