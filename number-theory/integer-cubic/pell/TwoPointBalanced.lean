module

public import Std.Tactic.BVDecide

public section

namespace SmallCubic.TwoPointBalanced

/-! In each normalized 2-adic coefficient lattice the two-mark identity
fails modulo eight. The variable H includes every possible positive integer
part of the slope. All variable coefficients of all three coordinates are free
modulo eight, subject only to having a unit at an index attaining the slope. -/

abbrev B := BitVec 3
private abbrev Poly := List B
private abbrev Pair := Poly × Poly

private def add : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a+b) :: add p q

-- Each product eᵢeⱼ has one binary carry determined by the fractional part r/e.
private def row (r e i : Nat) (a : B) : Nat → Poly → Poly
  | _, [] => []
  | j, b :: q =>
    (a*b * BitVec.ofNat 3 (2^(r*(i+j)/e - r*i/e - r*j/e))) :: row r e i a (j+1) q

private def mult (r e : Nat) : Nat → Poly → Poly → Poly
  | _, [], _ => []
  | i, a :: p, q => add (row r e i a 0 q) (0 :: mult r e (i+1) p q)

-- small=true means the integer part is zero. Otherwise h=k+r/e, k≥1, and 2H represents 2^k.
private def scaleRow (r e : Nat) (small : Bool) (H : B) (j : Nat) : Nat → Poly → Poly
  | _, [] => []
  | i, c :: p =>
    let n := r*(i+j)/e-r*i/e
    let factor := if small then BitVec.ofNat 3 (2^(n - (if j == 2 then 1 else 0)))
      else (if j == 1 then 2*H else 2*H*H) * BitVec.ofNat 3 (2^n)
    (c*factor) :: scaleRow r e small H j (i+1) p

private def shift (r e : Nat) (small : Bool) (H : B) (j : Nat) (p : Poly) : Poly :=
  List.replicate j 0 ++ scaleRow r e small H j 0 p

private def prod (r e : Nat) (small : Bool) (H : B) (f g : Pair) : Pair :=
  let m := mult r e 0 f.2 g.2
  let w := shift r e small H 1 m
  (add (mult r e 0 f.1 g.1) (add w (shift r e small H 2 m)),
   add (mult r e 0 f.1 g.2) (add (mult r e 0 f.2 g.1) (add m w)))

private def plus (f g : Pair) : Pair := (add f.1 g.1, add f.2 g.2)

private def coordinates (alternate : Bool) (c : Nat → B) : Pair × Pair × Pair :=
  (([0,c 0,c 1,c 2,c 3],[if alternate then -2 else 1,c 4,c 5,c 6]),
   ([1,c 7,c 8,c 9],[if alternate then 2 else -1,c 10,c 11]),
   ([1,c 12,c 13,c 14,c 15,c 16,c 17],[if alternate then 0 else -2,c 18,c 19,c 20,c 21,c 22]))

def identityHolds (alternate : Bool) (r e : Nat) (small : Bool) (H : B) (c : Nat → B) : Bool :=
  let (x,y,z) := coordinates alternate c
  let m := prod r e small H
  let (a,b) := plus (m x (m x x)) (m z (plus z (m y y)))
  (a.drop 1 ++ b).all (· == 0)

/-- At least one coefficient with index divisible by the slope denominator is odd. -/
def active (e : Nat) (c : Nat → B) : Bool :=
  let entries : List (Nat × B) := [(1,c 0), (2,c 1), (3,c 2), (4,c 3), (1,c 4), (2,c 5), (3,c 6), (1,c 7), (2,c 8), (3,c 9), (1,c 10), (2,c 11), (1,c 12), (2,c 13), (3,c 14), (4,c 15), (5,c 16), (6,c 17), (1,c 18), (2,c 19), (3,c 20), (4,c 21), (5,c 22)]
  entries.any fun (i,b) => (i % e == 0) && (b &&& 1 == 1)

/-- The reduced fractional slopes of positive denominator at most six. -/
inductive Chart where
  | integer
  | half
  | oneThird
  | twoThirds
  | aboveHalfAtTwoThirds
  | oneFourth
  | threeFourths
  | aboveHalfAtThreeFourths
  | oneFifth
  | twoFifths
  | threeFifths
  | aboveHalfAtThreeFifths
  | fourFifths
  | aboveHalfAtFourFifths
  | oneSixth
  | fiveSixths
  | aboveHalfAtFiveSixths

/-- Numerator, denominator and whether the integer part is zero. -/
def slopeCase : Chart → Nat × Nat × Bool
  | .integer => (0, 1, false)
  | .half => (1, 2, false)
  | .oneThird => (1, 3, false)
  | .twoThirds => (2, 3, false)
  | .aboveHalfAtTwoThirds => (2, 3, true)
  | .oneFourth => (1, 4, false)
  | .threeFourths => (3, 4, false)
  | .aboveHalfAtThreeFourths => (3, 4, true)
  | .oneFifth => (1, 5, false)
  | .twoFifths => (2, 5, false)
  | .threeFifths => (3, 5, false)
  | .aboveHalfAtThreeFifths => (3, 5, true)
  | .fourFifths => (4, 5, false)
  | .aboveHalfAtFourFifths => (4, 5, true)
  | .oneSixth => (1, 6, false)
  | .fiveSixths => (5, 6, false)
  | .aboveHalfAtFiveSixths => (5, 6, true)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- For either prescribed value, no one of the seventeen possible positive-slope
charts admits normalized coefficients with the required unit and cubic identity. -/
theorem no_balanced_lift (alternate : Bool) (k : Chart) (c : Nat → B) (H : B) :
    let (r,e,small) := slopeCase k
    ¬ (active e c && identityHolds alternate r e small H c) = true := by
  cases k <;> cases alternate <;>
    simp only [slopeCase, identityHolds, coordinates, prod, plus, shift, mult, row,
      scaleRow, add, active, List.any_cons, List.any_nil, List.replicate_succ,
      List.replicate_zero, List.cons_append, List.nil_append, List.drop, List.all_cons,
      List.all_nil, reduceIte, Bool.false_eq_true] <;> bv_decide

private def charts : List Chart := [
  .integer, .half, .oneThird, .twoThirds,
  .aboveHalfAtTwoThirds, .oneFourth, .threeFourths, .aboveHalfAtThreeFourths,
  .oneFifth, .twoFifths, .threeFifths, .aboveHalfAtThreeFifths,
  .fourFifths, .aboveHalfAtFourFifths, .oneSixth, .fiveSixths,
  .aboveHalfAtFiveSixths]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem charts_cover : ∀ r e : Fin 7, ∀ small : Bool,
    e.val ≠ 0 → r.val < e.val → Nat.Coprime r.val e.val →
    (small = true → e.val < 2*r.val) →
    charts.any (fun k => slopeCase k == (r.val, e.val, small)) = true := by
  decide +kernel

/-- The obstruction covers every reduced fraction that can occur at positive
index in degrees at most six and slope greater than one half. -/
theorem no_lift_for_fraction (alternate small : Bool) (r e : Fin 7) (he : e.val ≠ 0)
    (hr : r.val < e.val) (hcop : Nat.Coprime r.val e.val)
    (hsmall : small = true → e.val < 2*r.val) (c : Nat → B) (H : B) :
    ¬ (active e.val c && identityHolds alternate r.val e.val small H c) = true := by
  obtain ⟨k, _, hk⟩ := List.any_eq_true.mp (charts_cover r e small he hr hcop hsmall)
  have h := no_balanced_lift alternate k c H
  rw [eq_of_beq hk] at h
  exact h

end SmallCubic.TwoPointBalanced
