import Std

/-! A board is specified by the surviving sticks on its first vertical line
and, for each column, its six horizontal sticks and its five right-hand
vertical sticks. A 1-bit always means that the stick survives. -/
namespace Matchsticks

abbrev HMask := Fin 64
abbrev VMask := Fin 32
abbrev RowPair := Fin 15

/-- The fifteen pairs of distinct levels, in lexicographic order. -/
def levels : Array (Nat × Nat) := #[
  (0,1), (0,2), (0,3), (0,4), (0,5), (1,2), (1,3), (1,4),
  (1,5), (2,3), (2,4), (2,5), (3,4), (3,5), (4,5)]

def top (p : RowPair) : Nat := levels[p.val]!.1
def bottom (p : RowPair) : Nat := levels[p.val]!.2

private def pairMask (keep : Nat → Nat → Bool) : Nat :=
  (List.finRange 15).foldl (fun s p =>
    if keep (top p) (bottom p) then s ||| (1 <<< p.val) else s) 0

private def horizontalTable : Array Nat := Array.ofFn fun h : HMask =>
  pairMask fun a b => h.val.testBit a && h.val.testBit b

private def verticalTable : Array Nat := Array.ofFn fun v : VMask =>
  pairMask fun a b => (List.range 5).all fun i =>
    decide (i < a ∨ b ≤ i) || v.val.testBit i

def hPairs (h : HMask) : Nat := horizontalTable[h.val]!
def vPairs (v : VMask) : Nat := verticalTable[v.val]!

/-- Count the erased horizontal sticks in one column. -/
def hCost (h : HMask) : Nat :=
  ((List.range 6).filter fun i => !h.val.testBit i).length

/-- Count the erased vertical sticks on one boundary. -/
def vCost (v : VMask) : Nat :=
  ((List.range 5).filter fun i => !v.val.testBit i).length

def advance (s : Nat) (h : HMask) (v : VMask) : Nat :=
  (s &&& hPairs h) ||| vPairs v

def legal (s : Nat) (h : HMask) (v : VMask) : Prop :=
  ((s &&& hPairs h) &&& vPairs v) = 0

instance (s : Nat) (h : HMask) (v : VMask) : Decidable (legal s h v) :=
  inferInstanceAs (Decidable (_ = 0))

inductive Board where
  | left (v : VMask)
  | snoc (b : Board) (h : HMask) (v : VMask)
  deriving Repr

def Board.width : Board → Nat
  | .left _ => 0
  | .snoc b _ _ => b.width + 1

def Board.cost : Board → Nat
  | .left v => vCost v
  | .snoc b h v => b.cost + (hCost h + vCost v)

def Board.state : Board → Nat
  | .left v => vPairs v
  | .snoc b h v => advance b.state h v

def Board.safe : Board → Prop
  | .left _ => True
  | .snoc b h v => b.safe ∧ legal b.state h v

def target (n : Nat) : Nat := if n = 1 then 5 else (10*n+4)/3

end Matchsticks

namespace Matchsticks
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

theorem pair_bounds (p : RowPair) : top p < bottom p ∧ bottom p < 6 := by
  exact (by decide : ∀ p : RowPair, top p < bottom p ∧ bottom p < 6) p

theorem all_pairs (a b : Nat) (hab : a < b) (hb : b < 6) :
    ∃ p : RowPair, top p = a ∧ bottom p = b := by
  have all : ∀ x y : Fin 6, x.val < y.val →
      ∃ p : RowPair, top p = x.val ∧ bottom p = y.val := by decide
  exact all ⟨a, by omega⟩ ⟨b, hb⟩ hab

theorem hPairs_bit (h : HMask) (p : RowPair) :
    (hPairs h).testBit p.val = (h.val.testBit (top p) && h.val.testBit (bottom p)) := by
  exact (by decide +kernel : ∀ h : HMask, ∀ p : RowPair,
    (hPairs h).testBit p.val = (h.val.testBit (top p) && h.val.testBit (bottom p))) h p

theorem vPairs_bit (v : VMask) (p : RowPair) :
    (vPairs v).testBit p.val = true ↔
      ∀ i : Nat, top p ≤ i → i < bottom p → v.val.testBit i = true := by
  have h : ∀ v : VMask, ∀ p : RowPair, (vPairs v).testBit p.val = true ↔
      ∀ i : Fin 5, top p ≤ i.val → i.val < bottom p → v.val.testBit i.val = true := by
    decide +kernel
  rw [h]
  constructor
  · intro hp i hlo hhi
    have := (pair_bounds p).2
    exact hp ⟨i, by omega⟩ hlo hhi
  · intro hp i
    exact hp i.val

theorem vPairs_bound (v : VMask) : vPairs v < 2^15 :=
  (by decide +kernel : ∀ v : VMask, vPairs v < 2^15) v

theorem hPairs_bound (h : HMask) : hPairs h < 2^15 :=
  (by decide +kernel : ∀ h : HMask, hPairs h < 2^15) h

theorem state_bound (b : Board) : b.state < 2^15 := by
  cases b with
  | left v => exact vPairs_bound v
  | snoc b h v =>
    exact Nat.or_lt_two_pow (Nat.lt_of_le_of_lt Nat.and_le_right (hPairs_bound h)) (vPairs_bound v)

theorem legal_iff (s : Nat) (h : HMask) (v : VMask) :
    legal s h v ↔ ∀ p : RowPair, ¬ (s.testBit p.val = true ∧
      (hPairs h).testBit p.val = true ∧ (vPairs v).testBit p.val = true) := by
  constructor
  · intro eqzero p ⟨hs, hh, hv⟩
    have eqbits := congrArg (fun n : Nat => n.testBit p.val) eqzero
    simp [Nat.testBit_and, hs, hh, hv] at eqbits
  · intro hlegal
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 15
    · have hp := hlegal ⟨i, hi⟩
      simp only [Nat.testBit_and, Nat.zero_testBit, Bool.and_eq_false_iff]
      cases hs : s.testBit i <;> cases hh : (hPairs h).testBit i <;> simp_all
    · have hlt : vPairs v < 2^i := Nat.lt_of_lt_of_le (vPairs_bound v)
          (Nat.pow_le_pow_right (by decide) (by omega))
      simp [Nat.testBit_and, Nat.testBit_lt_two_pow hlt]

end Matchsticks
