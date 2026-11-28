/-! A five-row matchstick board is specified by the surviving sticks on its left
boundary and, for each column, its six horizontal sticks and five right-hand
vertical sticks. A 1-bit means that the stick survives. -/
namespace Matchsticks

abbrev HMask := Fin 64
abbrev VMask := Fin 32
abbrev RowPair := Fin 15

/-- The fifteen pairs of distinct horizontal grid lines, in lexicographic order. -/
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

def target (n : Nat) : Nat := if n = 1 then 5 else (10 * n + 4) / 3

theorem pair_bounds (p : RowPair) : top p < bottom p ∧ bottom p < 6 :=
  (by decide : ∀ p : RowPair, top p < bottom p ∧ bottom p < 6) p

theorem all_pairs (a b : Nat) (hab : a < b) (hb : b < 6) :
    ∃ p : RowPair, top p = a ∧ bottom p = b := by
  have h : ∀ x y : Fin 6, x.val < y.val →
      ∃ p : RowPair, top p = x.val ∧ bottom p = y.val := by decide
  exact h ⟨a, by omega⟩ ⟨b, hb⟩ hab

theorem hPairs_bit (h : HMask) (p : RowPair) :
    (hPairs h).testBit p.val = (h.val.testBit (top p) && h.val.testBit (bottom p)) :=
  (by decide +kernel : ∀ h : HMask, ∀ p : RowPair,
    (hPairs h).testBit p.val = (h.val.testBit (top p) && h.val.testBit (bottom p))) h p

theorem vPairs_bit (v : VMask) (p : RowPair) :
    (vPairs v).testBit p.val = true ↔
      ∀ i : Nat, top p ≤ i → i < bottom p → v.val.testBit i = true := by
  have h : ∀ v : VMask, ∀ p : RowPair, (vPairs v).testBit p.val = true ↔
      ∀ i : Fin 5, top p ≤ i.val → i.val < bottom p → v.val.testBit i.val = true := by
    decide +kernel
  rw [h]
  exact ⟨fun hp i hlo hhi => hp ⟨i, by have := (pair_bounds p).2; omega⟩ hlo hhi,
         fun hp i => hp i.val⟩

theorem legal_elim {s : Nat} {h : HMask} {v : VMask} (hleg : legal s h v) (p : RowPair) :
    ¬ (s.testBit p.val = true ∧ (hPairs h).testBit p.val = true ∧ (vPairs v).testBit p.val = true) := by
  rintro ⟨hs, hh, hv⟩
  have hbit := congrArg (fun n : Nat => n.testBit p.val) hleg
  simp [Nat.testBit_and, hs, hh, hv] at hbit

end Matchsticks
