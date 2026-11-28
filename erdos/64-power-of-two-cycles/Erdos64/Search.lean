import Erdos64.Obstructions
import Erdos64.Masks

namespace Erdos64

structure Anchor where
  vertex : Nat
  p : Nat
  q : Nat
  score : Nat
deriving Inhabited

/-- The score chooses which vertex to extend. The proof checks separately that
the selected vertex has at most two neighbors among the labels already present. -/
def pickAnchor (k : Nat) (nbrs : Array Nat) (allowed : Nat → Nat) : Option Anchor := Id.run do
  let mut best : Option Anchor := none
  for v in [:nbrs.size] do
    let neighbors := nbrs.getD v 0
    let rem := neighbors &&& (neighbors-1)
    if rem &&& (rem-1) != 0 then continue
    let available := allowed v
    let degree := countBitsUpTo 2 neighbors
    let paths := countBitsUpTo k (available &&& (2^k-1))
    let count := countBitsUpTo nbrs.size available
    let score := 64 * (if v < k then count + 10 else paths) + count + degree
    let a : Anchor := ⟨v, lowestBitIndex neighbors, lowestBitIndex rem, score⟩
    if v ≥ k && paths == 0 then return some a
    if best.all (fun old => score < old.score) then best := some a
  return best

/-- Returning true certifies that no extension of the board can occur in a
minimum-degree-three host with the distinguished dominating path and no C4, C8,
or C16. Exhausting the fuel always returns false. -/
def closes (k : Nat) : Nat → Array Nat → Bool
  | 0, _ => false
  | fuel + 1, rows =>
    let nbrs := neighborMasks rows
    let allowed := allowedAt (allowedRows rows nbrs)
    match pickAnchor k nbrs allowed with
    | none => false
    | some a =>
      decide (a.vertex < rows.size ∧ ∀ i : Fin rows.size,
        adjAt rows a.vertex i.val = true → i.val = a.p ∨ i.val = a.q) &&
      allMasks rows.size a.vertex allowed (fun m =>
        m &&& (2^k-1) == 0 || closes k fuel (rows.push m))

private theorem meetsMask {k m : Nat} (hit : ∃ i : Fin k, m.testBit i.val = true) :
    (m &&& (2^k-1)) ≠ 0 := by
  obtain ⟨i, hi⟩ := hit
  intro empty
  have h : (2^k-1 : Nat).testBit i.val = true := by
    exact (Nat.testBit_two_pow_sub_one k i.val).trans (decide_eq_true i.isLt)
  have eq := congrArg (fun a : Nat => a.testBit i.val) empty
  rw [Nat.testBit_and, h, hi] at eq
  simp at eq

theorem closes_sound {V : Type u} {G : Graph V} (d : MinDegreeThree G)
    (noCycles : ¬ (HasCycle G 4 ∨ HasCycle G 8 ∨ HasCycle G 16))
    (k fuel : Nat) (rows : Array Nat) (len : k ≤ rows.size)
    (c : Copy G rows.size (adjAt rows)) (dom : DominatesFirst k c)
    (complete : closes k fuel rows = true) : False := by
  induction fuel generalizing rows with
  | zero => simp [closes] at complete
  | succ fuel ih =>
    rw [closes] at complete
    split at complete
    · contradiction
    next a _ =>
      obtain ⟨ha, covered⟩ := Bool.and_eq_true_iff.mp complete
      obtain ⟨av, cover⟩ := of_decide_eq_true ha
      obtain ⟨m, bound, bit, cx, fixes⟩ := extendCopyFixing c d av cover
      have domx : DominatesFirst k cx := dom.transfer (fun i hi => fixes i (by omega))
      have met := meetsMask (maskMeetsDominatingSeed cx len domx)
      have checked := allMasks_sound covered av bound bit (fun i j hi hj ne bi bj =>
        allowedRows_sound hi hj ne bi bj noCycles cx)
      have closedChild : closes k fuel (rows.push m) = true := by
        simpa only [beq_eq_false_iff_ne.mpr met, Bool.false_or] using checked
      obtain ⟨child, labels⟩ := pushCopyFixing cx
      exact ih _ (by simp; omega) child (domx.transfer fun i _ => labels i) closedChild

end Erdos64
