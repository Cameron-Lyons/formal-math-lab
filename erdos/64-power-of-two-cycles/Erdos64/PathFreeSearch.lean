import Erdos64.Search
import Erdos64.PathClauses

namespace Erdos64

def pathRows (r : Nat) : Array Nat :=
  Array.ofFn fun i : Fin r => if i.val = 0 then 0 else 1 <<< (i.val-1)

@[simp] theorem pathRows_size (r : Nat) : (pathRows r).size = r := by simp [pathRows]

theorem pathRows_adj {r i j : Nat} (hi : i < r) (hj : j < r) :
    adjAt (pathRows r) i j = pathAdj r i j := by
  simp only [adjAt, pathRows, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
    ↓reduceDIte, Option.getD_some, pathAdj, hi, hj, true_and]
  split
  next h =>
    have nz : j ≠ 0 := by omega
    simp [nz, Nat.one_shiftLeft, Nat.testBit_two_pow]
    grind
  next h =>
    split
    next h' =>
      have nz : i ≠ 0 := by omega
      simp [nz, Nat.one_shiftLeft, Nat.testBit_two_pow]
      grind
    next => simp; omega

theorem pathBoardCopy {V : Type u} {G : Graph V} {r : Nat} (path : HasInducedPath G r) :
    Nonempty (Copy G (pathRows r).size (adjAt (pathRows r))) := by
  rw [pathRows_size]
  obtain ⟨c⟩ := path
  exact c.congr (fun _ hi _ hj => (pathRows_adj hi hj).symm)

/-- Give priority to an endpoint for which a fresh neighbor has few ways to
avoid extending an existing induced path. The choice affects only running time. -/
def pathAnchor (r : Nat) (nbrs : Array Nat) (allowed : Nat → Nat) (h : PathHints) :
    Option Anchor := Id.run do
  let mut best : Option Anchor := none
  for v in [:nbrs.size] do
    let neighbors := nbrs.getD v 0
    let rem := neighbors &&& (neighbors-1)
    if rem &&& (rem-1) != 0 then continue
    let available := allowed v
    let supports := supportSize h v available
    let score := 80*supports + (if v < r then 100 else 0) +
      16 * countBitsUpTo nbrs.size available + nbrs.size - v
    let a : Anchor := ⟨v, lowestBitIndex neighbors, lowestBitIndex rem, score⟩
    if supports == 0 then return some a
    if best.all (fun old => score < old.score) then best := some a
  return best

/-- Choose a deficient vertex using any heuristic. Its degree bound and every
branch of its possible neighborhood are verified independently. -/
def closesPathWith (selectAnchor : Nat → Array Nat → (Nat → Nat) → PathHints → Option Anchor)
    (r : Nat) : Nat → Array Nat → Bool
  | 0, _ => false
  | fuel+1, rows =>
    let nbrs := neighborMasks rows
    let hints := pathHints nbrs r
    if longPath rows r hints then true else
    let allowed := allowedAt (allowedRows rows nbrs)
    match selectAnchor r nbrs allowed hints with
    | none => false
    | some a =>
      decide (a.vertex < rows.size ∧ ∀ i : Fin rows.size,
        adjAt rows a.vertex i.val = true → i.val = a.p ∨ i.val = a.q) &&
      allMasks rows.size a.vertex allowed
        (fun m => closesPathWith selectAnchor r fuel (rows.push m))

theorem closesPathWith_sound {selectAnchor} {V : Type u} {G : Graph V} {r : Nat} (d : MinDegreeThree G)
    (noCycles : ¬ (HasCycle G 4 ∨ HasCycle G 8 ∨ HasCycle G 16))
    (noLong : ¬ HasInducedPath G (r+1)) (fuel : Nat) (rows : Array Nat)
    (c : Copy G rows.size (adjAt rows)) (closed : closesPathWith selectAnchor r fuel rows = true) : False := by
  induction fuel generalizing rows with
  | zero => simp [closesPathWith] at closed
  | succ fuel ih =>
    rw [closesPathWith] at closed
    split at closed
    next h => exact noLong (longPath_sound h c)
    next =>
      dsimp only at closed
      split at closed
      · contradiction
      next a _ =>
        obtain ⟨ha, done_⟩ := Bool.and_eq_true_iff.mp closed
        obtain ⟨av, cover⟩ := of_decide_eq_true ha
        obtain ⟨m, bound, bit, ⟨cx⟩⟩ := extendCopy c d av cover
        have childClosed := allMasks_sound done_ av bound bit (fun i j hi hj ne bi bj =>
          allowedRows_sound hi hj ne bi bj noCycles cx)
        obtain ⟨child⟩ := pushCopy cx
        exact ih _ child childClosed

abbrev closesPath := closesPathWith pathAnchor

theorem closesPath_sound {V : Type u} {G : Graph V} {r : Nat} (d : MinDegreeThree G)
    (noCycles : ¬ (HasCycle G 4 ∨ HasCycle G 8 ∨ HasCycle G 16))
    (noLong : ¬ HasInducedPath G (r+1)) (fuel : Nat) (rows : Array Nat)
    (c : Copy G rows.size (adjAt rows)) (closed : closesPath r fuel rows = true) : False :=
  closesPathWith_sound d noCycles noLong fuel rows c closed

end Erdos64
