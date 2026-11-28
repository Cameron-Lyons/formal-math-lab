import Erdos64.PathFreeSearch

/-! An alternative branching order for the fourteen-to-fifteen vertex step.
Once no induced path on fifteen vertices was found, prefer a deficient
vertex that is an endpoint of a long induced path on the current board. -/
namespace Erdos64

private def maxOverBits (value : Nat → Nat) (cap : Nat) : Nat → Nat → Nat → Nat
  | 0, _, best => best
  | fuel+1, bits, best =>
    if bits == 0 || best == cap then best else
    let rest := bits &&& (bits-1)
    maxOverBits value cap fuel rest (max best (value (lowestBitIndex bits)))

/-- Maximum number of further edges of an induced path, capped at the fuel.
The available labels exclude the path so far and all neighbors of earlier
vertices other than the tip. This quantity only controls the search order. -/
private def extraLength (nbrs : Array Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel+1, tip, available =>
    let options := available &&& nbrs.getD tip 0
    let next := available ^^^ options
    maxOverBits (fun w => 1 + extraLength nbrs fuel w next) (fuel+1) nbrs.size options 0

def longestAnchor (r : Nat) (nbrs : Array Nat) (allowed : Nat → Nat)
    (h : PathHints) : Option Anchor := Id.run do
  let mut best : Option Anchor := none
  let labels := (1 <<< nbrs.size) - 1
  for v in [:nbrs.size] do
    let neighbors := nbrs.getD v 0
    let rem := neighbors &&& (neighbors-1)
    if rem &&& (rem-1) != 0 then continue
    let available := allowed v
    let support := supportSize h v available
    let length := if (h.byEnd.getD v []).isEmpty then
      1 + extraLength nbrs (r-1) v (labels ^^^ (1 <<< v))
      else r
    let score := 200*(r-length) + 40*(min 6 support) +
      4*(countBitsUpTo nbrs.size available) + nbrs.size - v
    let candidate : Anchor := ⟨v, lowestBitIndex neighbors, lowestBitIndex rem, score⟩
    if best.all (fun old => score < old.score) then best := some candidate
  return best

end Erdos64
