import Lean
import SevenCycle.Resolution

/-! Color one edge at a time. Once a good seven-cycle appears, its seven edges
prove that every extension of the current coloring works. Otherwise try all
three colors on the next edge. The tactic builds a proof using `leaf` and `split`. -/

namespace SevenCycle.Cert.Search
open Lean Elab Tactic

private def edgeId (a b : Nat) := 10 * min a b + max a b

/-- Edges with smaller maximum endpoint come first, so the first ten edges
are exactly the already colored edges among the five vertices of the star. -/
private def edgeOrder := (List.range 10).flatMap fun b => (List.range b).map (edgeId · b)

private structure Cycle where
  vertices : List Nat
  edges : List Nat

private def paths : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | n+1, allowed => allowed.flatMap fun v => (paths n (allowed.erase v)).map (v :: ·)

/-- A cycle first becomes testable when its last edge is colored. Enumerate it
once by taking its smallest vertex first and choosing one of the two directions. -/
private def cyclesByLastEdge : Array (List Cycle) := Id.run do
  let mut buckets := Array.replicate 100 []
  let rank (e : Nat) := 10 * (e % 10) + e / 10
  for start in [0:4] do
    for path in paths 6 ((List.range 10).drop (start + 1)) do
      if path.head! < path.getLast! then
        let vs := start :: path
        let es := vs.zipWith edgeId (vs.rotateLeft 1)
        let last := es.foldl (fun a b => if rank a < rank b then b else a) es.head!
        buckets := buckets.modify last (⟨vs, es⟩ :: ·)
  return buckets

private def good (colors : Array Nat) (cycle : Cycle) : Bool := Id.run do
  let mut previous := colors[cycle.edges.getLast!]!
  let mut changes := 0
  for e in cycle.edges do
    let current := colors[e]!
    if current != previous then
      changes := changes + 1
      if changes > 2 then return false
    previous := current
  return true

private structure Node where
  mask : Nat
  proof : Expr

private abbrev SearchM := StateT (Std.HashMap Nat Expr) (Except String)

/-- Reuse the proof if a different branch reaches the same requirements. -/
private def node (m : Nat) (proof : Unit → Expr) : SearchM Node := do
  if let some p := (← get)[m]? then return ⟨m, p⟩
  let p := proof ()
  modify (·.insert m p)
  return ⟨m, p⟩

private def reflTrue := mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Bool) (mkConst ``Bool.true)

private def witness (colors : Array Nat) (cycle : Cycle) : SearchM Node := do
  let m := cycle.edges.foldl (fun mask e => mask ||| bit e colors[e]!) 0
  node m fun _ =>
    let vs := cycle.vertices.map fun v => toExpr (Fin.ofNat 10 v)
    let cs := cycle.edges.map fun e => toExpr (Fin.ofNat 3 colors[e]!)
    mkAppN (mkConst ``Cert.leaf) ((vs ++ cs ++ [mkRawNatLit m, reflTrue]).toArray)

private def search (buckets : Array (List Cycle)) (colors : Array Nat) (root : Option Nat) :
    List Nat → SearchM Node
  | [] => throw "found a coloring with no good seven-cycle"
  | e :: rest => do
    let branch (k : Nat) := do
      let next := colors.set! e k
      if let some cycle := buckets[e]!.find? (good next) then witness next cycle
      else search buckets next none rest
    let bits := 7 <<< (3 * e)
    let red ← branch 0
    if root.isNone && red.mask &&& bits == 0 then return red
    let green ← branch 1
    if root.isNone && green.mask &&& bits == 0 then return green
    let blue ← branch 2
    if root.isNone && blue.mask &&& bits == 0 then return blue
    let used := red.mask ||| green.mask ||| blue.mask
    let m := root.getD (used ^^^ (used &&& bits))
    node m fun _ => mkAppN (mkConst ``Cert.split) #[mkRawNatLit e, mkRawNatLit m,
      mkRawNatLit red.mask, mkRawNatLit green.mask, mkRawNatLit blue.mask,
      red.proof, green.proof, blue.proof, reflTrue]

/-- Prove that a concrete star pattern forces a good cycle. The kernel checks
both the witness at each leaf and the three colors covered at each split. -/
elab "search_star" : tactic => do
  let_expr Cert.Valid mask := (← getMainTarget) | throwError "expected a star coloring"
  let_expr Cert.seedMask seed := mask | throwError "expected a seed mask"
  let some n ← Meta.getNatValue? seed | throwError "expected a concrete seed"
  let mut colors := Array.replicate 100 0
  let mut digits := n
  for e in [12,13,23,14,24,34] do
    colors := colors.set! e (digits % 3)
    digits := digits / 3
  match (search cyclesByLastEdge colors (some (Cert.seedMask n)) (edgeOrder.drop 10)).run {} with
  | .error msg => throwError msg
  | .ok (result, _) =>
    (← getMainGoal).assign result.proof
    replaceMainGoal []

end SevenCycle.Cert.Search
