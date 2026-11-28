import Lean

/-! A 19-point certificate for the order-17 search in Erdős problem 835.
A block is a triple in increasing order. Points 0 through 16 rotate
and points 17 and 18 are fixed. -/

namespace Erdos835.Order17On19

set_option maxRecDepth 50000
set_option maxHeartbeats 20000000
set_option cbv.maxSteps 4000000

/-- Elaborate the data file to a literal list, so the kernel can check the
two identities below by reduction. -/
elab "order17Seed%" : term => do
  let result : Except String (List (List Nat)) :=
    (Lean.Json.parse (include_str "order17-19.json")).bind Lean.fromJson?
  match result with
  | .ok blocks => return Lean.toExpr blocks
  | .error e => throwError "invalid seed: {e}"

def seed : List (List Nat) := order17Seed%

def translate (s : Nat) (B : List Nat) : List Nat :=
  (B.map fun x => if x < 17 then (x + s) % 17 else x).mergeSort

def pairs : List (List Nat) :=
  (List.range 19).flatMap fun a =>
    ((List.range 19).filter fun b => a < b).map fun b => [a, b]

def triples : List (List Nat) :=
  (List.range 19).flatMap fun a =>
    ((List.range 19).filter fun b => a < b).flatMap fun b =>
      ((List.range 19).filter fun c => b < c).map fun c => [a, b, c]

def blockPairs : List Nat → List (List Nat)
  | [a, b, c] => [[a, b], [a, c], [b, c]]
  | _ => []

-- Each pair lies in exactly one of the 57 seed triples.
theorem seed_covers_pairs : (seed.flatMap blockPairs).mergeSort = pairs := by cbv

-- The 17 translated copies partition all triples on the 19 points.
theorem translates_cover_triples : ((List.range 17).flatMap fun s => seed.map (translate s)).mergeSort = triples := by
  cbv

end Erdos835.Order17On19
