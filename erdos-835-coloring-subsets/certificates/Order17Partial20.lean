module

public meta import Lean
import all Init.Data.List.Sort.Basic

@[expose] public section

/-! A compatible set of all three links at the fixed points 17, 18 and 19.
The blocks containing 19 recover the previously checked 19-point certificate.
The only remaining candidates are quadruples entirely on the moving points. -/

namespace Erdos835.Order17Partial20

set_option maxRecDepth 50000
set_option maxHeartbeats 50000000
set_option cbv.maxSteps 8000000

private meta def readBlocks (source : String) : Lean.Elab.Term.TermElabM Lean.Expr := do
  match (Lean.Json.parse source).bind (Lean.fromJson? (α := List (List Nat))) with
  | .ok blocks => return Lean.toExpr blocks
  | .error e => throwError "invalid seed: {e}"

elab "partial20Seed%" : term => readBlocks (include_str "order17-partial20.json")
elab "previous19Seed%" : term => readBlocks (include_str "order17-19.json")

def seed : List (List Nat) := partial20Seed%

/-- Every block and face below is a list of distinct labels in increasing order.
Use its incidence mask for comparisons of set families. -/
def mask (b : List Nat) : Nat := b.foldl (fun m x => m ||| (1 <<< x)) 0

def faces : List Nat → List (List Nat)
  | [a,b,c,d] => [[a,b,c], [a,b,d], [a,c,d], [b,c,d]]
  | _ => []

def subsets : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | n + 1, x :: xs => (subsets n xs).map (x :: ·) ++ subsets (n + 1) xs

def touchesFixed (b : List Nat) : Bool := b.any (17 ≤ ·)

def rotate (s : Nat) (x : Nat) : Nat := if x < 17 then (x + s) % 17 else x

theorem seed_shape : seed.length = 145 ∧ seed.all (fun b =>
    b.length = 4 && b.all (· < 20) && b == b.mergeSort.eraseDups && touchesFixed b) = true := by
  cbv

/-- All 460 triples containing a fixed point occur once as seed faces. -/
theorem covers_fixed_triples :
    (((seed.flatMap faces).filter touchesFixed).map mask).mergeSort =
    (((subsets 3 (List.range 20)).filter touchesFixed).map mask).mergeSort := by cbv

/-- The 120 moving triples already used by the seed occur without repetition. -/
theorem moving_faces_distinct :
    let moving := ((seed.flatMap faces).filter (fun b => !(touchesFixed b))).map mask
    moving.length = 120 ∧ moving.eraseDups.length = 120 := by cbv

/-- The 17 translates partition all 2,465 quadruples that meet the fixed points. -/
theorem covers_fixed_orbits :
    ((List.range 17).flatMap (fun s => seed.map fun b => mask (b.map (rotate s)))).mergeSort =
    (((subsets 4 (List.range 20)).filter touchesFixed).map mask).mergeSort := by cbv

/-- The link at 19 is exactly the original triple seed. -/
theorem extends_19 :
    ((seed.filter (fun b => b.contains 19)).map fun b => b.filter (· < 19)) =
    previous19Seed% := by cbv

end Erdos835.Order17Partial20
