import certificates.Order17Partial20
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic

namespace Erdos835.Order17Packings

open Order17Partial20

private def literal (src : String) : Lean.Elab.Term.TermElabM Lean.Expr := do
  let data ← Lean.ofExcept ((Lean.Json.parse src).bind (Lean.fromJson? (α := List (List Nat))))
  return Lean.toExpr data

elab "packingWithBoundary%" : term => literal (include_str "order17-packing257.json")
elab "packing263%" : term => literal (include_str "order17-packing263.json")

def withBoundary : List (List Nat) := packingWithBoundary%
def largestFound : List (List Nat) := packing263%

def faceMasks (D : List (List Nat)) := (D.flatMap faces).map mask
def translatedMasks (D : List (List Nat)) :=
  (List.range 17).flatMap fun i => D.map fun b => mask (b.map (rotate i))

def Shape (D : List (List Nat)) : Prop :=
  D.all (fun b => match b with
    | [a,b,c,d] => a < b && b < c && c < d && d < 20
    | _ => false) = true

/-- The combinatorial rank keeps our working bitset below 4,845 bits. -/
private def rank (m : Nat) : Nat :=
  ((List.range 20).foldl (fun (s : Nat × Nat) i =>
    if m.testBit i then (s.1 + 1, s.2 + i.choose (s.1 + 1)) else s) (0,0)).2

private def visit (seen : Nat) : List Nat → Bool
  | [] => true
  | x :: xs => !seen.testBit x && visit (seen ||| (1 <<< x)) xs

private theorem visit_sound (xs : List Nat) (s : Nat) (h : visit s xs = true) :
    xs.Nodup ∧ ∀ x ∈ xs, s.testBit x = false := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh, next⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨tail, absent⟩ := ih _ next
    have newbit : (1 <<< x).testBit x = true := by simp
    constructor
    · apply List.nodup_cons.mpr
      exact ⟨fun hx => by simpa [newbit] using absent x hx, tail⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · simpa using fresh
      · exact (Bool.or_eq_false_iff.mp (by simpa only [Nat.testBit_or] using absent y hy)).1

private theorem checked (xs : List Nat) (h : visit 0 (xs.map rank) = true) : xs.Nodup :=
  List.Nodup.of_map rank (visit_sound _ _ h).1

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- The 257-quadruple packing retains exactly the previously verified mixed blocks. -/
theorem retains_boundary : withBoundary.filter touchesFixed = Order17Partial20.seed := by decide +kernel

theorem packing257 :
    withBoundary.length = 257 ∧ Shape withBoundary ∧
    (faceMasks withBoundary).Nodup ∧ (translatedMasks withBoundary).Nodup := by
  refine ⟨by decide +kernel, by unfold Shape; decide +kernel, checked _ ?_, checked _ ?_⟩
  all_goals decide +kernel

/-- A second packing realizes 263 of the 285 required orbits. -/
theorem packing263 :
    largestFound.length = 263 ∧ Shape largestFound ∧
    (faceMasks largestFound).Nodup ∧ (translatedMasks largestFound).Nodup := by
  refine ⟨by decide +kernel, by unfold Shape; decide +kernel, checked _ ?_, checked _ ?_⟩
  all_goals decide +kernel

/-- The triple {0,1,15} is missing. Every possible fourth point gives a
quadruple that repeats a triple already used by the packing. -/
def blocksCompletion (D : List (List Nat)) : Bool :=
  let used := faceMasks D
  let t := [0, 1, 15]
  !used.contains (mask t) && (List.range 20).all (fun x =>
    t.contains x || (faces (x :: t)).any (fun f => used.contains (mask f)))

theorem missing_triple_cannot_be_filled :
    blocksCompletion withBoundary = true ∧ blocksCompletion largestFound = true := by
  decide +kernel

end Erdos835.Order17Packings
