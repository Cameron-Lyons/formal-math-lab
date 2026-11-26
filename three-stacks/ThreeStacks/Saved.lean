import ThreeStacks.Replay
import ThreeStacks.Data.Witnesses

namespace ThreeStacks

/-- Fixed-width expansion with the least significant digit first. -/
private def digits (base offset : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, code => (code % base + offset) :: digits base offset n (code / base)

/-- Original deck and 76 moves for each individually archived length-19 case. -/
def residual19 : List (List Nat × List Nat) :=
  residualCodes.map fun (p, w) => (digits 32 0 19 p, digits 4 1 76 w)

private def checks19 (entry : List Nat × List Nat) : Bool :=
  checkRun entry.2 entry.1 [] [] [] (target 19)

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem residual19_count : residual19.length = 384 := by decide +kernel

theorem residual19_distinct : (residual19.map Prod.fst).Nodup := by decide +kernel

theorem residual19_checked : residual19.all checks19 = true := by decide +kernel

theorem residual19_sorts {p ms} (h : (p, ms) ∈ residual19) : Sortable 19 p :=
  (run_iff_sortsTo _ _).mp (checkRun_sound (List.all_eq_true.mp residual19_checked _ h))

/-- Delete the card with label k and renumber the larger surviving cards. -/
def deletePublished (k : Nat) : List Nat :=
  (published.erase k).map fun a => if a < k then a else a-1

private def checksDeletion (k : Nat) : Bool :=
  match deletionCodes.lookup k with
  | none => false
  | some w => checkRun (digits 4 1 80 w) (deletePublished k) [] [] [] (target 20)

private theorem allDeletions : (target 21).all checksDeletion = true := by decide +kernel

theorem published_deletion_sorts (k : Nat) (hk : k ∈ target 21) :
    Sortable 20 (deletePublished k) := by
  have ok := List.all_eq_true.mp allDeletions _ hk
  unfold checksDeletion at ok
  split at ok
  · contradiction
  · exact (run_iff_sortsTo _ _).mp (checkRun_sound ok)

end ThreeStacks
