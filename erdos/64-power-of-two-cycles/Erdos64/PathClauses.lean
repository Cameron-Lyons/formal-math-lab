import Erdos64.ExtensionSoundness
import Erdos64.Masks

/-! Find induced paths on the current board. Shorter path masks guide the
choice of vertex to expand. Only a checked full path can close a branch. -/
namespace Erdos64

structure PathHints where
  byEnd : Array (List Nat)
  long? : Option (List Nat)
  deriving Inhabited

private def visitBits {α : Type} (f : Nat → α → α) : Nat → Nat → α → α
  | 0, _, acc => acc
  | fuel+1, bits, acc =>
    if bits == 0 then acc else
    let rest := bits &&& (bits-1)
    visitBits f fuel rest (f (bits ^^^ rest).log2 acc)

private abbrev PathsAtRoot := List Nat × Option (List Nat)

private def gather (nbrs : Array Nat) : Nat → Nat → Nat → Nat → List Nat →
    PathsAtRoot → PathsAtRoot
  | 0,v,avail,other,prev,acc =>
    if acc.2.isSome then acc else
    let options := nbrs.getD v 0 &&& avail
    if options == 0 then (other :: acc.1, none)
    else let w := (options ^^^ (options &&& (options-1))).log2
         (acc.1,some (w :: v :: prev))
  | left+1,v,avail,other,prev,acc =>
    if acc.2.isSome then acc else
    let options := nbrs.getD v 0 &&& avail
    let next := avail ^^^ options
    visitBits (fun w cur => gather nbrs left w next (other ||| (1 <<< w)) (v :: prev) cur)
      nbrs.size options acc

def pathHints (nbrs : Array Nat) (r : Nat) : PathHints := Id.run do
  let mut table := #[]
  let all := (1 <<< nbrs.size)-1
  for a in [:nbrs.size] do
    let (masks,long) := gather nbrs (r-1) a (all ^^^ (1 <<< a)) 0 [] ([],none)
    if long.isSome then return ⟨table,long⟩
    table := table.push masks
  return ⟨table,none⟩

/-- Check that these labels induce precisely the path on r vertices. -/
private def pathValid (rows : Array Nat) (r : Nat) (p : Array Nat) : Bool :=
  decide ((∀ i : Fin r, p.getD i.val 0 < rows.size) ∧
    (∀ i j : Fin r, p.getD i.val 0 = p.getD j.val 0 → i = j) ∧
    (∀ i j : Fin r, adjAt rows (p.getD i.val 0) (p.getD j.val 0) = pathAdj r i.val j.val))

private theorem pathOfArray {V : Type u} {G : Graph V} {rows p : Array Nat} {r : Nat}
    (good : pathValid rows r p = true) (c : Copy G rows.size (adjAt rows)) :
    HasInducedPath G r := by
  obtain ⟨rg, inj, edges⟩ := of_decide_eq_true good
  let f (i : Nat) := c.lab (p.getD i 0)
  refine ⟨⟨f, ?_, ?_⟩⟩
  · intro i j hi hj e
    exact congrArg Fin.val (inj ⟨i,hi⟩ ⟨j,hj⟩ (c.inj (rg ⟨i,hi⟩) (rg ⟨j,hj⟩) e))
  · intro i j hi hj
    exact (c.edge (rg ⟨i,hi⟩) (rg ⟨j,hj⟩)).trans (by rw [edges ⟨i,hi⟩ ⟨j,hj⟩])

def longPath (rows : Array Nat) (r : Nat) (h : PathHints) : Bool :=
  match h.long? with
  | some p => pathValid rows (r+1) p.toArray
  | none => false

theorem longPath_sound {V : Type u} {G : Graph V} {rows : Array Nat} {r : Nat} {h : PathHints}
    (ok : longPath rows r h = true) (c : Copy G rows.size (adjAt rows)) :
    HasInducedPath G (r+1) := by
  unfold longPath at ok
  split at ok
  · exact pathOfArray ok c
  · contradiction

/-- Heuristic only. The value 30 is the default when the endpoint is not
the start of any recorded maximal path. -/
def supportSize (h : PathHints) (a allowed : Nat) : Nat :=
  (h.byEnd.getD a []).foldl (fun best mask => min best (countBitsUpTo best (mask &&& allowed))) 30

end Erdos64
