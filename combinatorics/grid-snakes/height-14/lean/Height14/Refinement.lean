import Height14.Transfer
import Height14.Profile

namespace Height14.Cert

/-- Read the geometric meaning of a packed key independently of the graph builder. -/
@[inline] def decode (k : UInt64) : Profile :=
  if k == Machine.finished then Profile.finished else
  let name (i : Row) := Machine.label (Machine.slot k i.val)
  { done := false
    occ := fun i => Machine.slot k i.val != 0
    sat := fun i => Machine.slot k i.val > 8
    linked := fun i j => name i != 0 && name i == name j
    isolated := k &&& Machine.pivotBit != 0 }

def nextProfile (g : Graph) (r : Row) (i : Nat) (b : Bool) : Option Profile :=
  let j := dest g r.val i b
  let keys := (layer g ((r.val + 1) % 14)).keys
  if 0 < j ∧ j - 1 < keys.size then some (decode (keys.getD (j - 1) 0)) else none

/-- Each table entry is checked against the uncompressed geometric update. -/
def GoodRow (g : Graph) (r : Row) : Prop :=
  let a := layer g r.val
  a.keys.size = a.edges.size ∧ ∀ i, i < a.keys.size → ∀ b : Bool,
    (decode (a.keys.getD i 0)).change r b = nextProfile g r i b

instance (g : Graph) (r : Row) : Decidable (GoodRow g r) := by
  unfold GoodRow
  infer_instance

/-- The empty key starts the scan and the terminal test agrees with geometry. -/
def GoodEnds (g : Graph) : Prop :=
  let keys := (layer g 0).keys
  0 < keys.size ∧ decode (keys.getD 0 0) = Profile.empty ∧
    ∀ i, i < keys.size → (decode (keys.getD i 0)).accept = Machine.accept (keys.getD i 0)

instance (g : Graph) : Decidable (GoodEnds g) := by
  unfold GoodEnds
  infer_instance

/-- The fourteen row checks share the same immutable graph. -/
def checkRows (g : Graph) : Bool :=
  let checks := (List.finRange 14).map fun r => Task.spawn (fun _ => decide (GoodRow g r))
  checks.all (·.get)

theorem checkedRows {g : Graph} (h : checkRows g = true) (r : Row) : GoodRow g r := by
  simp [checkRows, Task.spawn, List.all_eq_true] at h
  exact h r

end Height14.Cert
