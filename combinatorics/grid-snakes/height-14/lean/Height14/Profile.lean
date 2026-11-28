import Std

namespace Height14

abbrev Row := Fin 14

private instance {α : Type} [DecidableEq α] : DecidableEq (Row → α) :=
  fun f g => decidable_of_iff (∀ i, f i = g i) ⟨funext, congrFun⟩

/-- What a path forest exposes at the moving cut. Two occupied rows are
    linked when a path in the scanned region joins them. -/
@[ext] structure Profile where
  done : Bool
  occ : Row → Bool
  sat : Row → Bool
  linked : Row → Row → Bool
  isolated : Bool
  deriving DecidableEq

namespace Profile

def empty : Profile := ⟨false, fun _ => false, fun _ => false, fun _ _ => false, false⟩
def finished : Profile := { empty with done := true }

/-- Read a property at the row above, returning false on the top edge. -/
@[inline] def above (f : Row → Bool) (r : Row) : Bool :=
  (r.val != 0) && f ⟨r.val - 1, by omega⟩

@[inline] def touches (p : Profile) (r i : Row) : Bool :=
  p.linked i r || above (p.linked i) r

def keep (p : Profile) (r : Row) : Profile where
  done := false
  occ i := i != r && p.occ i
  sat i := i != r && p.sat i
  linked i j := i != r && j != r && p.linked i j
  isolated := false

def insert (p : Profile) (r : Row) : Profile where
  done := false
  occ i := i == r || p.occ i
  sat i := if i == r then p.occ r && above p.occ r
    else if i.val + 1 == r.val then p.occ i && !p.isolated else p.sat i
  linked i j :=
    if i == r then j == r || p.touches r j
    else if j == r then p.touches r i
    else p.linked i j || (p.touches r i && p.touches r j)
  isolated := r.val + 1 < 14 && !p.occ r && !above p.occ r

def change (p : Profile) (r : Row) (fill : Bool) : Option Profile :=
  if p.done then if fill then none else some finished
  else if fill then
    if p.sat r || above p.sat r || above (p.linked r) r then none
    else some (p.insert r)
  else if !p.occ r || decide (∃ i, i ≠ r ∧ p.linked i r = true) then some (p.keep r)
  else if decide (∃ i, i ≠ r ∧ p.occ i = true) then none
  else some finished

def accept (p : Profile) : Bool :=
  p.done || (decide (∃ i, p.occ i = true) &&
    decide (∀ i j, p.occ i = true → p.occ j = true → p.linked i j = true))

end Profile
end Height14
