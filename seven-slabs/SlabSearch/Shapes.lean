module

public import Std

/-! The dimensions and allowed orientations of an integer slab. -/

@[expose] public section

namespace SevenSlabs

/-- The actual edge lengths, in increasing order, of a slab of order `k`. -/
structure Shape where
  k : Nat
  a : Nat
  b : Nat
  deriving DecidableEq, BEq, Repr, Inhabited

def Shape.vol (s : Shape) := s.k * s.a * s.b

def Shape.Valid (n order : Nat) (s : Shape) : Prop :=
  s.k = order ∧ 0 < order ∧ s.k ≤ s.a ∧ s.a ≤ s.b ∧ s.b ≤ n ∧ s.k ∣ s.a ∧ s.k ∣ s.b

/-- A coordinate triple, also used for the edge lengths in their placed orientation. -/
structure Triple where
  x : Nat
  y : Nat
  z : Nat
  deriving DecidableEq, BEq, Repr, Inhabited

def Shape.orientations (s : Shape) : List Triple :=
  [⟨s.k,s.a,s.b⟩, ⟨s.k,s.b,s.a⟩, ⟨s.a,s.k,s.b⟩,
   ⟨s.a,s.b,s.k⟩, ⟨s.b,s.k,s.a⟩, ⟨s.b,s.a,s.k⟩]

inductive Axis | x | y | z deriving DecidableEq, BEq, Repr

def Triple.along (d : Triple) : Axis → Nat
  | .x => d.x | .y => d.y | .z => d.z

def Triple.area (d : Triple) : Axis → Nat
  | .x => d.y * d.z | .y => d.z * d.x | .z => d.x * d.y

def Triple.vol (d : Triple) := d.x * d.y * d.z

structure Box where
  lo : Triple
  size : Triple
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Assign one permitted slab shape to each order in the given list. -/
def LegalShapes (n : Nat) : List Nat → List Shape → Prop
  | [], [] => True
  | k :: ks, s :: ss => s.Valid n k ∧ LegalShapes n ks ss
  | _, _ => False

end SevenSlabs
