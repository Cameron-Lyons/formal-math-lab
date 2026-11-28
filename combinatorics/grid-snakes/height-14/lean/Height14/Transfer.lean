import Height14.Machine

namespace Height14.Cert

/-- A layer stores the reachable keys at a given row of the scan and both
one-square transitions for each key. Destinations are numbered from one. -/
structure Layer where
  keys : Array UInt64 := #[]
  edges : Array Nat := #[]
  deriving Inhabited

abbrev Graph := Array Layer

/-- Each destination index plus one fits in 22 bits. Zero means no edge.
The finite graph check verifies every decoded edge against the original keys. -/
@[inline] def edgeDest (e : Nat) (fill : Bool) : Nat :=
  if fill then e >>> 22 else e &&& 4194303

@[inline] def shift (c v : Nat) : Nat := if v = 0 then 0 else v + c

@[inline] def phase (t : Nat) : Nat := (14 - t % 14) % 14

def layer (g : Graph) (r : Nat) : Layer := g[r]!

def dest (g : Graph) (r i : Nat) (b : Bool) : Nat :=
  edgeDest ((layer g r).edges.getD i 0) b

/-- An absent edge, or an impossible continuation, has value zero.
All other values count squares plus one. -/
@[inline] def edgeValue (a : Array Nat) (j : Nat) (fill : Bool) : Nat :=
  if j = 0 then 0 else shift fill.toNat (a.getD (j - 1) 0)

/-- Scan one square backwards, taking the better legal continuation. -/
def back (g : Graph) (r : Nat) (a : Array Nat) : Array Nat :=
  (layer g r).edges.map fun e =>
    max (edgeValue a (edgeDest e false) false) (edgeValue a (edgeDest e true) true)

/-- With no squares left, only complete, nonempty paths can accept. -/
def initial (g : Graph) : Array Nat :=
  (layer g 0).keys.map fun s => (Machine.accept s).toNat

def vals (g : Graph) : Nat → Array Nat
  | 0 => initial g
  | t+1 => back g (phase (t+1)) (vals g t)

end Height14.Cert
