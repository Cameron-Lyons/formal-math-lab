import Std

namespace Height14.Machine

/-- All ones has an impossible base-17 pair and marks a finished snake. -/
def finished : UInt64 := 0xffffffffffffffff

def pivotBit : UInt64 := 0x8000000000000000

/-- Two base-17 digits occupy nine bits. A slot is vacant, a component
label from 1 to 8, or a degree-two vertex with the corresponding label plus 8. -/
@[inline] def slot (s : UInt64) (r : Nat) : UInt64 :=
  let pair := (s >>> (9 * (r / 2)).toUInt64) &&& 511
  if r % 2 == 0 then pair % 17 else pair / 17

@[inline] def put (s : UInt64) (r : Nat) (old new : UInt64) : UInt64 :=
  let weight := (if r % 2 == 0 then 1 else 17 : UInt64) <<< (9 * (r / 2)).toUInt64
  s - old * weight + new * weight

@[inline] def label (v : UInt64) : UInt64 := if v > 8 then v - 8 else v

/-- Renumber components in order of first appearance on the boundary. -/
def canonical (s : UInt64) : UInt64 := Id.run do
  let mut s := s
  let mut names : UInt64 := 0
  let mut count : UInt64 := 0
  for i in [:14] do
    let v := slot s i
    if v != 0 then
      let off := 4 * label v
      let mut name := (names >>> off) &&& 15
      if name == 0 then
        count := count + 1
        name := count
        names := names ||| (name <<< off)
      s := put s i v (if v > 8 then name + 8 else name)
  return s

/-- Scan one square in row `r`, joining it to each occupied old neighbor.
An absent transition rejects the choice. -/
def step (s : UInt64) (r : Nat) (fill : Bool) : Option UInt64 := Id.run do
  if s == finished then return if fill then none else some finished
  let l := slot s r
  let u := if r == 0 then 0 else slot s (r - 1)
  let ll := label l
  let ul := label u
  let isolated := (s &&& pivotBit) != 0
  let mut s := s &&& (~~~pivotBit)
  if !fill then
    if l == 0 then return some s
    s := put s r l 0
    for i in [:14] do
      if label (slot s i) == ll then return some (canonical s)
    return if s == 0 then some finished else none
  if l > 8 || u > 8 || (ll != 0 && ll == ul) then return none
  if u != 0 && !isolated then s := put s (r - 1) u (u + 8)
  if l != 0 && u != 0 then
    for i in [:14] do
      let v := slot s i
      if label v == ll then s := put s i v (if v > 8 then ul + 8 else ul)
  let mut newLabel := if u != 0 then ul else ll
  if newLabel == 0 then
    let mut present : UInt64 := 0
    for i in [:14] do present := present ||| (1 <<< label (slot s i))
    for i in [1:9] do
      if (present &&& (1 <<< i.toUInt64)) == 0 then
        newLabel := i.toUInt64
        break
    if newLabel == 0 then return none
  s := put s r (slot s r) (if u != 0 && l != 0 then newLabel + 8 else newLabel)
  if r + 1 < 14 && u == 0 && l == 0 then s := s ||| pivotBit
  return some (canonical s)

/-- A boundary state accepts if exactly one component has been drawn. -/
def accept (s : UInt64) : Bool := Id.run do
  if s == finished then return true
  if s == 0 then return false
  for i in [:14] do
    if label (slot s i) > 1 then return false
  return true

end Height14.Machine
