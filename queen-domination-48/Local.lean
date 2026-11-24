import Std

/-! Enumerate diagonal covers of a Cartesian subset of the 16 by 16 residue board
when the perimeter bound is tight. A cover records empty columns, empty rows,
occupied differences (with offset 15), and occupied sums. -/
namespace Local

structure Cover where
  x : Nat
  y : Nat
  t : Nat
  s : Nat
  deriving Inhabited, BEq, Repr

private abbrev Mask := UInt64

@[inline] private def bit (i : Nat) : Mask := 1 <<< i.toUInt64
@[inline] private def low (m : Mask) : Mask := m &&& (0-m)

/-- Reverse the bottom sixteen bits. -/
@[inline] private def flip (m : Mask) : Mask := Id.run do
  let mut r : Mask := 0
  for i in [:16] do
    r := (r <<< 1) ||| ((m >>> i.toUInt64) &&& 1)
  return r

@[inline] private def count (m : Mask) : Nat := Id.run do
  let mut r := m
  let mut n := 0
  for _ in [:64] do
    if r == 0 then break
    n := n+1
    r := r &&& (r-1)
  return n

/-- Four sides use bits 0..15, 16..31, 33..46, and 49..62 respectively.
The first two sides include their corners. -/
private structure Box where
  w : Nat
  h : Nat
  tLine : Array Mask
  sLine : Array Mask
  tEnds : Array Mask
  sEnds : Array Mask

private def box (w h : Nat) : Box := Id.run do
  let mut tLine := Array.replicate 64 0
  let mut sLine := Array.replicate 64 0
  let mut ts := Array.replicate 31 (0 : Mask)
  let mut ss := Array.replicate 31 (0 : Mask)
  for x in [:w+1] do
    for y in [:h+1] do
      if x != 0 && x != w && y != 0 && y != h then continue
      let v := if y==0 then x else if y==h then 16+x else if x==0 then 32+y else 48+y
      let d := 15+y-x
      let s := x+y
      tLine := tLine.set! v (bit d)
      sLine := sLine.set! v (bit s)
      ts := ts.modify d (· ||| bit v)
      ss := ss.modify s (· ||| bit v)
  return ⟨w,h,tLine,sLine,tLine.map (fun m => ts[m.log2.toNat]!),
    sLine.map (fun m => ss[m.log2.toNat]!)⟩

/-- Retain labels occurring on at least two of four disjoint sides. -/
@[inline] private def twice (a b c d : Mask) : Mask :=
  (a &&& b) ||| (c &&& d) ||| ((a ||| b) &&& (c ||| d))

@[inline] private def misses (x : Mask) (y : Nat) (t s : Mask) : Bool :=
  x &&& ~~~(flip (t >>> y.toUInt64) ||| (s >>> y.toUInt64)) != 0

private def emit (b : Box) (x y t s : Mask) (all : Bool) (out : Array Cover) : Array Cover := Id.run do
  let mut rows := y
  for _ in [:16] do
    if rows == 0 then break
    if misses x (low rows).log2.toNat t s then return out
    rows := rows &&& (rows-1)
  if !all then return out.push ⟨x.toNat,y.toNat,t.toNat,s.toNat⟩
  let mut result := out
  for dx in [:16-b.w] do
    for dy in [:16-b.h] do
      let td := if dy≥dx then t <<< (dy-dx).toUInt64 else t >>> (dx-dy).toUInt64
      result := result.push ⟨x.toNat <<< dx,y.toNat <<< dy,td.toNat,s.toNat <<< (dx+dy)⟩
  return result

/-- The least remaining needy perimeter point has at most two choices. Its chosen
line must join it to another remaining needy point. Each recursive step removes
both endpoints, so each complete branch is a perimeter matching. -/
private def matchEnds (b : Box) (x y et es rem t s : Mask) (nt ns : Nat) (all : Bool)
    (out : Array Cover) : Nat → Array Cover
  | 0 => if rem == 0 then emit b x y t s all out else out
  | k+1 => Id.run do
    let v := (low rem).log2.toNat
    let mut result := out
    let dt := b.tLine[v]!
    let de := b.tEnds[v]!
    if nt>0 && dt &&& et != 0 && de &&& rem == de then
      result := matchEnds b x y et es (rem ^^^ de) (t ||| dt) s (nt-1) ns all result k
      if !all && !result.isEmpty then return result
    let ds := b.sLine[v]!
    let se := b.sEnds[v]!
    if ns>0 && ds &&& es != 0 && se &&& rem == se then
      result := matchEnds b x y et es (rem ^^^ se) t (s ||| ds) nt (ns-1) all result k
    return result

/-- Masks in this array have fixed population, minimum zero and prescribed maximum. -/
private def axes (n : Nat) : Array (Array Mask) := Id.run do
  let mut groups := Array.replicate 16 #[]
  for i in [:32768] do
    let m := (2*i+1).toUInt64
    if count m == n then groups := groups.modify m.log2.toNat (·.push m)
  return groups

private def solve (e f nt ns : Nat) (all : Bool) : Array Cover := Id.run do
  if e<2 || f<2 || e>16 || f>16 || e+f != nt+ns+2 then return #[]
  let xs := axes e
  let ys := axes f
  let mut out := #[]
  for w in [e-1:16] do
    for h in [f-1:16] do
      let b := box w h
      let wy := (15-w).toUInt64
      let ht := h.toUInt64
      let innerMask := (bit h)-2
      for x in xs[w]! do
        let rx := flip x
        let topT := rx <<< ht
        let topS := x <<< ht
        -- With only X fixed, all interior row indices remain available.
        -- Eliminate rows individually if their whole X row cannot be covered.
        let maxT := twice rx topT (innerMask <<< 15) (innerMask <<< wy)
        let maxS := twice x topS innerMask (innerMask <<< w.toUInt64)
        let mut possible := (bit (h+1))-1
        for j in [:h+1] do
          if misses x j maxT maxS then possible := possible ^^^ bit j
        if count possible < f || possible &&& (1 ||| bit h) != (1 ||| bit h) then continue
        for y in ys[h]! do
          if y &&& possible != y then continue
          let inner := y &&& innerMask
          let et := twice rx topT (inner <<< 15) (inner <<< wy)
          let es := twice x topS inner (inner <<< w.toUInt64)
          if count et < nt || count es < ns || misses x 0 et es || misses x h et es then continue
          if inner &&& ~~~((et >>> 15) ||| es) != 0 then continue
          if inner &&& ~~~((et >>> wy) ||| (es >>> w.toUInt64)) != 0 then continue
          let rem := x ||| (x <<< 16) ||| (inner <<< 32) ||| (inner <<< 48)
          out := matchEnds b x y et es rem 0 0 nt ns all out (nt+ns)
          if !all && !out.isEmpty then return out
  return out

def feasible (e f t s : Nat) : Bool := !(solve e f t s false).isEmpty

def covers (e f t s : Nat) : Array Cover := solve e f t s true

end Local
