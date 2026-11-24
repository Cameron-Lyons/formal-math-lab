import Global

/-! A self-contained finite check for queen domination on the ordinary 48×48 board.
Run from this project directory with `lake exe queens48`. -/

abbrev Histogram := Array Nat

/-- Entries of a histogram are in (column residue, row residue) order. -/
def columnCount (h : Histogram) (i : Nat) := h[3*i]! + h[3*i+1]! + h[3*i+2]!
def rowCount (h : Histogram) (j : Nat) := h[j]! + h[3+j]! + h[6+j]!

/-- If both classes have empty axes, the perimeter inequality implies at least
two queens in the block. Every queen outside it contributes to exactly one
class, so twice the diagonal capacity is too small otherwise. -/
def perimeterAllows (h : Histogram) : Bool := Id.run do
  for i in [:3] do
    if columnCount h i >= 16 then continue
    for j in [:3] do
      if h[3*i+j]! < 2 && rowCount h j < 16 then return false
  return true

/-- Generate all weak compositions without storing the rejected ones. -/
def distributions (placed : Histogram) (left : Nat) : Nat → Array Histogram
  | 0 => let h := placed.push left; if perimeterAllows h then #[h] else #[]
  | slots+1 => Id.run do
    let mut found := #[]
    for a in [:left+1] do
      found := found ++ distributions (placed.push a) (left-a) slots
    return found

/-- A tight block has e empty columns, f empty rows, and t,s occupied diagonals.
Transposition exchanges e,f and reflection exchanges t,s. -/
structure Shape where
  e : Nat
  f : Nat
  t : Nat
  s : Nat
  deriving BEq, Hashable, Inhabited

def tightShapes (h : Histogram) : Array Shape := Id.run do
  let mut shapes := #[]
  for i in [:3] do
    for j in [:3] do
      let c := columnCount h i
      let r := rowCount h j
      if h[3*i+j]! != 2 || c >= 16 || r >= 16 then continue
      let d := (j+3-i)%3
      let a := (i+j)%3
      let t := h[d]! + h[3+(d+1)%3]! + h[6+(d+2)%3]!
      let s := h[a]! + h[3+(a+2)%3]! + h[6+(a+1)%3]!
      let e := 16-c
      let f := 16-r
      shapes := shapes.push ⟨min e f, max e f, min t s, max t s⟩
  return shapes

/-- The published 25-queen cover, in zero-based (column,row) coordinates. -/
def cover25 : Array (Int × Int) :=
  #[(1,20), (3,38), (5,12), (7,30), (9,10), (11,2), (13,22), (15,14),
    (17,44), (19,40), (21,4), (23,28), (25,18), (27,42), (29,24), (31,34),
    (33,0), (35,46), (37,8), (39,36), (41,16), (43,6), (45,32), (47,26), (8,39)]

def verifiesUpperBound : Bool := Id.run do
  if cover25.size != 25 || cover25.any (fun (a,b) => a<0 || a>=48 || b<0 || b>=48) then return false
  for x in [:48] do
    for y in [:48] do
      let x : Int := x
      let y : Int := y
      if !cover25.any (fun (a,b) => x==a || y==b || y-x==b-a || y+x==b+a) then return false
  return true

def main : IO Unit := do
  unless verifiesUpperBound do throw (IO.userError "Invalid 25-queen cover")
  let candidates := distributions #[] 24 8
  let mut cache : Std.HashMap Shape Bool := {}
  let mut survivors := #[]
  for h in candidates do
    let mut possible := true
    for shape in tightShapes h do
      if !cache.contains shape then
        cache := cache.insert shape (Local.feasible shape.e shape.f shape.t shape.s)
      if !cache[shape]! then possible := false
    if possible then survivors := survivors.push h
  IO.println s!"Perimeter allows {candidates.size} histograms. Checking {cache.size} block shapes leaves {survivors.size}."
  let strips := Local.covers 10 8 8 8
  let crosses := Local.covers 8 8 7 7
  IO.println s!"The two local lists contain {strips.size} and {crosses.size} covers."
  unless ← Global.check survivors strips crosses do throw (IO.userError "Unresolved histogram")
  IO.println "No 24-queen cover exists. The listed 25 queens cover all 2,304 squares."
