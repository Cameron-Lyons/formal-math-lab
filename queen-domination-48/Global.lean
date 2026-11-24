import Local

/-! Join exact local line sets on the common residue classes. A global
mask for a difference d has its bit at 47+d. Sums use their own index. -/
namespace Global

open Local (Cover)

private def ones (n : Nat) := (1 <<< n) - 1
private def difference (a b : Nat) := a ^^^ (a &&& b)
private def bit (a i : Nat) : Bool := (a >>> i) &&& 1 == 1

private def scatter (mask n base : Nat) : Nat := Id.run do
  let mut result := 0
  for i in [:n] do
    if bit mask i then result := result ||| (1 <<< (base+3*i))
  return result

private def liftCover (p : Cover) (a b : Nat) : Cover :=
  ⟨scatter p.x 16 a, scatter p.y 16 b, scatter p.t 31 (2+b-a), scatter p.s 31 (a+b)⟩

private def byKey {α : Type} [BEq α] [Hashable α] (vs : Array Cover) (key : Cover → α) :
    Std.HashMap α (Array Cover) := Id.run do
  let mut groups : Std.HashMap α (Array Cover) := {}
  for v in vs do groups := groups.alter (key v) (fun g => some ((g.getD #[]).push v))
  return groups

private def reflect (mask : Nat) : Nat := Id.run do
  let mut result := 0
  for k in [:95] do
    if bit mask k then result := result ||| (1 <<< (94-k))
  return result

/-- Every occupied row y requires a pair of occupied diagonal labels t,s
with t+s=2y. At index 47−t in the shifted mask, we read its bit at 2y−t. -/
private def stripPossible (a b c : Cover) : Bool := Id.run do
  let emptyRows := a.y ||| b.y ||| c.y
  let reflectedT := a.t ||| b.t ||| c.t
  let sums := (a.s ||| b.s ||| c.s) <<< 47
  for y in [:48] do
    if !bit emptyRows y && reflectedT &&& (sums >>> (2*y)) == 0 then return false
  return true

private def strips (vs : Array Cover) (a : Nat) : Nat × Nat := Id.run do
  let records := fun j => vs.map fun v =>
    let p := liftCover v a j
    { p with t := reflect p.t }
  let g1 := byKey (records 1) Cover.x
  let g2 := byKey (records 2) Cover.x
  let mut count := 0
  let mut alive := 0
  for u in records 0 do
    for v in g1.getD u.x #[] do
      for w in g2.getD u.x #[] do
        count := count+1
        if stripPossible u v w then alive := alive+1
  return (count,alive)

private structure Moments where
  count : Nat := 0
  sum : Int := 0
  squares : Int := 0

private def moments (mask offset : Nat) : Moments := Id.run do
  let mut result : Moments := {}
  for i in [:95] do
    if bit mask i then
      let k := (i : Int) - offset
      result := ⟨result.count+1, result.sum+k, result.squares+k*k⟩
  return result

/-- A square on two empty axes has to use a diagonal. If one slope is
unavailable, the other label is required. With 23 or 24 distinct required
labels in each slope, its missing multiset entry is determined by summing
x+y and y−x. The square identity then tests those two completions. -/
private def crossPossible (emptyX emptyY fixedT fixedS openT openS : Nat) : Bool := Id.run do
  let mut neededT := fixedT
  let mut neededS := fixedS
  for x in [:48] do
    if !bit emptyX x then continue
    let uncovered := difference emptyY ((fixedT >>> (47-x)) ||| (fixedS >>> x))
    let canT := openT >>> (47-x)
    let canS := openS >>> x
    if difference uncovered (canT ||| canS) != 0 then return false
    neededT := neededT ||| (difference uncovered canS <<< (47-x))
    neededS := neededS ||| (difference uncovered canT <<< x)
  let t := moments neededT 47
  let s := moments neededS 0
  if t.count > 24 || s.count > 24 then return false
  if t.count < 23 || s.count < 23 then return true
  let x := moments (difference (ones 48) emptyX) 0
  let y := moments (difference (ones 48) emptyY) 0
  if x.count != 24 || y.count != 24 then return true
  let d := y.sum-x.sum-t.sum
  let a := y.sum+x.sum-s.sum
  if (t.count == 24 && d != 0) || (s.count == 24 && a != 0) then return false
  return t.squares+s.squares+d*d+a*a == 2*(x.squares+y.squares)

private def diagClass (r : Nat) := scatter (ones 32) 32 r &&& ones 95

private def crosses (vs : Array Cover) (i j : Nat) : Nat × Nat := Id.run do
  let i₁ := (i+1)%3
  let i₂ := (i+2)%3
  let j₁ := (j+1)%3
  let j₂ := (j+2)%3
  let byX := byKey (vs.map (liftCover · i j₂)) Cover.x
  let c1 := byKey (vs.map (liftCover · i₁ j)) (fun p => (p.t,p.s))
  let c2 := byKey (vs.map (liftCover · i₂ j)) (fun p => (p.t,p.s))
  let tc := fun a => diagClass ((47+j-a)%3)
  let sc := fun a => diagClass ((a+j)%3)
  let mut count := 0
  let mut alive := 0
  for a in vs.map (liftCover · i j₁) do
    for b in byX.getD a.x #[] do
      let t := a.t ||| b.t
      let s := a.s ||| b.s
      for c in c1.getD (t &&& tc i₁, s &&& sc i₁) #[] do
        for d in c2.getD (t &&& tc i₂, s &&& sc i₂) #[] do
          if c.y != d.y then continue
          count := count+1
          if crossPossible (a.x ||| c.x ||| d.x) (a.y ||| b.y ||| c.y) t s (tc i) (sc i) then
            alive := alive+1
  return (count,alive)

/-- Under transposition, use a column strip if one exists. Its three tight
blocks must have the four line counts 6,8,8,8. -/
private def stripShape (v : Array Nat) (i : Nat) (transpose : Bool) : Bool := Id.run do
  let h := fun x y => if transpose then v[3*y+x]! else v[3*x+y]!
  for j in [:3] do
    if h i j != 2 || h 0 j + h 1 j + h 2 j != 8 then return false
    if h 0 j + h 1 ((j+1)%3) + h 2 ((j+2)%3) != 8 then return false
    if h 0 j + h 1 ((j+2)%3) + h 2 ((j+1)%3) != 8 then return false
  return true

private def crossShape (v : Array Nat) (i j : Nat) : Bool := Id.run do
  for x in [:3] do for y in [:3] do
    if v[3*x+y]! != (if x==i && y==j then 4 else if x==i || y==j then 2 else 3) then return false
  return true

/-- Refute a histogram only if it has a tested shape and every compatible
choice of the local line sets in the tight blocks of that shape is excluded. -/
def check (histograms : Array (Array Nat)) (strip cross : Array Cover) : IO Bool := do
  let mut stripResults := #[]
  let mut crossResults := #[]
  let mut nstrip := 0
  let mut ncross := 0
  for i in [:3] do
    let (n,left) := strips strip i
    stripResults := stripResults.push (left==0)
    nstrip := nstrip+n
    for j in [:3] do
      let (n,left) := crosses cross i j
      crossResults := crossResults.push (left==0)
      ncross := ncross+n
  for v in histograms do
    if v.size != 9 then return false
    let mut refuted := false
    for i in [:3] do
      if stripResults[i]! && (stripShape v i false || stripShape v i true) then refuted := true
      for j in [:3] do
        if crossResults[3*i+j]! && crossShape v i j then refuted := true
    if !refuted then return false
  IO.println s!"All {nstrip} strip joins and {ncross} cross joins were excluded."
  return true

end Global
