import Lean

/-! A support in the 15 by 15 grid has fifteen candidate points. Search for five
lines covering it, then verify the returned lines and point assignments in the
kernel. Each row represents one line modulo 5; columns are the 84 triples of
distinct residues modulo 3. -/

namespace Grid75.CRT

/-- The 84 three-element subsets of the nine residue pairs modulo 3, packed
as three four-bit indices. -/
def triples : Array Nat := by
  run_tac
    let mut entries := #[]
    for a in [:9] do
      for b in [a+1:9] do
        for c in [b+1:9] do
          entries := entries.push (a + 16*b + 256*c)
    (← Lean.Elab.Tactic.getMainGoal).assign (Lean.toExpr entries)

/-- Parameterize the line of slope l/5 and intercept l%5, including vertical lines. -/
def lineResidue (l i : Nat) : Nat × Nat :=
  if l / 5 = 5 then (l % 5, i) else (i, ((l / 5)*i + l % 5) % 5)

def tripleResidue (m k : Nat) : Nat := (triples[m]! >>> (4*k)) % 16

/-- Combine the residues of one coordinate modulo 5 and 3 in the range 0 to 14. -/
def combine (a b : Nat) : Nat := a + 5 * ((2 * (b + 6 - a)) % 3)

def locate (l m j : Nat) : Nat × Nat :=
  let (x,y) := lineResidue l (j % 5)
  let r := tripleResidue m (j / 5)
  (combine x (r % 3), combine y (r / 3))

structure Line where
  x : Int
  y : Int
  dx : Int
  dy : Int

/-- Membership in the ordinary integer line with the given anchor and direction. -/
def Line.contains (s : Line) (x y : Int) : Bool :=
  decide ((s.dx ≠ 0 ∨ s.dy ≠ 0) ∧ (x-s.x)*s.dy = (y-s.y)*s.dx)

private def unpackSegment (a b : Nat) : Line :=
  ⟨a % 15, a / 15, ((b % 15 : Nat) : Int) - (a % 15), ((b / 15 : Nat) : Int) - (a / 15)⟩

private abbrev Cell := Nat × Nat
private abbrev Segment := Nat × Nat

private def cellIndex (p : Cell) : Nat := p.1 + 15 * p.2

private def liesOn (s : Segment) (p : Cell) : Bool :=
  (unpackSegment s.1 s.2).contains p.1 p.2

/-- Try the lines through the first uncovered point, largest first. -/
private def cover : Nat → List Cell → Option (List Segment)
  | _, [] => some []
  | 0, _ => none
  | _ + 1, [p] => some [(cellIndex p, cellIndex p + 1)]
  | k + 1, p :: q :: rest =>
    let others := q :: rest
    let alternatives := others.map fun r =>
      let line := (cellIndex p, cellIndex r)
      (line, others.filter fun z => !liesOn line z)
    (alternatives.mergeSort (fun a b => a.2.length ≤ b.2.length)).findSome? fun (line, leftover) =>
      (cover k leftover).map (line :: ·)

/-- Five 16-bit segments followed by fifteen 3-bit segment indices. -/
private def pack (points : List Cell) (lines : List Segment) : Nat :=
  let segments := lines.foldr (fun (u,v) acc => u + 256*v + (acc <<< 16)) 0
  let assignments := points.foldr (fun p acc => lines.findIdx (fun s => liesOn s p) + (acc <<< 3)) 0
  segments + (assignments <<< 80)

private def searchRow (l : Nat) : Option Nat := do
  let mut row := 0
  for m in [:84] do
    let points := (List.range 15).map (locate l m)
    let lines ← cover 5 points
    row := row + (pack points lines <<< (125*m))
  return row

def segmentIndex (word j : Nat) : Fin 5 := ⟨((word >>> (80 + 3*j)) % 8) % 5, by omega⟩

def segmentAt (word : Nat) (i : Fin 5) : Line :=
  let segment := word >>> (16*i.val)
  unpackSegment (segment % 256) ((segment / 256) % 256)

def certifies (l m j word : Nat) : Bool :=
  let (x,y) := locate l m j
  (segmentAt word (segmentIndex word j)).contains x y

private def checkRow (l : Nat) (ar : Nat) : Bool :=
  (List.finRange 84).all fun m =>
    (List.finRange 15).all fun j => certifies l m.val j.val ((ar >>> (125*m.val)) % (2^125))


/-- The search generates numerical witnesses at elaboration time. Each row is
then checked by the kernel against the integer determinant. -/
private def bank : Array Nat := by
  run_tac
    let mut rows := #[]
    for l in [:30] do
      let some row := searchRow l | throwError "no five-line cover found for row {l}"
      rows := rows.push row
    (← Lean.Elab.Tactic.getMainGoal).assign (Lean.toExpr rows)

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000 in
private theorem row_checked (n : Nat) (h : n < 30) : checkRow n bank[n]! = true := by
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9
  | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19
  | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 => decide +kernel
  | n + 30 => omega

def selectWord (l : Fin 30) (m : Fin 84) : Nat := (bank[l.val]! >>> (125 * m.val)) % (2^125)

theorem selected_certifies (l : Fin 30) (m : Fin 84) (j : Fin 15) :
    certifies l.val m.val j.val (selectWord l m) = true := by
  have r := row_checked l.val l.isLt
  have c := List.all_eq_true.mp r m (List.mem_finRange _)
  exact List.all_eq_true.mp c j (List.mem_finRange _)

end Grid75.CRT
