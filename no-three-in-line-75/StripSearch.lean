import Grid75
import Lean

/-! A certificate rules out a completion from a list of retained points.
At a node we choose a row or a column and exempt one of its cells.
Every other cell either lies on a secant of two retained points or leads to
a child node where that cell is retained. A 150-point solution needs two
points on the chosen line, so it must enter one of the children. -/

namespace Grid75.StripSearch

private def cell (vertical : Bool) (i j : Fin 75) : Point :=
  if vertical then (i, j) else (j, i)

private theorem needs_another {s : List Point} (size : s.length = 150)
    (nd : s.Nodup) (nt : NoThree s) (v : Bool) (i except : Fin 75) :
    ∃ j : Fin 75, j ≠ except ∧ cell v i j ∈ s := by
  classical
  apply Classical.byContradiction
  intro no
  have miss (j : Fin 75) (hne : j ≠ except) : cell v i j ∉ s := fun m => no ⟨j, hne, m⟩
  let coord : Point → Fin 75 := if v then Prod.fst else Prod.snd
  have len : (fiber coord s i).length = 2 := by
    have e := equality_forces_two_per_row_and_column size nd nt i
    cases v <;> simp_all [coord]
  have sub : fiber coord s i ⊆ [cell v i except] := by
    intro p hp
    obtain ⟨hs, hi⟩ := List.mem_filter.mp hp
    have hcoord : coord p = i := beq_iff_eq.mp hi
    rcases p with ⟨x, y⟩
    cases v
    · change y = i at hcoord
      subst y
      have ex : x = except := Classical.byContradiction (fun ne => miss x ne hs)
      simp [cell, ex]
    · change x = i at hcoord
      subst x
      have ex : y = except := Classical.byContradiction (fun ne => miss y ne hs)
      simp [cell, ex]
  have small := (nd.sublist List.filter_sublist).length_le_of_subset sub
  change (fiber coord s i).length ≤ 1 at small
  omega

private def address (p : Point) : Nat := p.1.val + 75 * p.2.val

private def decode (k : Nat) : Point := (Fin.ofNat 75 k, Fin.ofNat 75 (k / 75))

private theorem decode_address (p : Point) : decode (address p) = p := by
  rcases p with ⟨x, y⟩
  have hx := x.isLt
  have hy := y.isLt
  apply Prod.ext <;> apply Fin.ext <;> simp only [decode, address, Fin.ofNat] <;> omega

/-- A known point is recorded at its zero-based grid address. -/
private def insertPoint (known : Nat) (p : Point) : Nat := known ||| (1 <<< address p)

private def KnownIn (known : Nat) (s : List Point) : Prop :=
  ∀ i, known.testBit i = true → decode i ∈ s

private theorem known_insert {s : List Point} {known : Nat} (h : KnownIn known s)
    {p : Point} (hp : p ∈ s) : KnownIn (insertPoint known p) s := by
  intro i hi
  simp [insertPoint, Nat.shiftLeft_eq, Nat.testBit_two_pow] at hi
  rcases hi with ha | he
  · exact h i ha
  · simpa [← he, decode_address] using hp

/-- A cell is unavailable when it forms a collinear triple of distinct
points with two retained cells. -/
private def blocked (known p a b : Nat) : Bool :=
  let x := decode p
  let y := decode a
  let z := decode b
  known.testBit a && known.testBit b && (x != y) && (x != z) && (y != z) && (det x y z == 0)

private theorem blocked_sound {s : List Point} (nt : NoThree s) {known : Nat}
    (inc : KnownIn known s) {p : Point} {a b : Nat}
    (ok : blocked known (address p) a b = true) : p ∉ s := by
  simp only [blocked, decode_address, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at ok
  obtain ⟨⟨⟨⟨⟨ha, hb⟩, na⟩, nb⟩, nab⟩, col⟩ := ok
  exact fun hp => nt.exclude_triple (by simp [na, nb, nab]) col hp (inc a ha) (inc b hb)

private def cellAddress (line j : Nat) : Nat :=
  if line ≥ 75 then line % 75 + 75*j else j+75*line

private theorem cellAddress_eq (line : Nat) (j : Fin 75) :
    cellAddress line j.val = address (cell (decide (line ≥ 75)) (Fin.ofNat 75 line) j) := by
  by_cases h : 75 ≤ line
  · simp [cellAddress, cell, address, h, Fin.ofNat]
  · simp [cellAddress, cell, address, h, Fin.ofNat, Nat.mod_eq_of_lt (by omega : line < 75)]

/-- No 150-point solution contains all the points marked by this bit mask. -/
def Refuted (fixed : Nat) : Prop :=
  ∀ {s : List Point}, s.length = 150 → s.Nodup → NoThree s → KnownIn fixed s → False

/-- A node packs a line number and its exception into two bytes, followed
by 75 twenty-seven-bit entries. An odd entry names a previously proved
child. An even entry gives two thirteen-bit grid addresses for a secant. -/
def checkNode (fixed word : Nat) (children : List {k : Nat // Refuted k}) : Bool :=
  let line := word % 256
  let except := ((word >>> 8) % 256) % 75
  (List.range 75).all fun j =>
    if j = except then true else
    let p := cellAddress line j
    let code := (word >>> (16 + 27 * j)) % 134217728
    if code % 2 = 1 then
      match children[code / 2]? with
      | some child => child.val == (fixed ||| (1 <<< p))
      | none => false
    else blocked fixed p ((code / 16384) % 8192) ((code / 2) % 8192)

/-- Refute a node using only the local secant checks and its proved children. -/
theorem step (fixed word : Nat) (children : List {k : Nat // Refuted k})
    (ok : checkNode fixed word children = true) : Refuted fixed := by
  intro s size nd nt known
  unfold checkNode at ok
  let line := word % 256
  let except := Fin.ofNat 75 ((word >>> 8) % 256)
  obtain ⟨j, ne, hj⟩ := needs_another size nd nt (decide (line ≥ 75)) (Fin.ofNat 75 line) except
  have h := List.all_eq_true.mp ok j.val (List.mem_range.mpr j.isLt)
  dsimp only at h
  have hne : j.val ≠ ((word >>> 8) % 256) % 75 := fun e => ne (Fin.ext e)
  rw [ite_eq_right hne] at h
  simp only [cellAddress_eq _ j] at h
  split at h
  · split at h
    next child _ =>
      apply child.property size nd nt
      rw [beq_iff_eq.mp h]
      exact known_insert known hj
    next => contradiction
  · exact (blocked_sound nt known h) hj

/-- The last row is free. Only seed points in the original 74 rows outside
the specified consecutive band are retained. -/
def retained (first width : Nat) : Array Point :=
  (witness148.filter (fun p => decide (p.2.val < first ∨ first + width ≤ p.2.val))).toArray

private def knownMask (ps : List Point) : Nat := ps.foldr (fun p k => insertPoint k p) 0

private theorem mask_sound {ps s : List Point} (sub : ps ⊆ s) : KnownIn (knownMask ps) s := by
  induction ps with
  | nil => simp [KnownIn, knownMask, Nat.zero_testBit]
  | cons p ps ih =>
    apply known_insert (ih (fun _ h => sub (List.mem_cons_of_mem _ h))) (sub (by simp))

def seedMask (first width : Nat) : Nat := knownMask (retained first width).toList

theorem strip_sound {first width : Nat} (bad : Refuted (seedMask first width))
    {s : List Point} (keep : (retained first width).toList ⊆ s) (nd : s.Nodup)
    (nt : NoThree s) : s.length ≠ 150 :=
  fun size => bad size nd nt (mask_sound keep)

open Lean Elab Command

private def board : Nat := (1 <<< 5625) - 1

private def gridAddress (line j : Nat) : Nat :=
  if line < 75 then j + 75*line else line-75 + 75*j

private def lineMasks : Array Nat := (Array.range 150).map fun line =>
  (List.range 75).foldl (fun k j => k ||| (1 <<< gridAddress line j)) 0

private partial def popcount (x : Nat) : Nat :=
  if x = 0 then 0 else popcount (x &&& (x-1)) + 1

private structure Position where
  points : List Nat := []
  fixed : Nat := 0
  available : Nat := board
  /-- Encoded witness pair for each cell eliminated by a secant. -/
  blocker : Array Nat := Array.replicate 5625 0

private partial def Position.select (s : Position) (p : Nat) : Position := Id.run do
  let x : Int := p % 75
  let y : Int := p / 75
  let mut available := s.available ^^^ (1 <<< p)
  let mut blocker := s.blocker
  for a in s.points do
    let dx := (a % 75 : Nat) - (x : Int)
    let dy := (a / 75 : Nat) - (y : Int)
    let g : Int := Nat.gcd dx.natAbs dy.natAbs
    for sign in [-1, 1] do
      let (u,v) := (sign * (dx/g), sign * (dy/g))
      let mut (i,j) := (x+u, y+v)
      while 0 ≤ i && i < 75 && 0 ≤ j && j < 75 do
        let cell := i.toNat + 75 * j.toNat
        if available.testBit cell then
          available := available ^^^ (1 <<< cell)
          blocker := blocker.set! cell (2 * (8192*a + p))
        i := i+u
        j := j+v
  return ⟨p :: s.points, s.fixed ||| (1 <<< p), available, blocker⟩

private def Position.chooseLine (s : Position) : Nat × Nat := Id.run do
  let mut best := 10000
  let mut choice := (0, 0)
  for i in [:150] do
    let selected := s.fixed &&& lineMasks[i]!
    let taken := popcount selected
    if taken ≥ 2 then continue
    let free := s.available &&& lineMasks[i]!
    let count := popcount free
    -- Prefer a deficient line, followed by the smallest number of spare cells.
    let score := if taken+count < 2 then count else 100 + (taken+count-2)*100 + count
    if score < best then
      best := score
      let cell := (if selected != 0 then selected else free).log2
      let except := if i < 75 then cell % 75 else cell / 75
      choice := (i, except)
  return choice

/-- Construct `step fixed word [⟨k₁,h₁⟩, …] rfl`. The kernel evaluates
the checker when verifying that `rfl` has the required type. -/
private def stepProof (fixed word : Nat) (children : List (Nat × Expr)) : Expr :=
  let prop := mkConst ``Refuted
  let arg := mkConst ``Nat
  let ty := mkApp2 (mkConst ``Subtype [.one]) arg prop
  let pairs := children.foldr (fun (bits,proof) rest =>
    let child := mkApp4 (mkConst ``Subtype.mk [.one]) arg prop (mkNatLit bits) proof
    mkApp3 (mkConst ``List.cons [.zero]) ty child rest) (mkApp (mkConst ``List.nil [.zero]) ty)
  let valid := mkApp2 (mkConst ``Eq.refl [.one]) (mkConst ``Bool) (mkConst ``Bool.true)
  mkApp4 (mkConst ``step) (mkNatLit fixed) (mkNatLit word) pairs valid

private partial def Position.refute (s : Position) : Except String Expr := do
  if s.points.length == 150 then throw "found a 150-point completion"
  let (line,except) := s.chooseLine
  let mut word := line + 256*except
  let mut children := #[]
  for j in [:75] do
    if j == except then continue
    let p := gridAddress line j
    let mut code := s.blocker[p]!
    if s.available.testBit p then
      let next := s.select p
      let proof ← next.refute
      code := 2 * children.size + 1
      children := children.push (next.fixed,proof)
    else if code == 0 then throw s!"missing secant on line {line}, cell {j}"
    word := word ||| (code <<< (16 + 27*j))
  return stepProof s.fixed word children.toList

private def AllStrips (width first count : Nat) : Prop :=
  ∀ i : Fin count, Refuted (seedMask (i.val + first) width)

private theorem emptyStrips (width first : Nat) : AllStrips width first 0 := by intro i; exact Fin.elim0 i

private theorem prependStrip (width first count : Nat) (head : Refuted (seedMask first width))
    (tail : AllStrips width (first+1) count) : AllStrips width first (count+1) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using head
  · simpa [Nat.succ_add, Nat.add_assoc] using tail j

/-- Verify every consecutive strip of the requested width. The search constructs
a proof tree per strip, which the kernel checks before it is combined with the others. -/
elab "refute_strips " name:ident width:num count:num : command => do
  let w := width.getNat
  let n := count.getNat
  let ns ← getCurrNamespace
  let theoremName := ns ++ name.getId
  let mut all := mkApp2 (mkConst ``emptyStrips) (mkNatLit w) (mkNatLit n)
  for i in [:n] do
    let first := n-i-1
    let points := (retained first w).toList
    let s := points.foldl (fun (q : Position) p => q.select (p.1.val + 75*p.2.val)) {}
    let proof ← match s.refute with
      | .ok proof => pure proof
      | .error message => throwError message
    let key := if name.getId == `certificates then ns ++ Name.mkSimple s!"Window{first}" ++ `refuted
      else theoremName ++ Name.mkSimple s!"window{first}"
    let mask := mkApp2 (mkConst ``seedMask) (mkNatLit first) (mkNatLit w)
    liftCoreM <| addDecl (.thmDecl {
      name := key
      levelParams := []
      type := mkApp (mkConst ``Refuted) mask
      value := proof })
    all := mkApp5 (mkConst ``prependStrip) (mkNatLit w) (mkNatLit first) (mkNatLit i) (mkConst key) all
  liftCoreM <| addDecl (.thmDecl {
    name := theoremName
    levelParams := []
    type := mkApp3 (mkConst ``AllStrips) (mkNatLit w) (mkNatLit 0) (mkNatLit n)
    value := all })

end Grid75.StripSearch
