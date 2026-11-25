import Std

/-! Finite transition certificate for the treewidth-three argument.
The combinatorial interpretation of three-boundary graphs is in the accompanying
proof. This module proves the exclusion for every expression in the profile
grammar. The finite computation uses `native_decide`. -/

namespace Erdos64.TreewidthProfiles

/-- Boundary degrees capped at three. The six masks give the lengths through
or avoiding the third boundary vertex for pairs 01, 02 and 12, in that order;
the avoiding mask comes first in each pair. Only lengths up to 15 are stored. -/
structure Profile where
  degrees : Array Nat
  paths : Array Nat
  deriving DecidableEq, Repr, Inhabited

private def zero : Profile := ⟨#[0,0,0], #[0,0,0,0,0,0]⟩
private def pairEnds := #[(0,1), (0,2), (1,2)]
private def pairId (a b : Nat) := if a = 0 then b-1 else if b = 0 then a-1 else 2
private def target : Nat := 2^4 + 2^8 + 2^16

/-- Length-set convolution, retaining sums through 16. -/
private def convolution (a b : Nat) : Nat := Id.run do
  let mut x := a
  let mut y := b
  let mut s := 0
  for _ in [:16] do
    if x == 0 then break
    if x % 2 == 1 then s := s ||| y
    x := x / 2
    y := y <<< 1
  return s &&& 131071

private structure Step where
  a : Nat
  b : Nat
  via : Nat
  part : Nat
  slot : Nat
  isEdge : Bool

private structure Route where
  output : Nat
  edges : Nat
  factors : List Nat
  deriving BEq

/-- Enumerate the routes on at most four named vertices. Every component is used
at most once. A transit that uses its third terminal marks that vertex visited. -/
private def routes (faces : List (Array Nat)) (edges : List (Nat × Nat))
    (order : Nat) : List Route := Id.run do
  let mut steps : List Step := []
  for (f, face) in faces.zipIdx.map Prod.swap do
    for p in [:3] do
      let (i,j) := pairEnds[p]!
      for pass in [:2] do
        let via := if pass == 0 then 0 else 1 <<< face[3-i-j]!
        steps := ⟨face[i]!, face[j]!, via, f, 6*f+2*p+pass, false⟩ :: steps
  for ((a,b),i) in edges.zipIdx do
    steps := ⟨a,b,0,faces.length+i,i,true⟩ :: steps
  let rec walk (fuel root atV seen parts edgeMask : Nat) (fs : List Nat) : List Route :=
    match fuel with
    | 0 => []
    | n+1 => steps.flatMap fun s => Id.run do
      if parts.testBit s.part || (s.via &&& seen) != 0 || (atV != s.a && atV != s.b) then return []
      let w := if atV == s.a then s.b else s.a
      if w != root && seen.testBit w then return []
      let used := seen ||| s.via ||| (1 <<< w)
      let required := if s.isEdge then edgeMask ||| (1 <<< s.slot) else edgeMask
      let factors := if s.isEdge then fs else s.slot :: fs
      if w == root then return [⟨6, required, factors.mergeSort⟩]
      let more := walk n root w used (parts ||| (1 <<< s.part)) required factors
      if root < w && w < 3 then
        let output := 2 * pairId root w + (used.testBit (3-root-w)).toNat
        return ⟨output, required, factors.mergeSort⟩ :: more
      return more
  return ((List.range order).flatMap fun root => walk order root root (1 <<< root) 0 0 []).eraseDups

private def triangles := [(0,1),(0,2),(1,2)]
private def parallelRoutes := routes [#[0,1,2], #[0,1,2]] [] 3
private def apexRoutes := routes [#[0,1,3], #[0,2,3], #[1,2,3]] [(0,3),(1,3),(2,3)] 4
private def rootRoutes := routes [#[0,1,2]] triangles 3

private def bitCount3 (m : Nat) := (m.testBit 0).toNat + (m.testBit 1).toNat + (m.testBit 2).toNat

private def lengths (r : Route) (edges : Nat) (params : Array Nat) : Nat :=
  if (r.edges &&& edges) != r.edges then 0 else
  -- Every factor has length at most 15. Shift the bare-edge count last.
  let paths := r.factors.foldl (fun acc j => convolution params[j]! acc) 1
  paths <<< bitCount3 r.edges

private def hasCycle (rs : List Route) (edges : Nat) (params : Array Nat) :=
  rs.any fun r => r.output == 6 && (lengths r edges params &&& target) != 0

private def compute (rs : List Route) (edges : Nat) (params ds : Array Nat) : Option Profile := Id.run do
  if hasCycle rs edges params then return none
  let mut ps := #[0,0,0,0,0,0]
  for r in rs do
    if r.output < 6 then
      ps := ps.modify r.output fun p => p ||| (lengths r edges params &&& 65535)
  return some ⟨ds.map (min 3), ps⟩

private def link (a b : Profile) (i j : Nat) : Bool :=
  let u := a.paths[2*i]! ||| a.paths[2*i+1]!
  let v := b.paths[2*j]! ||| b.paths[2*j+1]!
  (convolution u v &&& target) == 0

/-- Two graphs on the same independent boundary. -/
def parallel (a b : Profile) :=
  compute parallelRoutes 0 (a.paths ++ b.paths) ((Array.range 3).map fun i => a.degrees[i]! + b.degrees[i]!)

/-- Degree of the new interior vertex of an apex transition. -/
def apexDegree (a b c : Profile) (edges : Fin 8) :=
  a.degrees[2]! + b.degrees[2]! + c.degrees[2]! + bitCount3 edges.val

/-- Introduce an internal vertex 3 with three possible edges to 0, 1 and 2.
The child faces are 013, 023 and 123. A failed link test already gives a cycle
using just the two children meeting along that pair of terminals. -/
def apex (a b c : Profile) (edges : Fin 8) : Option Profile := Id.run do
  let m := edges.val
  if apexDegree a b c edges < 3 then return none
  if !(link a b 1 1 && link a c 2 1 && link b c 2 2) then return none
  return compute apexRoutes m (a.paths ++ b.paths ++ c.paths) #[
    a.degrees[0]! + b.degrees[0]! + (m.testBit 0).toNat,
    a.degrees[1]! + c.degrees[0]! + (m.testBit 1).toNat,
    b.degrees[1]! + c.degrees[1]! + (m.testBit 2).toNat]

/-- Degree at a boundary vertex after supplying the final boundary edges.
The contribution of the original profile is capped at three. -/
def rootDegree (s : Profile) (edges : Fin 8) (i : Fin 3) : Nat :=
  let incident := triangles.zipIdx.filter fun ((a,b),j) =>
    (a == i.val || b == i.val) && edges.val.testBit j
  s.degrees[i.val]! + incident.length

/-- Detect a 4-, 8- or 16-cycle introduced by the supplied root edges. -/
def rootHasTarget (s : Profile) (edges : Fin 8) : Bool :=
  hasCycle rootRoutes edges.val s.paths

/-- Supply the remaining boundary edges, then test degrees and cycle avoidance. -/
def accepts (s : Profile) (edges : Fin 8) : Bool :=
  (List.finRange 3).all (fun i => 3 ≤ rootDegree s edges i) && !rootHasTarget s edges

/-- Bit mask for all lengths in the inclusive interval. -/
private def interval (lo hi : Nat) : Nat := 2^(hi + 1) - 2^lo

/-- Extend the ports selected by the three-bit mask. An extended endpoint
adds one edge to the path. An extended third port becomes a leaf, so both
old path types avoid the new boundary vertex. -/
private def extendPorts (pairs : Array (Nat × Nat)) (mask : Nat) : Profile := Id.run do
  let ext := fun i => (mask.testBit i).toNat
  let mut paths := #[]
  for k in [:3] do
    let (i,j) := pairEnds[k]!
    let (avoid,through) := pairs[k]!
    let (avoid,through) := if mask.testBit (3-i-j) then (avoid ||| through, 0) else (avoid,through)
    let shift := fun n => (n <<< (ext i + ext j)) &&& 65535
    paths := (paths.push (shift avoid)).push (shift through)
  return ⟨(Array.range 3).map (fun i => 2 - ext i), paths⟩

/-- Emit the allowable leaf extensions, each with its interior order. -/
private def extensions (order minLeaves : Nat) (pairs : Array (Nat × Nat)) : List (Profile × Nat) :=
  ((List.range 8).filter fun mask => minLeaves ≤ bitCount3 mask).map fun mask =>
    (extendPorts pairs mask, order - 3 + bitCount3 mask)

/-- For the two asymmetric cores each boundary pair can be the outer pair. -/
private def outerPairs (order : Nat) (outer other : Nat × Nat) : List (Profile × Nat) :=
  (List.range 3).flatMap fun k =>
    extensions order 0 ((Array.range 3).map fun i => if i == k then outer else other)

/-- The empty piece, star, triangle, H₇, subdivided K₄ and H₁₅.
The path masks for each core record paths avoiding and visiting the third
port, respectively. Only the triangle requires at least two leaves. -/
private def entries : List (Profile × Nat) :=
  [(zero, 0), (⟨#[1,1,1], #[4,0,4,0,4,0]⟩, 1)] ++
  extensions 3 2 (Array.replicate 3 (interval 1 1, interval 2 2)) ++
  outerPairs 7 (interval 3 5, interval 4 6) (interval 2 5, interval 5 6) ++
  extensions 7 0 (Array.replicate 3 (interval 2 4, interval 5 6)) ++
  outerPairs 15 (interval 5 13, interval 6 14) (interval 3 13, interval 8 14)

private def catalogue : List Profile := entries.map Prod.fst

def interiorWeight (p : Profile) := ((entries.find? fun e => e.1 == p).map Prod.snd).getD 0

private def covered (result : Option Profile) (expected : Unit → Nat) :=
  result.all fun p => catalogue.contains p && interiorWeight p == expected ()
private def masks := List.finRange 8

private theorem initial : zero ∈ catalogue := by decide
private theorem parallel_closed : catalogue.all (fun a => catalogue.all fun b =>
    covered (parallel a b) (fun _ => interiorWeight a + interiorWeight b)) = true := by native_decide
private theorem apex_closed : catalogue.all (fun a => catalogue.all fun b => catalogue.all fun c =>
    masks.all fun m => covered (apex a b c m)
      (fun _ => 1 + interiorWeight a + interiorWeight b + interiorWeight c)) = true := by native_decide
private theorem apex_degree_checked : catalogue.all (fun a => catalogue.all fun b => catalogue.all fun c =>
    masks.all fun m => (apex a b c m).isNone || apexDegree a b c m == 3) = true := by native_decide
private theorem size_bound_checked : catalogue.all (fun p => interiorWeight p ≤ 15) = true := by native_decide
private theorem two_degrees_size_checked : catalogue.all (fun p => masks.all fun m =>
    rootHasTarget p m || !((List.finRange 3).all fun i => 2 ≤ rootDegree p m i) ||
      [0,4,12].contains (interiorWeight p)) = true := by native_decide
private theorem root_degrees_checked : catalogue.all (fun p => masks.all fun m =>
    rootHasTarget p m || (List.finRange 3).all fun i => rootDegree p m i ≤ 2) = true := by native_decide

/-- Expressions for the three-boundary profile grammar. -/
inductive Expression where
  | empty
  | parallel (a b : Expression)
  | apex (a b c : Expression) (edges : Fin 8)

def Expression.run : Expression → Option Profile
  | .empty => some zero
  | .parallel a b => do TreewidthProfiles.parallel (← a.run) (← b.run)
  | .apex a b c m => do TreewidthProfiles.apex (← a.run) (← b.run) (← c.run) m

/-- Count forgotten vertices. All three boundary vertices are retained separately. -/
def Expression.interiorCount : Expression → Nat
  | .empty => 0
  | .parallel a b => a.interiorCount + b.interiorCount
  | .apex a b c _ => 1 + a.interiorCount + b.interiorCount + c.interiorCount

private theorem lookup {p : Profile} {w : Unit → Nat} (h : covered (some p) w = true) :
    p ∈ catalogue ∧ interiorWeight p = w () := by
  simpa [covered] using h

private theorem run_info (t : Expression) {p : Profile} (h : t.run = some p) :
    p ∈ catalogue ∧ interiorWeight p = t.interiorCount := by
  induction t generalizing p with
  | empty => cases h; exact ⟨initial, by rfl⟩
  | parallel a b ha hb =>
    simp only [Expression.run, Bind.bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, hp⟩ := h
    obtain ⟨mx, wx⟩ := ha hx
    obtain ⟨my, wy⟩ := hb hy
    have row := List.all_eq_true.mp parallel_closed x mx
    have checked := List.all_eq_true.mp row y my
    simpa only [Expression.interiorCount, ← wx, ← wy] using lookup (hp ▸ checked)
  | apex a b c m ha hb hc =>
    simp only [Expression.run, Bind.bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, z, hz, hp⟩ := h
    obtain ⟨mx, wx⟩ := ha hx
    obtain ⟨my, wy⟩ := hb hy
    obtain ⟨mz, wz⟩ := hc hz
    have rowX := List.all_eq_true.mp apex_closed x mx
    have rowY := List.all_eq_true.mp rowX y my
    have rowZ := List.all_eq_true.mp rowY z mz
    have checked := List.all_eq_true.mp rowZ m (by simp [masks])
    simpa only [Expression.interiorCount, ← wx, ← wy, ← wz] using lookup (hp ▸ checked)

/-- Every successful introduction of an interior vertex in the clean grammar
assigns degree exactly three to that vertex. The other operations leave all
existing interior degrees unchanged. -/
theorem clean_apex_degree {a b c : Expression} {x y z p : Profile} (m : Fin 8)
    (va : a.run = some x) (vb : b.run = some y) (vc : c.run = some z)
    (clean : apex x y z m = some p) : apexDegree x y z m = 3 := by
  have row := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp apex_degree_checked
    x (run_info a va).1) y (run_info b vb).1) z (run_info c vc).1
  have check := List.all_eq_true.mp row m (by simp [masks])
  simpa [clean] using check

/-- In the clean grammar the profile determines the exact number of interior vertices. -/
theorem interior_count_of_profile (t : Expression) {p : Profile} (h : t.run = some p) :
    t.interiorCount = interiorWeight p := (run_info t h).2.symm

/-- An expression avoiding the three cycle lengths has at most 15 interior vertices. -/
theorem interior_count_le_fifteen (t : Expression) {p : Profile} (h : t.run = some p) :
    t.interiorCount ≤ 15 := by
  rw [interior_count_of_profile t h]
  simpa using List.all_eq_true.mp size_bound_checked p (run_info t h).1

/-- If the three boundary vertices have final degree at least two, the only
possible numbers of interior vertices are 0, 4, and 12. -/
theorem size_of_two_degree_root (t : Expression) {p : Profile} (edges : Fin 8)
    (valid : t.run = some p) (clean : rootHasTarget p edges = false)
    (degrees : ∀ i, 2 ≤ rootDegree p edges i) : t.interiorCount ∈ [0,4,12] := by
  have row := List.all_eq_true.mp two_degrees_size_checked p (run_info t valid).1
  have check := List.all_eq_true.mp row edges (by simp [masks])
  have all : ((List.finRange 3).all fun i => decide (2 ≤ rootDegree p edges i)) = true :=
    List.all_eq_true.mpr fun i _ => by simpa using degrees i
  rw [interior_count_of_profile t valid]
  simpa [clean, all] using check

/-- If a three-boundary expression and its final edges avoid 4-, 8- and
16-cycles, every boundary vertex has degree at most two. The bound holds for
all eight final edge sets, with arbitrary degrees at the other two vertices. -/
theorem clean_root_degrees (t : Expression) {p : Profile} (edges : Fin 8)
    (valid : t.run = some p) (clean : rootHasTarget p edges = false) (i : Fin 3) :
    rootDegree p edges i ≤ 2 := by
  have row := List.all_eq_true.mp root_degrees_checked p (run_info t valid).1
  have check := List.all_eq_true.mp row edges (by simp [masks])
  rw [clean, Bool.false_or] at check
  simpa using List.all_eq_true.mp check i (by simp)

/-- No expression in the finite profile grammar can pass the final root test. -/
theorem no_accepted_expression (t : Expression) (edges : Fin 8) :
    (t.run.any fun p => accepts p edges) = false := by
  cases e : t.run with
  | none => rfl
  | some p =>
    change accepts p edges = false
    cases h : rootHasTarget p edges with
    | true => simp [accepts, h]
    | false =>
      have bound := clean_root_degrees t edges e h 0
      have tooSmall : ¬ ((List.finRange 3).all fun i => decide (3 ≤ rootDegree p edges i)) = true := by
        intro all
        have enough := List.all_eq_true.mp all 0 (by simp)
        simp at enough
        omega
      simp [accepts, h, Bool.eq_false_iff.mpr tooSmall]

/-- Witnesses attaining the bounds 15 and 12 on the number of interior vertices.
The larger graph consists of H15 with a pendant boundary vertex at each port. -/
private def witnessPair : Expression × Expression := Id.run do
  let e := Expression.empty
  let star := Expression.apex e e e 7
  let left := Expression.apex e e star 5
  let right := Expression.apex e e star 3
  let a := Expression.apex left right e 0
  let b := Expression.apex e e left 1
  let c := Expression.apex left e b 0
  let twelve := Expression.apex a e c 0
  let attach := fun t => Expression.apex e e t 1
  return (attach (attach (attach twelve)), twelve)

theorem sharp_interior_bounds :
    (∃ t : Expression, t.interiorCount = 15 ∧ t.run.isSome = true) ∧
    (∃ t : Expression, t.interiorCount = 12 ∧ (t.run.any fun p =>
      !rootHasTarget p 0 && (List.finRange 3).all fun i => 2 ≤ rootDegree p 0 i) = true) := by
  exact ⟨⟨witnessPair.1, by native_decide⟩, ⟨witnessPair.2, by native_decide⟩⟩

end Erdos64.TreewidthProfiles
