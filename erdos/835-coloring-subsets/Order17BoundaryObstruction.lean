module

public import certificates.Order17Partial20
public import MultiplierSAT
public import Std.Sat.CNF.Dimacs
public import Mathlib.Basic.ExistsUnique
meta import certificates.Order17Partial20
meta import MultiplierSAT
meta import Std.Sat.CNF.Dimacs
meta import Std.Tactic.BVDecide.Reflect

@[expose] public section

/-! # No cyclic completion of the specified 145-block boundary

All new blocks must lie on the seventeen moving labels. A completion chooses
one quadruple through each still-uncovered triple and one from each translation
orbit. The exact-cover clauses below are generated from those conditions and
the checked boundary. At build time the bundled CaDiCaL produces an LRAT proof,
which is checked using the soundness theorem of Lean's standard library. -/

namespace Erdos835.Order17BoundaryObstruction

open Erdos835.Order17Partial20 Erdos835.MultiplierSAT
open Std.Tactic.BVDecide

/-- Rotate the low seventeen incidence bits and use the least rotation to name an orbit. -/
def orbitKey (b : Nat) : Nat :=
  (List.range 17).foldl (fun best s =>
    min best (((b <<< s) % 131072) ||| (b >>> (17 - s)))) b

def usedTriples : List Nat := (seed.flatMap faces).map mask

/-- All moving quadruples that avoid every triple already covered by the seed. -/
def candidates : List Nat :=
  ((subsets 4 (List.range 17)).filter fun q =>
    (faces q).all (fun t => !(usedTriples.contains (mask t)))).map mask

inductive Requirement where
  | triple (mask : Nat)
  | orbit (leastRotation : Nat)
  deriving DecidableEq, Repr

def requirements : List Requirement :=
  let triples := ((subsets 3 (List.range 17)).map mask).filter fun t => !(usedTriples.contains t)
  let orbits := ((subsets 4 (List.range 17)).map fun q => orbitKey (mask q)).eraseDups
  triples.map Requirement.triple ++ orbits.map Requirement.orbit

def meets : Requirement → Nat → Bool
  | .triple t, b => (b &&& t) == t
  | .orbit o, b => orbitKey b == o

/-- A choice of moving quadruples meets each geometric requirement exactly once. -/
def Completes (chosen : Nat → Bool) : Prop :=
  ∀ r ∈ requirements, ∃! b, b ∈ candidates ∧ meets r b = true ∧ chosen b = true

private def options (r : Requirement) : List Nat := candidates.filter (meets r)

private def exclusions (xs : List Nat) : List (List Lit) :=
  xs.flatMap fun b => (xs.filter (b < ·)).map fun c => [(b,false),(c,false)]

private def clauses : List (List Lit) :=
  (requirements.map fun r => (options r).map (·, true)) ++
  (requirements.flatMap fun r => exclusions (options r))

private theorem givesAssignment (chosen : Nat → Bool) (h : Completes chosen) :
    ∀ C ∈ clauses, clauseTrue chosen C := by
  intro C hc
  rw [clauses, List.mem_append] at hc
  rcases hc with hc | hc
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
    obtain ⟨b, ⟨hb, hm, hp⟩, _⟩ := h r hr
    exact ⟨(b,true), List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨hb, hm⟩, rfl⟩, hp⟩
  · obtain ⟨r, hr, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨b, hb, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨c, hcc, rfl⟩ := List.mem_map.mp hc
    obtain ⟨hc, hlt⟩ := List.mem_filter.mp hcc
    have hne : b ≠ c := Nat.ne_of_lt (of_decide_eq_true hlt)
    obtain ⟨b₀, _, unique⟩ := h r hr
    obtain ⟨hb', hm⟩ := List.mem_filter.mp hb
    obtain ⟨hc', hn⟩ := List.mem_filter.mp hc
    cases eb : chosen b with
    | false => exact ⟨(b,false), by simp, eb⟩
    | true =>
      cases ec : chosen c with
      | false => exact ⟨(c,false), by simp, ec⟩
      | true =>
        exact (hne ((unique b ⟨hb', hm, eb⟩).trans (unique c ⟨hc', hn, ec⟩).symm)).elim

open Lean in
elab "boundaryLRAT%" : term => do
  let mOrbitKey (b : Nat) : Nat :=
    (List.range 17).foldl (fun best s =>
      min best (((b <<< s) % 131072) ||| (b >>> (17 - s)))) b
  let mUsedTriples : List Nat := (seed.flatMap faces).map mask
  let mCandidates : List Nat :=
    ((subsets 4 (List.range 17)).filter fun q =>
      (faces q).all (fun t => !(mUsedTriples.contains (mask t)))).map mask
  let mTriples := ((subsets 3 (List.range 17)).map mask).filter fun t => !(mUsedTriples.contains t)
  let mOrbits := ((subsets 4 (List.range 17)).map fun q => mOrbitKey (mask q)).eraseDups
  let mOpts (p : Nat → Bool) : List Nat := mCandidates.filter p
  let mExcl (xs : List Nat) : List (List Lit) :=
    xs.flatMap fun b => (xs.filter (b < ·)).map fun c => [(b, false), (c, false)]
  let mReqOpts : List (List Nat) :=
    (mTriples.map fun t => mOpts fun b => (b &&& t) == t) ++
    (mOrbits.map fun o => mOpts fun b => mOrbitKey b == o)
  let mClauses : List (List Lit) :=
    (mReqOpts.map fun os => os.map (·, true)) ++
    (mReqOpts.flatMap mExcl)
  let proof ← IO.FS.withTempDir fun dir => do
    let cnfFile := dir / "boundary.cnf"
    let proofFile := dir / "boundary.lrat"
    IO.FS.writeFile cnfFile (toCNF mClauses).dimacs
    let solver := (← IO.appDir) / "cadical"
    let run ← IO.Process.output {
      cmd := solver.toString
      args := #["--quiet", "--lrat", "--no-binary", cnfFile.toString, proofFile.toString] }
    unless run.exitCode == 20 do
      throwError "CaDiCaL exited {run.exitCode}: {run.stderr} {run.stdout}"
    IO.FS.readFile proofFile
  return mkStrLit proof

private def traceFile : String := boundaryLRAT%

private theorem trace_valid : Reflect.verifyCert (toCNF clauses) traceFile = true := by
  native_decide

/-- The specific 145-block certificate admits no completion compatible with all 17 translates. -/
theorem cannot_complete (chosen : Nat → Bool) : ¬ Completes chosen := fun h =>
  of_verified clauses traceFile trace_valid chosen (givesAssignment chosen h)

end Erdos835.Order17BoundaryObstruction
