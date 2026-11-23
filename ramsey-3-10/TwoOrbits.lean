import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser
import Std

/-!
On two cycles of length 20, simultaneous rotation gives 40 possible edge orbits.
Every clause in the certificate is generated from the vertex pairs of an actual
three- or ten-element set. The LRAT refutation shows that no choice of edge orbits
avoids all of those obstructions.
-/

namespace Ramsey310.TwoOrbits
open Std.Sat Std.Tactic.BVDecide

abbrev Vertex := Fin 40
abbrev Graph := Vertex → Vertex → Bool

/-- Add k to the position in each of the cycles 0..19 and 20..39. -/
def shift (k : Nat) (v : Vertex) : Vertex :=
  Fin.ofNat 40 (20 * (v.val / 20) + (v.val + k) % 20)

/-- Within each cycle, record the shorter undirected distance. Between cycles, record
the offset from the endpoint in the first cycle to the endpoint in the second. -/
private def orbit (v w : Vertex) : Nat :=
  let x := v.val % 20
  let y := w.val % 20
  let d := max x y - min x y
  if v.val / 20 = w.val / 20 then
    10 * (v.val / 20) + (min d (20 - d) - 1)
  else if v.val < 20 then 20 + (y + 20 - x) % 20
  else 20 + (x + 20 - y) % 20

private def representative (i : Nat) : Vertex × Vertex :=
  if i < 10 then (0, Fin.ofNat 40 (i + 1))
  else if i < 20 then (20, Fin.ofNat 40 (20 + (i - 10) + 1))
  else (0, Fin.ofNat 40 i)

/-- Iterate the one-step rotation on an ordered pair. -/
private def rotatePair : Nat → Vertex × Vertex → Vertex × Vertex
  | 0, p => p
  | k + 1, p =>
    let (x, y) := rotatePair k p
    (shift 1 x, shift 1 y)

/-- An edge is a rotation of its representative in one of the two orientations. -/
private theorem coversPairs : ∀ v w : Vertex, v ≠ w →
    let p := representative (orbit v w)
    rotatePair (v.val % 20) p = (v, w) ∨ rotatePair (w.val % 20) p = (w, v) := by
  decide +kernel

abbrev HasTriangle (g : Graph) : Prop :=
  ∃ vs : List Vertex, vs.length = 3 ∧ vs.Nodup ∧ vs.Pairwise (fun v w => g v w = true)
abbrev HasIndependentTen (g : Graph) : Prop :=
  ∃ vs : List Vertex, vs.length = 10 ∧ vs.Nodup ∧ vs.Pairwise (fun v w => g v w = false)

private def orbitList : List Vertex → List Nat
  | [] => []
  | x :: xs => (xs.map (orbit x)) ++ orbitList xs

private def clause (vs : List Vertex) : CNF.Clause Nat :=
  let orbits := (orbitList vs).eraseDups.mergeSort
  .ofLiterals (orbits.map (fun i => (i, decide (vs.length = 10))))

private def decode (s : String) : Array (List Vertex) := Id.run do
  let mut result := #[]
  for row in s.splitOn "\n" do
    if row.isEmpty then continue
    result := result.push ((row.splitOn " ").filterMap fun val => do
      let n ← val.toNat?
      if h : n < 40 then some ⟨n, h⟩ else none)
  return result

private def sets := decode (include_str "certificates" / "two-orbits.sets")
private def formula : CNF Nat := ⟨sets.map clause⟩
private def proofSteps :=
  (LRAT.parseLRATProof (include_str "certificates" / "two-orbits.lrat").toUTF8).toOption.getD #[]

private theorem checked : formula.Unsat := LRAT.check_sound proofSteps formula (by native_decide)
private theorem validSets :
    ∀ vs ∈ sets, vs.Nodup ∧ (vs.length = 3 ∨ vs.length = 10) := by native_decide

/-- Testing every orbit in a row amounts to testing every pair of its vertices. -/
private theorem all_orbits (vs : List Vertex) (P : Nat → Prop) :
    (∀ i ∈ orbitList vs, P i) ↔ vs.Pairwise (fun v w => P (orbit v w)) := by
  induction vs with
  | nil => simp [orbitList]
  | cons v vs ih =>
    simp only [orbitList, List.forall_mem_append, List.forall_mem_map, List.pairwise_cons, ih]

/-- A false clause forces all its pairs to have the opposite color to its literals. -/
private theorem clause_false (vs : List Vertex) (a : Nat → Bool) :
    (clause vs).eval a = false ↔
      vs.Pairwise (fun v w => a (orbit v w) ≠ decide (vs.length = 10)) := by
  rw [← all_orbits vs (fun i => a i ≠ decide (vs.length = 10))]
  simp [clause, CNF.Clause.eval, List.any_map, List.any_eq_false, Function.comp_def]

/-- Every undirected graph on the two cycles for which simultaneous one-step rotation
preserves adjacency contains a triangle or an independent ten-element set. -/
theorem two_cycles_of_length_twenty (g : Graph)
    (sym : ∀ u v, g u v = g v u)
    (rot : ∀ u v, g (shift 1 u) (shift 1 v) = g u v) :
    HasTriangle g ∨ HasIndependentTen g := by
  let color := Function.uncurry g
  have rotate_color (k : Nat) (p : Vertex × Vertex) : color (rotatePair k p) = color p := by
    induction k with
    | zero => rfl
    | succ k ih => exact (rot (rotatePair k p).1 (rotatePair k p).2).trans ih
  let orbitColor := fun i => color (representative i)
  have edge_color {v w : Vertex} (h : v ≠ w) : g v w = orbitColor (orbit v w) := by
    obtain direct | reverse := coversPairs v w h
    · exact (congrArg color direct).symm.trans (rotate_color ..)
    · exact (sym v w).trans ((congrArg color reverse).symm.trans (rotate_color ..))
  have unsat := checked orbitColor
  simp only [formula, CNF.eval, Array.all_eq_false', Array.mem_map] at unsat
  obtain ⟨_, ⟨vs, member, rfl⟩, failed⟩ := unsat
  obtain ⟨distinct, size⟩ := validSets vs member
  have byOrbit := (clause_false vs orbitColor).mp (by simpa using failed)
  have byEdge := distinct.imp₂ (fun _ _ hne hcolor => (edge_color hne).symm ▸ hcolor) byOrbit
  rcases size with h3 | h10
  · exact Or.inl ⟨vs, h3, distinct, by simpa [h3] using byEdge⟩
  · exact Or.inr ⟨vs, h10, distinct, by simpa [h10] using byEdge⟩

end Ramsey310.TwoOrbits
