/-! Szabó's lower-bound construction for Erdős problem 272 on fourteen points. -/

namespace Erdos272Fourteen

/-- Bit `i` represents the label `i + 1` in {1,…,14}. -/
abbrev Mask := BitVec 14

def elements (s : Mask) : List Nat :=
  ((List.range 14).filter s.getLsbD).map (· + 1)

/-- Nonempty arithmetic progressions include singletons and pairs. -/
def IsAP (s : Mask) : Prop :=
  ∃ a d k : Nat, 0 < d ∧ 0 < k ∧ elements s = (List.range k).map (fun i => a + i * d)

private def step : List Nat → Nat
  | a :: b :: _ => b - a
  | _ => 1

private def checkAP (s : Mask) : Bool :=
  let xs := elements s
  let a := xs.headD 0
  let d := step xs
  decide (0 < d ∧ 0 < xs.length ∧ xs = (List.range xs.length).map (fun i => a + i * d))

private theorem checkAP_sound {s : Mask} (h : checkAP s = true) : IsAP s :=
  ⟨(elements s).headD 0, step (elements s), (elements s).length, of_decide_eq_true h⟩

private def bit (i : Nat) : Mask := 1 <<< i

private def others : List Nat := (List.range 14).filter (· != 6)

/-- The 92 sets of at most three points that contain 7. -/
private def baseFamily : List Mask :=
  [bit 6] ++ others.map (fun i => bit 6 ||| bit i) ++
    others.flatMap (fun i =>
      (others.filter (i < ·)).map (fun j => bit 6 ||| bit i ||| bit j))

/-- Select positions in the five-term arithmetic progression centred at 7 with step `d`. -/
private def localMask (d : Nat) (positions : List Nat) : Mask :=
  positions.foldl (fun s j => s ||| bit (6 - 2 * d + j * d)) 0

/-- For each step 1, 2, 3, replace two triples by the full progression and its four-term ends. -/
def witness : List Mask :=
  let steps := [1, 2, 3]
  let remove := steps.flatMap (fun d => [[0, 2, 3], [1, 2, 4]].map (localMask d))
  let add := steps.flatMap (fun d =>
    [[0, 1, 2, 3, 4], [0, 1, 2, 3], [1, 2, 3, 4]].map (localMask d))
  baseFamily.filter (fun s => !remove.contains s) ++ add

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem witness_check :
    witness.length = 95 ∧ witness.Nodup ∧
      witness.Pairwise (fun a b => checkAP (a &&& b) = true) := by decide +kernel

/-- There are 95 distinct subsets of {1,…,14} whose pairwise intersections are nonempty APs. -/
theorem exists_family_95 :
    ∃ family : List Mask, family.length = 95 ∧ family.Nodup ∧
      family.Pairwise (fun a b => IsAP (a &&& b)) :=
  ⟨witness, witness_check.1, witness_check.2.1,
    witness_check.2.2.imp fun h => checkAP_sound h⟩

end Erdos272Fourteen
