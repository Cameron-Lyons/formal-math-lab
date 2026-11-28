/-! Szabó's lower-bound construction for Erdős problem 272 at n = 16. -/

namespace Erdos272Sixteen

/-- Bit `i` represents the element `i + 1` of {1,…,16}. -/
abbrev Mask := BitVec 16

/-- Members of the encoded set in increasing order, using the original labels 1,…,16. -/
def elements (s : Mask) : List Nat :=
  ((List.range 16).filter s.getLsbD).map (· + 1)

/-- A nonempty arithmetic progression, allowing one or two terms. -/
def IsAP (s : Mask) : Prop :=
  ∃ a d k : Nat, 0 < d ∧ 0 < k ∧ elements s = (List.range k).map (fun i => a + i * d)

/-- Common difference from the first two terms, or `1` for a singleton. -/
private def step : List Nat → Nat
  | a :: b :: _ => b - a
  | _ => 1

private def checkShortAP (s : Mask) : Bool :=
  let xs := elements s
  let a := xs.headD 0
  let d := step xs
  decide (0 < d ∧ 0 < xs.length ∧ xs = (List.range xs.length).map (fun i => a + i * d) ∧
    xs.length ≤ 4)

private theorem checkShortAP_sound {s : Mask} (h : checkShortAP s = true) :
    IsAP s ∧ (elements s).length ≤ 4 := by
  obtain ⟨hd, hk, heq, hlen⟩ := of_decide_eq_true h
  exact ⟨⟨(elements s).headD 0, step (elements s), (elements s).length, hd, hk, heq⟩, hlen⟩

private def bit (i : Nat) : Mask := 1 <<< i

private def others : List Nat := (List.range 16).filter (· != 7)

/-- All sets of at most three elements containing 8. -/
private def baseFamily : List Mask :=
  [bit 7] ++ others.map (fun i => bit 7 ||| bit i) ++
    others.flatMap (fun i =>
      (others.filter (i < ·)).map (fun j => bit 7 ||| bit i ||| bit j))

/-- Select positions in the five-term progression centred at 8 with step `d`. -/
private def localMask (d : Nat) (positions : List Nat) : Mask :=
  positions.foldl (fun s j => s ||| bit (7 - 2 * d + j * d)) 0

/-- For each step 1, 2, 3, replace two triples by the five-term AP and its two four-term ends. -/
def witness : List Mask :=
  let steps := [1, 2, 3]
  let remove := steps.flatMap (fun d => [[0, 2, 3], [1, 2, 4]].map (localMask d))
  let add := steps.flatMap (fun d =>
    [[0, 1, 2, 3, 4], [0, 1, 2, 3], [1, 2, 3, 4]].map (localMask d))
  baseFamily.filter (fun s => !remove.contains s) ++ add

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem witness_check :
    witness.length = 124 ∧ witness.Nodup ∧
      witness.Pairwise (fun a b => checkShortAP (a &&& b) = true) := by decide +kernel

/-- Every intersection in the 124-member construction has at most four terms. -/
theorem witness_short_intersections :
    witness.Pairwise (fun a b => IsAP (a &&& b) ∧ (elements (a &&& b)).length ≤ 4) :=
  witness_check.2.2.imp fun h => checkShortAP_sound h

/-- There are 124 distinct subsets whose pairwise intersections are nonempty APs. -/
theorem exists_family_124 :
    ∃ family : List Mask, family.length = 124 ∧ family.Nodup ∧
      family.Pairwise (fun a b => IsAP (a &&& b)) :=
  ⟨witness, witness_check.1, witness_check.2.1,
    witness_short_intersections.imp fun h => h.1⟩

end Erdos272Sixteen
