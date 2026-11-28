import Std

/-!
Triple covers of 61 people. The displayed group lists use labels 1 through 61.
The proofs use zero-based `Fin 61` internally. Run with Lean 4.36.0.
-/

set_option Elab.async false

namespace Covering61

abbrev Person := Fin 61

/-- A group is represented by its 61 membership bits. Person 0 is bit 0. -/
def members (mask : Nat) : List Person :=
  (List.finRange 61).filter fun x => mask.testBit x.val

theorem mem_members (x : Person) (mask : Nat) :
    x ∈ members mask ↔ mask.testBit x.val = true := by
  simp [members, List.mem_finRange]

/-- All people who occur with both a and b in one of the given groups. -/
def companions (a b : Person) : List Nat → Nat
  | [] => 0
  | g :: rest =>
    (if g.testBit a.val && g.testBit b.val then g else 0) ||| companions a b rest

theorem companions_spec (a b c : Person) (groups : List Nat) :
    (companions a b groups).testBit c.val = true ↔
      ∃ g ∈ groups, a ∈ members g ∧ b ∈ members g ∧ c ∈ members g := by
  induction groups with
  | nil => simp [companions]
  | cons g rest ih =>
    by_cases ha : g.testBit a.val = true <;> by_cases hb : g.testBit b.val = true <;>
      simp [companions, Nat.testBit_or, ha, hb, ih, mem_members, Bool.or_eq_true]

def fullMask : Nat := 2^61 - 1

private theorem fullMask_contains : ∀ c : Person, fullMask.testBit c.val = true := by
  decide +kernel

def coversAll (groups : List Nat) : Bool :=
  (List.finRange 61).all fun a => (List.finRange 61).all fun b =>
    companions a b groups == fullMask

theorem coversAll_sound {groups : List Nat} (h : coversAll groups = true) (a b c : Person) :
    ∃ g ∈ groups, a ∈ members g ∧ b ∈ members g ∧ c ∈ members g := by
  have hab := List.all_eq_true.mp (List.all_eq_true.mp h a (List.mem_finRange a)) b
    (List.mem_finRange b)
  have heq : companions a b groups = fullMask := eq_of_beq hab
  exact (companions_spec a b c groups).mp (by rw [heq]; exact fullMask_contains c)

/-- Each group has 25 distinct people, and every triple occurs together.
    The coverage clause also holds if two or three of the people coincide. -/
def IsCover (n : Nat) (groups : List (List Person)) : Prop :=
  groups.length = n ∧ groups.Nodup ∧
  (∀ g ∈ groups, g.length = 25 ∧ g.Nodup) ∧
  ∀ a b c : Person, ∃ g ∈ groups, a ∈ g ∧ b ∈ g ∧ c ∈ g

theorem certify {groups : List Nat} {n : Nat}
    (hn : groups.length = n) (hd : (groups.map members).Nodup)
    (hs : groups.all (fun g => (members g).length == 25) = true)
    (hc : coversAll groups = true) : IsCover n (groups.map members) := by
  refine ⟨by simpa using hn, hd, ?_, ?_⟩
  · intro block hmem
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hmem
    exact ⟨eq_of_beq (List.all_eq_true.mp hs g hg),
      List.Pairwise.filter _ (List.nodup_finRange 61)⟩
  · intro a b c
    obtain ⟨g, hg, h⟩ := coversAll_sound hc a b c
    exact ⟨members g, List.mem_map.mpr ⟨g, hg, rfl⟩, h⟩

/-- Convert the source's one-based person labels to membership bits. -/
def pack (labels : List Nat) : Nat :=
  labels.foldl (fun bits i => bits ||| (1 <<< (i - 1))) 0

/-- Caleb Ashton's published 27 groups, in their original order and numbering.
    https://kaust-a-laut.github.io/results/covering-C61-25-3-27/README.md -/
def published : List Nat := [
  pack [5, 6, 8, 11, 13, 16, 17, 23, 26, 27, 28, 30, 31, 33, 41, 44, 45, 46, 48, 49, 51, 53, 55, 58, 61],
  pack [2, 4, 5, 6, 7, 11, 13, 17, 20, 24, 30, 31, 32, 34, 40, 45, 46, 47, 50, 52, 56, 58, 59, 60, 61],
  pack [1, 5, 6, 10, 11, 12, 13, 15, 17, 18, 19, 22, 29, 30, 31, 35, 38, 39, 42, 45, 46, 54, 56, 58, 61],
  pack [1, 3, 9, 13, 14, 16, 18, 20, 27, 28, 29, 30, 31, 32, 33, 34, 38, 40, 41, 42, 46, 50, 51, 52, 53],
  pack [1, 3, 4, 5, 6, 10, 14, 17, 18, 20, 21, 22, 23, 32, 34, 37, 38, 39, 40, 42, 43, 50, 54, 57, 61],
  pack [1, 5, 6, 10, 17, 18, 21, 23, 26, 28, 29, 32, 33, 34, 37, 38, 40, 41, 50, 53, 54, 55, 56, 59, 61],
  pack [4, 8, 9, 10, 11, 22, 28, 32, 33, 34, 39, 40, 41, 43, 44, 45, 48, 49, 50, 52, 53, 54, 56, 57, 58],
  pack [2, 3, 5, 6, 7, 9, 11, 13, 14, 17, 21, 24, 25, 30, 31, 36, 37, 43, 45, 46, 47, 56, 57, 58, 61],
  pack [2, 3, 4, 7, 10, 11, 14, 16, 22, 23, 24, 25, 26, 27, 29, 36, 39, 45, 47, 51, 52, 54, 55, 56, 58],
  pack [2, 3, 4, 5, 6, 7, 12, 14, 15, 17, 19, 20, 23, 24, 26, 28, 33, 35, 41, 43, 47, 53, 55, 57, 61],
  pack [2, 7, 9, 10, 16, 20, 21, 22, 24, 26, 27, 29, 32, 34, 37, 39, 40, 43, 47, 50, 51, 54, 57, 59, 60],
  pack [8, 11, 13, 16, 21, 23, 26, 27, 29, 30, 31, 32, 34, 37, 40, 44, 45, 46, 48, 49, 50, 51, 55, 56, 58],
  pack [2, 7, 10, 12, 13, 15, 16, 19, 22, 24, 27, 28, 29, 30, 31, 33, 35, 39, 41, 46, 47, 51, 53, 54, 56],
  pack [10, 12, 13, 15, 19, 20, 21, 22, 25, 30, 31, 32, 34, 35, 36, 37, 39, 40, 43, 46, 50, 52, 54, 55, 57],
  pack [1, 3, 4, 11, 12, 14, 15, 18, 19, 21, 25, 26, 32, 34, 35, 36, 37, 38, 40, 42, 45, 50, 52, 56, 58],
  pack [3, 5, 6, 8, 12, 14, 15, 16, 17, 19, 21, 27, 29, 35, 37, 43, 44, 48, 49, 51, 52, 57, 59, 60, 61],
  pack [1, 4, 13, 16, 18, 21, 25, 27, 28, 29, 30, 31, 33, 36, 37, 38, 41, 42, 43, 46, 51, 53, 57, 59, 60],
  pack [2, 7, 9, 12, 15, 19, 21, 23, 24, 25, 28, 32, 33, 34, 35, 36, 37, 40, 41, 47, 50, 52, 53, 59, 60],
  pack [1, 2, 7, 8, 11, 12, 15, 18, 19, 24, 28, 29, 33, 35, 38, 41, 42, 44, 45, 47, 48, 49, 53, 56, 58],
  pack [1, 5, 6, 9, 10, 17, 18, 22, 23, 25, 26, 28, 33, 36, 38, 39, 41, 42, 52, 53, 54, 55, 59, 60, 61],
  pack [4, 5, 6, 8, 9, 12, 15, 16, 17, 19, 20, 25, 27, 29, 32, 34, 35, 36, 40, 44, 48, 49, 50, 51, 61],
  pack [1, 2, 7, 8, 13, 18, 20, 23, 24, 25, 26, 30, 31, 36, 38, 42, 43, 44, 46, 47, 48, 49, 52, 55, 57],
  pack [1, 2, 5, 6, 7, 8, 10, 16, 17, 18, 22, 24, 27, 29, 38, 39, 42, 44, 47, 48, 49, 51, 54, 56, 61],
  pack [1, 9, 11, 12, 15, 16, 18, 19, 20, 23, 26, 27, 29, 35, 38, 42, 43, 45, 51, 55, 56, 57, 58, 59, 60],
  pack [3, 8, 10, 11, 14, 20, 21, 22, 25, 28, 33, 36, 37, 39, 41, 44, 45, 48, 49, 53, 54, 56, 58, 59, 60],
  pack [1, 2, 3, 4, 7, 8, 9, 14, 18, 21, 24, 32, 34, 37, 38, 40, 42, 44, 47, 48, 49, 50, 55, 59, 60],
  pack [3, 4, 8, 9, 10, 12, 13, 14, 15, 19, 22, 23, 26, 30, 31, 35, 39, 44, 46, 48, 49, 54, 55, 59, 60]
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem published_cover : IsCover 27 (published.map members) := by
  apply certify <;> decide +kernel

/-- Increasing triples drawn from `people` that occur in none of the groups. -/
def missingOn (people : List Person) (groups : List Nat) : List (Person × Person × Person) :=
  people.flatMap fun a =>
    (people.filter (fun b => a < b)).flatMap fun b =>
      let seen := companions a b groups
      (people.filter fun c => b < c && !seen.testBit c.val).map fun c => (a, b, c)

theorem missingOn_spec (people : List Person) (groups : List Nat) (a b c : Person) :
    (a, b, c) ∈ missingOn people groups ↔
      a ∈ people ∧ b ∈ people ∧ c ∈ people ∧ a < b ∧ b < c ∧
      ¬ ∃ g ∈ groups, a ∈ members g ∧ b ∈ members g ∧ c ∈ members g := by
  simp only [missingOn, List.mem_flatMap, List.mem_map, List.mem_filter, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_true_eq, Prod.mk.injEq, ← companions_spec, Bool.eq_false_iff]
  constructor
  · rintro ⟨_, ha, _, ⟨hb, hab⟩, _, ⟨hc, hbc, h⟩, rfl, rfl, rfl⟩
    exact ⟨ha, hb, hc, hab, hbc, h⟩
  · rintro ⟨ha, hb, hc, hab, hbc, h⟩
    exact ⟨a, ha, b, ⟨hb, hab⟩, c, ⟨hc, hbc, h⟩, rfl, rfl, rfl⟩

theorem missingOn_nodup {people : List Person} (groups : List Nat) (H : people.Nodup) :
    (missingOn people groups).Nodup := by
  unfold missingOn
  apply List.pairwise_flatMap.mpr
  constructor
  · intro a _
    apply List.pairwise_flatMap.mpr
    constructor
    · intro b _
      apply List.pairwise_map.mpr
      exact (H.filter _).imp (fun h heq => h (congrArg (fun x => x.2.2) heq))
    · apply (H.filter _).imp
      intro x y h u hu v hv heq
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hu
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
      exact h (congrArg (fun t => t.2.1) heq)
  · apply H.imp
    intro x y h u hu v hv heq
    obtain ⟨_, _, hu⟩ := List.mem_flatMap.mp hu
    obtain ⟨_, _, hv⟩ := List.mem_flatMap.mp hv
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hu
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
    exact h (congrArg Prod.fst heq)

def missingTriples (groups : List Nat) := missingOn (List.finRange 61) groups

theorem missingTriples_spec (groups : List Nat) (a b c : Person) :
    (a, b, c) ∈ missingTriples groups ↔
      a < b ∧ b < c ∧ ¬ ∃ g ∈ groups, a ∈ members g ∧ b ∈ members g ∧ c ∈ members g := by
  simp [missingTriples, missingOn_spec, List.mem_finRange]

theorem missingTriples_nodup (groups : List Nat) : (missingTriples groups).Nodup :=
  missingOn_nodup groups (List.nodup_finRange 61)

/-- A 26-group candidate with 84 uncovered triples. -/
def candidate : List Nat := [
  pack [3, 4, 7, 12, 14, 18, 19, 20, 23, 26, 28, 31, 34, 35, 36, 39, 40, 46, 48, 49, 52, 53, 54, 56, 61],
  pack [1, 2, 7, 11, 14, 16, 25, 26, 27, 29, 30, 33, 34, 37, 39, 40, 41, 43, 44, 45, 47, 51, 55, 58, 61],
  pack [1, 2, 11, 12, 13, 15, 16, 19, 24, 25, 27, 30, 33, 34, 37, 38, 40, 43, 45, 46, 47, 51, 53, 58, 61],
  pack [5, 6, 8, 9, 10, 12, 17, 19, 21, 22, 29, 32, 34, 40, 41, 42, 44, 46, 50, 53, 55, 57, 59, 60, 61],
  pack [3, 4, 13, 15, 18, 20, 23, 24, 28, 29, 31, 34, 35, 36, 38, 40, 41, 44, 48, 49, 52, 54, 55, 56, 61],
  pack [1, 4, 8, 11, 16, 18, 23, 27, 30, 33, 34, 35, 37, 42, 43, 48, 50, 51, 52, 54, 56, 57, 58, 59, 60],
  pack [2, 4, 5, 6, 9, 10, 11, 17, 18, 21, 22, 23, 25, 32, 34, 35, 40, 45, 47, 48, 51, 52, 54, 56, 61],
  pack [1, 3, 5, 16, 17, 18, 20, 21, 22, 27, 28, 30, 31, 32, 33, 36, 37, 40, 43, 45, 48, 49, 54, 58, 61],
  pack [2, 3, 6, 8, 9, 10, 11, 18, 20, 25, 28, 31, 36, 40, 42, 47, 48, 49, 50, 51, 54, 57, 59, 60, 61],
  pack [5, 6, 7, 8, 9, 10, 13, 14, 15, 17, 21, 22, 24, 26, 32, 34, 38, 39, 40, 42, 50, 57, 59, 60, 61],
  pack [1, 4, 6, 8, 9, 10, 16, 23, 27, 30, 33, 35, 37, 40, 42, 43, 45, 50, 52, 56, 57, 58, 59, 60, 61],
  pack [3, 4, 6, 9, 10, 11, 12, 13, 19, 20, 23, 24, 26, 28, 31, 35, 36, 39, 41, 44, 45, 49, 51, 52, 56],
  pack [2, 4, 5, 12, 15, 17, 19, 26, 27, 29, 31, 32, 33, 36, 38, 39, 42, 43, 47, 49, 52, 55, 58, 59, 60],
  pack [1, 4, 8, 12, 15, 16, 19, 21, 22, 25, 26, 29, 30, 31, 34, 36, 37, 38, 39, 45, 49, 50, 52, 55, 57],
  pack [1, 2, 6, 7, 9, 10, 12, 14, 15, 16, 18, 19, 25, 27, 30, 33, 37, 38, 41, 43, 44, 47, 48, 54, 58],
  pack [5, 7, 8, 11, 12, 13, 14, 17, 18, 19, 21, 22, 24, 29, 32, 42, 45, 48, 50, 51, 54, 55, 57, 59, 60],
  pack [2, 3, 8, 12, 15, 19, 20, 21, 22, 23, 26, 27, 28, 29, 33, 35, 38, 39, 43, 47, 50, 55, 56, 57, 58],
  pack [1, 3, 5, 12, 15, 16, 17, 19, 20, 23, 25, 26, 28, 29, 30, 32, 35, 37, 38, 39, 42, 55, 56, 59, 60],
  pack [3, 4, 6, 7, 9, 10, 11, 14, 15, 20, 23, 28, 29, 31, 35, 36, 38, 45, 46, 49, 51, 52, 53, 55, 56],
  pack [3, 4, 7, 13, 14, 20, 21, 22, 24, 25, 27, 28, 33, 34, 41, 42, 43, 44, 45, 46, 52, 53, 58, 59, 60],
  pack [1, 2, 3, 4, 5, 7, 8, 13, 14, 16, 17, 20, 24, 28, 30, 32, 37, 41, 44, 46, 47, 50, 52, 53, 57],
  pack [1, 3, 5, 6, 9, 10, 11, 16, 17, 20, 21, 22, 27, 28, 30, 31, 32, 33, 34, 36, 37, 43, 49, 51, 58],
  pack [1, 2, 7, 13, 14, 16, 21, 22, 23, 24, 30, 31, 35, 36, 37, 41, 42, 44, 46, 47, 49, 53, 56, 59, 60],
  pack [5, 7, 8, 13, 14, 17, 23, 24, 25, 27, 31, 32, 33, 35, 36, 41, 43, 44, 46, 49, 50, 53, 56, 57, 58],
  pack [1, 2, 6, 9, 10, 13, 16, 18, 24, 25, 26, 27, 29, 30, 33, 37, 39, 43, 46, 47, 48, 53, 54, 55, 58],
  pack [5, 8, 11, 15, 17, 18, 21, 22, 26, 32, 38, 39, 41, 42, 44, 45, 46, 48, 50, 51, 53, 54, 57, 59, 60]
]

set_option maxRecDepth 10000 in
theorem candidate_sizes :
    candidate.length = 26 ∧ (candidate.map members).Nodup ∧
    candidate.all (fun g => (members g).length == 25) = true := by decide +kernel

/-- All three Cartesian products use the one-based labels of the displayed groups. -/
private def helperEdges : List (Nat × Nat) :=
  let cross (xs ys : List Nat) := xs.flatMap fun x => ys.map fun y => (x, y)
  cross [2, 47] [3, 8, 20, 28, 31, 36, 42, 49, 50, 57, 59, 60] ++
  cross [3, 20, 28] [8, 50, 57] ++ cross [31, 36, 49] [42, 59, 60]

private def labelsOf (t : Person × Person × Person) : List Nat :=
  [t.1.val+1, t.2.1.val+1, t.2.2.val+1]

/-- The exact 84 missing triples, written with one-based labels.
    Each of the 42 helper pairs gives one triple with 34 and one with 45. -/
def missingLabels : List (List Nat) :=
  ([34, 45] : List Nat).flatMap fun p => helperEdges.map fun (x,y) =>
    let a := min x y
    let b := max x y
    if p < a then [p, a, b] else if b < p then [a, b, p] else [a, p, b]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
theorem exact_missing_triples :
    ((missingTriples candidate).map labelsOf).Perm missingLabels := by decide +kernel


theorem candidate_missing_count : (missingTriples candidate).length = 84 := by
  simpa only [List.length_map] using exact_missing_triples.length_eq.trans (show missingLabels.length = 84 by decide)

private def touchesSpecial (xs : List Nat) : Bool := xs.any fun i => i == 34 || i == 45

/-- Every uncovered triple contains person 34 or 45 in the one-based list. -/
def touches34or45 (t : Person × Person × Person) : Bool := touchesSpecial (labelsOf t)

theorem candidate_missing_location : (missingTriples candidate).all touches34or45 = true := by
  change (missingTriples candidate).all (touchesSpecial ∘ labelsOf) = true
  rw [← List.all_map, exact_missing_triples.all_eq]
  decide

/-- Add people 34 and 45 to group 9 of the candidate, using one-based labels. -/
def enlarged := candidate.modify 8 (fun group => group ||| pack [34, 45])

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem two_extra_seats :
    enlarged.map (fun g => (members g).length) =
      List.replicate 8 25 ++ [27] ++ List.replicate 17 25 ∧
    ∀ a b c : Person, ∃ g ∈ enlarged, a ∈ members g ∧ b ∈ members g ∧ c ∈ members g := by
  constructor
  · decide +kernel
  · exact coversAll_sound (groups := enlarged) (by decide +kernel)

/-- After a deletion, only triples inside the deleted group can be missing. -/
def privateTriples (g : Nat) := missingOn (members g) (published.erase g)

theorem privateTriples_spec (g : Nat) (a b c : Person) :
    (a, b, c) ∈ privateTriples g ↔ (a, b, c) ∈ missingTriples (published.erase g) := by
  rw [privateTriples, missingOn_spec, missingTriples_spec]
  constructor
  · exact fun h => h.2.2.2
  · rintro ⟨hab, hbc, hmiss⟩
    obtain ⟨block, hmem, ha, hb, hc⟩ := published_cover.2.2.2 a b c
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hmem
    by_cases heq : h = g
    · subst h
      exact ⟨ha, hb, hc, hab, hbc, hmiss⟩
    · exact False.elim (hmiss ⟨h, (List.mem_erase_of_ne heq).mpr hh, ha, hb, hc⟩)

theorem privateTriples_nodup (g : Nat) : (privateTriples g).Nodup :=
  missingOn_nodup _ (List.Pairwise.filter _ (List.nodup_finRange 61))

/-- Uncovered triple count when the group at this zero-based position is removed. -/
def deletionCount (i : Nat) : Nat := (privateTriples published[i]!).length

private theorem cons_eq {α : Type} {a b : α} {as bs : List α} (ha : a = b) (hs : as = bs) :
    a :: as = b :: bs := by rw [ha, hs]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
/-- Direct deletions in the order of the published groups. -/
theorem published_deletion_counts : (List.range 27).map deletionCount =
    [952, 887, 956, 851, 716, 272, 871, 868, 892, 974, 858, 434, 948, 890, 866, 856, 834, 880, 944, 696, 911, 974, 956, 878, 840, 866, 974] := by
  repeat' refine cons_eq (by as_aux_lemma => decide +kernel) ?_
  rfl

set_option maxRecDepth 10000 in
/-- The best direct deletion is published group 6, with 272 triples uncovered. -/
theorem min_direct_deletion : ((List.range 27).map deletionCount).min? = some 272 ∧
    deletionCount 5 = 272 := by
  constructor
  · rw [published_deletion_counts]
    decide
  · exact congrArg (fun counts => counts[5]!) published_deletion_counts

theorem direct_deletion_lower_bound (i : Fin 27) : 272 ≤ deletionCount i.val :=
  (List.min?_eq_some_iff.mp min_direct_deletion.1).2 _ <|
    List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩

end Covering61
