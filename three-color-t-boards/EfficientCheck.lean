import TBoards

/-!
A faster kernel-checkable certificate for validity. Sorting the 81 pattern
quadruples and comparing with their complete list avoids 81 separate scans.
Soundness is proved by a permutation theorem for a structurally recursive sort;
no property of an external sorting implementation or solver is assumed.
-/
namespace TBoards

/-- All ordered three-color patterns, in base-three order. -/
def orderedPatterns : List Pattern :=
  (List.range 3).flatMap fun a =>
  (List.range 3).flatMap fun l =>
  (List.range 3).flatMap fun m =>
  (List.range 3).map fun r => (a,l,m,r)

/-- Numeric key used only to order the actual pattern quadruples. -/
def patternKey (p : Pattern) : Nat :=
  27*p.1 + 9*p.2.1 + 3*p.2.2.1 + p.2.2.2

/-- Structurally recursive merge. Exhausting fuel concatenates the remaining
lists, so the permutation theorem does not require any fuel hypothesis. -/
def mergeFuel {α : Type} (le : α → α → Bool) : Nat → List α → List α → List α
  | 0, xs, ys => xs ++ ys
  | _+1, [], ys => ys
  | _+1, xs, [] => xs
  | n+1, x::xs, y::ys =>
    if le x y then x :: mergeFuel le n xs (y::ys)
    else y :: mergeFuel le n (x::xs) ys

theorem mergeFuel_perm {α : Type} (le : α → α → Bool)
    (n : Nat) (xs ys : List α) : (mergeFuel le n xs ys).Perm (xs ++ ys) := by
  induction n generalizing xs ys with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    cases xs with
    | nil => simp [mergeFuel]
    | cons x xs =>
      cases ys with
      | nil => simp [mergeFuel]
      | cons y ys =>
        simp only [mergeFuel]
        split
        · exact List.Perm.cons x (ih xs (y::ys))
        · exact List.perm_cons_append_cons y (ih (x::xs) ys)

/-- The recursive depth is explicit, keeping all evaluation inside the kernel's
structural recursor. Insufficient fuel preserves the list's multiset. -/
def sortFuel {α : Type} (le : α → α → Bool) : Nat → List α → List α
  | 0, xs => xs
  | n+1, xs =>
    if xs.length ≤ 1 then xs else
    let mid := xs.length / 2
    mergeFuel le xs.length (sortFuel le n (xs.take mid)) (sortFuel le n (xs.drop mid))

theorem sortFuel_perm {α : Type} (le : α → α → Bool) (n : Nat) (xs : List α) :
    (sortFuel le n xs).Perm xs := by
  induction n generalizing xs with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    simp only [sortFuel]
    split
    · exact List.Perm.refl _
    · have hm := mergeFuel_perm le xs.length
        (sortFuel le n (xs.take (xs.length / 2)))
        (sortFuel le n (xs.drop (xs.length / 2)))
      have hp := hm.trans ((ih _).append (ih _))
      simpa only [List.take_append_drop] using hp

/-- A pattern whose four coordinates are colors. -/
def ColorPattern (p : Pattern) : Prop :=
  p.1 < 3 ∧ p.2.1 < 3 ∧ p.2.2.1 < 3 ∧ p.2.2.2 < 3

theorem patternKey_injective {p q : Pattern}
    (hp : ColorPattern p) (hq : ColorPattern q) (he : patternKey p = patternKey q) :
    p = q := by
  rcases p with ⟨a,l,m,r⟩
  rcases q with ⟨a',l',m',r'⟩
  simp only [ColorPattern] at hp hq
  simp only [patternKey] at he
  have ha : a = a' := by omega
  have hl : l = l' := by omega
  have hm : m = m' := by omega
  have hr : r = r' := by omega
  simp_all

theorem WellFormed.pattern_colors {b : Board} (h : WellFormed b)
    {p : Pattern} (hp : p ∈ patterns b) : ColorPattern p := by
  change p ∈ placements.map (patternAt b) at hp
  obtain ⟨pos, hpos, rfl⟩ := List.mem_map.mp hp
  have hg := placement_bounds ((mem_placements pos).mp hpos)
  obtain ⟨_, _, _, _, ha⟩ := h.cell_is_entry pos.1 pos.2 hg.1 hg.2.1
  obtain ⟨_, _, _, _, hl⟩ := h.cell_is_entry (pos.1+1) pos.2 hg.2.2.1 hg.2.2.2.1
  obtain ⟨_, _, _, _, hm⟩ := h.cell_is_entry (pos.1+1) (pos.2+1) hg.2.2.1 hg.2.2.2.2.1
  obtain ⟨_, _, _, _, hr⟩ := h.cell_is_entry (pos.1+1) (pos.2+2) hg.2.2.1 hg.2.2.2.2.2
  exact ⟨ha, hl, hm, hr⟩

/-- Read neighboring cells once, instead of repeatedly indexing a row. -/
def scanRow : List Nat → List Nat → List Pattern
  | a::as, l::m::r::bs => (a,l,m,r) :: scanRow as (m::r::bs)
  | _, _ => []

theorem scanRow_eq (upper lower : List Nat) (hlen : lower.length = upper.length+2) :
    scanRow upper lower = (List.range upper.length).map (fun j =>
      (upper.getD j 0, lower.getD j 0, lower.getD (j+1) 0, lower.getD (j+2) 0)) := by
  induction upper generalizing lower with
  | nil => simp [scanRow]
  | cons a as ih =>
    cases lower with
    | nil => simp at hlen
    | cons l ls =>
      cases ls with
      | nil => simp at hlen
      | cons m ms =>
        cases ms with
        | nil => simp at hlen
        | cons r bs =>
          have ht : (m::r::bs).length = as.length+2 := by simp_all
          rw [scanRow, ih (m::r::bs) ht]
          simp [List.range_succ_eq_map, List.map_map, Function.comp_def,
            Nat.succ_eq_add_one]

def scanPatterns (b : Board) : List Pattern :=
  (List.range 9).flatMap fun r => scanRow (b.getD r []) (b.getD (r+1) [])

theorem WellFormed.scanPatterns_eq {b : Board} (h : WellFormed b) :
    scanPatterns b = patterns b := by
  simp only [scanPatterns, patterns, placements, List.map_flatMap, List.map_map]
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro r hr
  have hr9 := List.mem_range.mp hr
  have hu := h.2.1 r (List.mem_range.mpr (by omega))
  have hl := h.2.1 (r+1) (List.mem_range.mpr (by omega))
  rw [scanRow_eq _ _ (by omega), hu]
  rfl

def patternCodes (b : Board) : List Nat := (scanPatterns b).map patternKey

def sortedCodes (b : Board) : List Nat :=
  sortFuel (fun p q => decide (p ≤ q)) 7 (patternCodes b)

/-- An efficient sufficient condition for the original `Valid` predicate. -/
def FastValid (b : Board) : Prop :=
  WellFormed b ∧ sortedCodes b = List.range 81

instance (b : Board) : Decidable (FastValid b) := by
  unfold FastValid
  infer_instance

/-- The fast finite certificate proves the original mathematical specification. -/
theorem FastValid.valid {b : Board} (h : FastValid b) : Valid b := by
  refine ⟨h.1, ?_⟩
  intro a l m r
  let p : Pattern := (a.val,l.val,m.val,r.val)
  have hp : ColorPattern p := ⟨a.isLt, l.isLt, m.isLt, r.isLt⟩
  have hbound : patternKey p < 81 := by
    have := a.isLt; have := l.isLt; have := m.isLt; have := r.isLt
    simp only [p, patternKey]
    omega
  have hs : (sortedCodes b).Perm (patternCodes b) := sortFuel_perm _ _ _
  have hc := hs.count_eq (patternKey p)
  rw [h.2, List.count_range, ite_eq_left hbound] at hc
  have hm : (patternCodes b).count (patternKey p) = (patterns b).count p := by
    rw [patternCodes, h.1.scanPatterns_eq]
    simp only [List.count_eq_countP, List.countP_map]
    apply List.countP_congr
    intro q hq
    simp only [Function.comp_apply, beq_iff_eq]
    exact ⟨fun he => patternKey_injective (h.1.pattern_colors hq) hp he,
      fun he => congrArg patternKey he⟩
  exact hm.symm.trans hc.symm

/-- Batch certificates can share the same soundness theorem. -/
theorem fastValid_list_valid {bs : List Board} (h : ∀ b ∈ bs, FastValid b) :
    ∀ b ∈ bs, Valid b := fun b hb => (h b hb).valid

end TBoards
