import EfficientCheck

/-! Exact validity from modular occurrence counts. This uses the saturation
of 81 available placements by 81 required distinct patterns. -/
namespace TBoards.ExactParity

private theorem count_one_of_cover {α : Type} [DecidableEq α]
    (required actual : List α) (hn : required.Nodup)
    (hs : required ⊆ actual) (hl : required.length = actual.length)
    (a : α) (ha : a ∈ required) : actual.count a = 1 := by
  have ham : a ∈ actual := hs ha
  have hpos : 0 < actual.count a := List.count_pos_iff.mpr ham
  by_cases hne : actual.count a = 1
  · exact hne
  exfalso
  have htwo : 2 ≤ actual.count a := by omega
  have hs' : required ⊆ actual.erase a := by
    intro x hx
    by_cases hxa : x = a
    · subst x
      apply List.count_pos_iff.mp
      rw [List.count_erase_self]
      omega
    · exact (List.mem_erase_of_ne hxa).mpr (hs hx)
  have hshort := hn.length_le_of_subset hs'
  have he := List.length_erase_of_mem ham
  have hlength := List.length_pos_of_mem ham
  omega

private theorem ordered_length : orderedPatterns.length = 81 := by decide
private theorem ordered_nodup : orderedPatterns.Nodup := by decide

def AllPresent (b : Board) : Prop :=
  ∀ a l m r : Fin 3, (a.val,l.val,m.val,r.val) ∈ patterns b

def AllOdd (b : Board) : Prop :=
  ∀ a l m r : Fin 3, (patterns b).count (a.val,l.val,m.val,r.val) % 2 = 1

def AllCongruentOne (b : Board) (modulus : Nat) : Prop :=
  ∀ a l m r : Fin 3,
    (patterns b).count (a.val,l.val,m.val,r.val) % modulus = 1

theorem valid_iff_present (b : Board) :
    Valid b ↔ WellFormed b ∧ AllPresent b := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro a l m r
    apply List.count_pos_iff.mp
    rw [h.2 a l m r]
    decide
  · rintro ⟨hw,hp⟩
    have hs : orderedPatterns ⊆ patterns b := by
      intro p hmem
      rcases p with ⟨a,l,m,r⟩
      simp [orderedPatterns] at hmem
      obtain ⟨a',ha,l',hl,m',hm,r',hr,rfl,rfl,rfl,rfl⟩ := hmem
      exact hp ⟨a',ha⟩ ⟨l',hl⟩ ⟨m',hm⟩ ⟨r',hr⟩
    refine ⟨hw, ?_⟩
    intro a l m r
    apply count_one_of_cover orderedPatterns (patterns b) ordered_nodup hs
      (by rw [ordered_length, patterns_length])
    simp [orderedPatterns]
    exact ⟨a.val,a.isLt,l.val,l.isLt,m.val,m.isLt,r.val,r.isLt,rfl,rfl,rfl,rfl⟩

/-- Counts congruent to one are positive; saturation makes every count one.
Primality is unnecessary for this counting statement. -/
theorem valid_iff_congruent_one (b : Board) (modulus : Nat)
    (hm : 1 < modulus) :
    Valid b ↔ WellFormed b ∧ AllCongruentOne b modulus := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro a l m r
    rw [h.2 a l m r]
    exact Nat.mod_eq_of_lt hm
  · rintro ⟨hw,hc⟩
    apply (valid_iff_present b).mpr
    refine ⟨hw, ?_⟩
    intro a l m r
    apply List.count_pos_iff.mp
    have hcount := hc a l m r
    by_cases hz : (patterns b).count (a.val,l.val,m.val,r.val) = 0
    · simp [hz] at hcount
    · exact Nat.pos_of_ne_zero hz

/-- Odd nonnegative counts are positive; 81 positive counts in 81 slots are all one. -/
theorem valid_iff_odd (b : Board) :
    Valid b ↔ WellFormed b ∧ AllOdd b := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro a l m r
    rw [h.2 a l m r]
  · rintro ⟨hw,ho⟩
    apply (valid_iff_present b).mpr
    refine ⟨hw, ?_⟩
    intro a l m r
    apply List.count_pos_iff.mp
    have hm := ho a l m r
    omega

end TBoards.ExactParity

#print axioms TBoards.ExactParity.valid_iff_odd
#print axioms TBoards.ExactParity.valid_iff_congruent_one
