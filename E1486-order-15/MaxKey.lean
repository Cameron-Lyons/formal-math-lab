import Std

/-! A nonempty family of objects with keys of one length has a member whose key is largest. -/

namespace E1486.Symmetry

local instance : Std.IsLinearOrder Bool where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  le_total := by decide

local instance : Std.LawfulOrderLT Bool where
  lt_iff := by decide

private theorem maximum_mem (x : List Bool) (l : List (List Bool)) :
    ∃ v ∈ x :: l, ∀ w ∈ x :: l, w ≤ v := by
  induction l generalizing x with
  | nil => exact ⟨x, by simp, by simp⟩
  | cons y ys ih =>
    obtain ⟨v, hv, hm⟩ := ih y
    rcases List.le_total x v with hx | hx
    · refine ⟨v, by simp [hv], ?_⟩
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hx
      · exact hm w hw
    · refine ⟨x, by simp, ?_⟩
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact Std.le_refl _
      · exact List.le_trans (hm w hw) hx

/-- All Boolean words of a fixed length. Used only in the existence proof for a maximum. -/
private def words : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (words n).map (false :: ·) ++ (words n).map (true :: ·)

private theorem mem_words (xs : List Bool) : xs ∈ words xs.length := by
  induction xs with
  | nil => simp [words]
  | cons b bs ih => cases b <;> simp [words, ih]

theorem exists_max_key {α : Type} (P : α → Prop) (f : α → List Bool) (n : Nat)
    (lengths : ∀ a, (f a).length = n) (start : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → f b ≤ f a := by
  classical
  let L := (words n).filter fun v => decide (∃ a, P a ∧ f a = v)
  have memL (a : α) (ha : P a) : f a ∈ L := by
    have hw := mem_words (f a)
    rw [lengths] at hw
    exact List.mem_filter.mpr ⟨hw, decide_eq_true ⟨a,ha,rfl⟩⟩
  obtain ⟨a₀,ha₀⟩ := start
  obtain ⟨v,hv,hm⟩ := maximum_mem (f a₀) L
  have ev : ∃ a, P a ∧ f a = v := by
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨a₀,ha₀,rfl⟩
    · exact of_decide_eq_true (List.mem_filter.mp hv).2
  obtain ⟨a,ha,rfl⟩ := ev
  exact ⟨a,ha,fun b hb => hm _ (List.mem_cons_of_mem _ (memL b hb))⟩

end E1486.Symmetry
