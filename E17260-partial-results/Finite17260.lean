import Equation17260
import Mathlib.Data.Fintype.BigOperators

namespace Equation17260

variable {α : Type*} {op : α → α → α}

/-- The set of entries in the column indexed by `x`. -/
abbrev Column (op : α → α → α) (x : α) := {a : α // ∃ y, op y x = a}

/-- The set of entries in the row indexed by `x`. -/
abbrev Row (op : α → α → α) (x : α) := {a : α // ∃ y, op x y = a}

noncomputable instance [Finite α] (x : α) : Fintype (Column op x) :=
  Fintype.ofFinite (Column op x)

noncomputable instance [Finite α] (x : α) : Fintype (Row op x) :=
  Fintype.ofFinite (Row op x)

/-- The column sizes obey a uniform inequality for every square column.
This is a necessary condition, not a proof of nonexistence. -/
theorem sum_column_card_le [Fintype α] (h : Law op) (z : α) :
    (∑ x, Fintype.card (Column op x)) ≤
      Fintype.card α * Fintype.card (Column op (op z z)) := by
  let f : (Σ x, Column op x) → α × Column op (op z z) :=
    fun p => (p.2.val, ⟨op p.1 (op z z), p.1, rfl⟩)
  have hf : Function.Injective f := by
    rintro ⟨x, a, y, hy⟩ ⟨x', a', y', hy'⟩ heq
    have ha : a = a' := congrArg Prod.fst heq
    have hq : op x (op z z) = op x' (op z z) :=
      congrArg (fun p => p.2.val) heq
    have hx : x = x' := recover h (hy.trans (ha.trans hy'.symm)) hq
    subst x'
    subst a'
    rfl
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_sigma, Fintype.card_prod] using hc

/-- Each row must have at least the square root of the size of the algebra. -/
theorem card_le_row_card_sq [Fintype α] (h : Law op) (z : α) :
    Fintype.card α ≤ Fintype.card (Row op z) * Fintype.card (Row op z) := by
  let f : α → Row op z × Row op z := fun x =>
    (⟨op z x, x, rfl⟩, ⟨op z (op x (op z z)), op x (op z z), rfl⟩)
  have hf : Function.Injective f := by
    intro x x' heq
    have h₁ : op z x = op z x' := congrArg (fun p => p.1.val) heq
    have h₂ : op z (op x (op z z)) = op z (op x' (op z z)) :=
      congrArg (fun p => p.2.val) heq
    calc
      x = op (op z x) (op z (op x (op z z))) := h x z z
      _ = op (op z x') (op z (op x' (op z z))) := by rw [h₁, h₂]
      _ = x' := (h x' z z).symm
  simpa only [Fintype.card_prod] using Fintype.card_le_of_injective f hf

end Equation17260
