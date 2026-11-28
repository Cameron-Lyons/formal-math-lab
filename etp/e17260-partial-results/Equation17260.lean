module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card

@[expose] public section

/-!
Equation 17260: structural consequences, without any associativity or cancellation
assumptions. This file does not claim to decide finite-model existence.
-/

namespace Equation17260

def Law {α : Type*} (op : α → α → α) : Prop :=
  ∀ x y z, x = op (op y x) (op z (op x (op z z)))

variable {α : Type*} {op : α → α → α} (h : Law op)

include h

/-- The two displayed intermediate values jointly determine `x`. -/
theorem recover {x x' y y' z : α}
    (hleft : op y x = op y' x')
    (hright : op x (op z z) = op x' (op z z)) : x = x' := by
  calc
    x = op (op y x) (op z (op x (op z z))) := h x y z
    _ = op (op y' x') (op z (op x' (op z z))) := by rw [hleft, hright]
    _ = x' := (h x' y' z).symm

/-- Distinct elements in a fiber of right multiplication by a square have
disjoint column images. -/
theorem columns_disjoint {x x' z : α} (hne : x ≠ x')
    (heq : op x (op z z) = op x' (op z z)) :
    Disjoint (Set.range (fun y => op y x)) (Set.range (fun y => op y x')) := by
  apply Set.disjoint_left.mpr
  rintro a ⟨y, hy⟩ ⟨y', hy'⟩
  exact hne (recover h (hy.trans hy'.symm) heq)

/-- On all right inputs which can produce a given output, multiplication
on the right by any square is injective. -/
theorem square_injective_on_inputs (a z : α) :
    Set.InjOn (fun x => op x (op z z)) {x | ∃ y, op y x = a} := by
  rintro x ⟨y, hy⟩ x' ⟨y', hy'⟩ heq
  exact recover h (hy.trans hy'.symm) heq

/-- Every element is a product. -/
theorem product_surjective : Function.Surjective (fun p : α × α => op p.1 p.2) := by
  intro x
  exact ⟨(op x x, op x (op x (op x x))), (h x x x).symm⟩

end Equation17260
