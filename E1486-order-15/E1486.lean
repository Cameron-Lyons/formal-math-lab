import Std

/-! Square-row facts used by the order-12, order-14 and order-15 proofs. Further results are in
`Simple.AdditionalResults`. -/

namespace E1486

def Law {S : Type} (op : S → S → S) : Prop :=
  ∀ x y z, op (op y x) (op x (op z z)) = x

/-- The neighbors of x are the results of multiplying x by a square. -/
def Row {S : Type} (op : S → S → S) (x b : S) : Prop :=
  ∃ z, op x (op z z) = b

/-- Add the diagonal arrows d(b) → b to a relation R. -/
def Pred {S : Type} (R : S → S → Prop) (d : S → S) (a b : S) : Prop :=
  R a b ∨ d b = a

variable {S : Type}

/-- The elements appearing on the diagonal. -/
def Square (op : S → S → S) (x : S) : Prop := ∃ z, op z z = x

/-- If q is a square and u = x⋆q, then x²⋆u = x. -/
theorem recover_source {op : S → S → S} (h : Law op) (x : S) {q : S}
    (hq : Square op q) : op (op x x) (op x q) = x := by
  obtain ⟨z, rfl⟩ := hq
  exact h x x z

/-- If q is a square and u = x⋆q, then u⋆q² = q. -/
theorem return_to_square {op : S → S → S} (h : Law op) (x : S) {q : S}
    (hq : Square op q) : op (op x q) (op q q) = q := by
  obtain ⟨z, rfl⟩ := hq
  exact h (op z z) x z

/-- If q is a square and u = x⋆q, then u²⋆q = u. -/
theorem recover_target {op : S → S → S} (h : Law op) (x : S) {q : S}
    (hq : Square op q) : op (op (op x q) (op x q)) q = op x q := by
  have recover := recover_source h (op x q) (show Square op (op q q) from ⟨q, rfl⟩)
  rwa [return_to_square h x hq] at recover

/-- On a → i → b, if b = i⋆q for a square q, then a⋆b = i. -/
theorem returnOnEdge {op : S → S → S} (h : Law op) {a i b : S}
    (hai : Pred (Row op) (fun x => op x x) a i) (hib : Row op i b) : op a b = i := by
  obtain ⟨z, rfl⟩ := hib
  -- Every first arrow a → i expresses a as t⋆i for some t.
  obtain ⟨t, ht⟩ : ∃ t, op t i = a := by
    rcases hai with ⟨w, rfl⟩ | rfl
    · exact ⟨op a a, recover_source h a ⟨w, rfl⟩⟩
    · exact ⟨i, rfl⟩
  rw [← ht]
  exact h i t z

theorem square_involution {op : S → S → S} (h : Law op) {x : S} (hx : Square op x) :
    op (op x x) (op x x) = x :=
  return_to_square h x hx

theorem square_edge {op : S → S → S} {x : S} (hx : Square op x) :
    Row op x (op x x) := by
  obtain ⟨z, hz⟩ := hx
  exact ⟨z, by rw [hz]⟩

end E1486
