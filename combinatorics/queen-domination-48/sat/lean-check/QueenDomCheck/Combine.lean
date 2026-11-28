/-
From per-item results to a statement about a whole list.

The parallel driver hands the items of a list `l` to worker threads in an order and a distribution
that are not trusted.  Each worker returns, for the items it has settled, values of the subtype
`{x // P x}`: an item together with a proof of the property.  The driver puts them into a list of
slots, one per position of `l`.  `covers` then walks `l` and the slots in parallel and checks that
the `i`-th slot holds a proved item that is *equal* to the `i`-th item of `l`; if so, `P` holds for
every item of `l` (`forall_of_covers`).  Nothing about the scheduling has to be believed: a slot that
is empty, or filled with the result of another item, makes `covers` false.
-/
namespace QueenDomCheck

/-- Slot `i` holds a proved item equal to the `i`-th item of `l`, for every position of `l`. -/
def covers {α : Type} [DecidableEq α] (P : α → Prop) : List α → List (Option {x : α // P x}) → Bool
  | [], _ => true
  | x :: xs, some y :: slots => decide (y.val = x) && covers P xs slots
  | _ :: _, _ => false

theorem forall_of_covers {α : Type} [DecidableEq α] {P : α → Prop} :
    ∀ (l : List α) (slots : List (Option {x : α // P x})), covers P l slots = true → ∀ x ∈ l, P x
  | [], _, _ => by simp
  | x :: xs, some y :: slots, h => by
    simp only [covers, Bool.and_eq_true, decide_eq_true_eq] at h
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact h.1 ▸ y.property
    · exact forall_of_covers xs slots h.2 z hz
  | _ :: _, none :: _, h => by simp [covers] at h
  | _ :: _, [], h => by simp [covers] at h

/-- The combination step of the driver: a proof for the whole list, or nothing. -/
def combine {α : Type} [DecidableEq α] (P : α → Prop) (l : List α)
    (slots : List (Option {x : α // P x})) : Option (PLift (∀ x ∈ l, P x)) :=
  if h : covers P l slots = true then some ⟨forall_of_covers l slots h⟩ else none

end QueenDomCheck
