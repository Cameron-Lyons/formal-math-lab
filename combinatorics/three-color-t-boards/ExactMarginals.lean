import TBoards

/-! An exact triangular system for the 81 ternary pattern counts.
Sixteen binary-cube entries and 65 selected three-coordinate margins
determine all entries. This is an equivalence, not just a necessary check. -/
namespace TBoards.ExactMarginals

abbrev Counts := Fin 3 → Fin 3 → Fin 3 → Fin 3 → Nat

def embed (a : Fin 2) : Fin 3 := ⟨a.val, by have := a.isLt; omega⟩

def Uniform (f : Counts) : Prop := ∀ a b c d, f a b c d = 1

/-- 16 point conditions followed by 8+12+18+27 line-sum conditions. -/
def Reduced (f : Counts) : Prop :=
  (∀ a b c d : Fin 2, f (embed a) (embed b) (embed c) (embed d) = 1) ∧
  (∀ a b c : Fin 2,
    f (embed a) (embed b) (embed c) 0 +
    f (embed a) (embed b) (embed c) 1 +
    f (embed a) (embed b) (embed c) 2 = 3) ∧
  (∀ a b : Fin 2, ∀ d : Fin 3,
    f (embed a) (embed b) 0 d + f (embed a) (embed b) 1 d +
    f (embed a) (embed b) 2 d = 3) ∧
  (∀ a : Fin 2, ∀ c d : Fin 3,
    f (embed a) 0 c d + f (embed a) 1 c d + f (embed a) 2 c d = 3) ∧
  (∀ b c d : Fin 3, f 0 b c d + f 1 b c d + f 2 b c d = 3)

private theorem extend (f : Fin 3 → Nat) (h0 : f 0 = 1) (h1 : f 1 = 1)
    (hs : f 0 + f 1 + f 2 = 3) : ∀ a, f a = 1 := by
  have h2 : f 2 = 1 := by omega
  intro a
  have ha : a = 0 ∨ a = 1 ∨ a = 2 := by have := a.isLt; omega
  rcases ha with rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2

theorem reduced_iff_uniform (f : Counts) : Reduced f ↔ Uniform f := by
  constructor
  · rintro ⟨base,last,third,second,first⟩
    have hd (a b c : Fin 2) (d : Fin 3) :
        f (embed a) (embed b) (embed c) d = 1 := by
      exact extend (f (embed a) (embed b) (embed c))
        (base a b c 0) (base a b c 1) (last a b c) d
    have hc (a b : Fin 2) (c d : Fin 3) : f (embed a) (embed b) c d = 1 := by
      exact extend (fun c => f (embed a) (embed b) c d)
        (hd a b 0 d) (hd a b 1 d) (third a b d) c
    have hb (a : Fin 2) (b c d : Fin 3) : f (embed a) b c d = 1 := by
      exact extend (fun b => f (embed a) b c d)
        (hc a 0 c d) (hc a 1 c d) (second a c d) b
    intro a b c d
    exact extend (fun a => f a b c d) (hb 0 b c d) (hb 1 b c d) (first b c d) a
  · intro h
    unfold Reduced
    exact ⟨fun a b c d => h _ _ _ _,
      fun a b c => by rw [h, h, h],
      fun a b d => by rw [h, h, h],
      fun a c d => by rw [h, h, h],
      fun b c d => by rw [h, h, h]⟩

def counts (b : Board) : Counts := fun a l m r =>
  (patterns b).count (a.val,l.val,m.val,r.val)

/-- The reduced count equations characterize the original validity predicate. -/
theorem valid_iff_reduced (b : Board) :
    Valid b ↔ WellFormed b ∧ Reduced (counts b) := by
  constructor
  · intro h
    exact ⟨h.1, (reduced_iff_uniform _).mpr h.2⟩
  · rintro ⟨hw,hr⟩
    exact ⟨hw, (reduced_iff_uniform _).mp hr⟩

end TBoards.ExactMarginals

#print axioms TBoards.ExactMarginals.valid_iff_reduced
