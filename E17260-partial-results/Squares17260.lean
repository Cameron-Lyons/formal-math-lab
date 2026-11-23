import Cancellation17260

namespace Equation17260

/-- A model whose square map is surjective is trivial, with no finiteness assumption. -/
theorem subsingleton_of_surjective_square {α : Type*} {op : α → α → α}
    (h : Law op) (hs : Function.Surjective (fun x => op x x)) : Subsingleton α := by
  classical
  let g : α → α := fun x => Classical.choose (hs x)
  have hg (x : α) : op (g x) (g x) = x := Classical.choose_spec (hs x)
  have gi : Function.Injective g := by
    intro x y hxy
    exact (hg x).symm.trans ((congrArg (fun t => op t t) hxy).trans (hg y))
  let T : α → α → α := fun x z => op (g z) (op x z)
  let P : α → α := fun x => op (g (g x)) x
  -- Rewrite the law using a square root of its third input.
  have recover (x y z : α) : op (op y x) (T x z) = x := by
    simpa only [T, hg] using (h x y (g z)).symm
  have root (x z : α) : op x (T (g x) z) = g x := by
    simpa only [hg] using recover (g x) (g x) z
  have tgg (x : α) : T (g x) (g x) = P x := by
    dsimp [T, P]
    rw [hg]
  have xp (x : α) : op x (P x) = g x := by
    simpa only [tgg] using root x (g x)
  have partner (x z : α) : op (g x) (op (g (T x z)) x) = P x := by
    have ht := recover (P x) x (T x z)
    have hx : op (P x) (T x z) = x := recover x (g (g x)) z
    change op (op x (P x)) (op (g (T x z)) (op (P x) (T x z))) = P x at ht
    rwa [xp, hx] at ht
  have root_decoder (x z : α) : g (T x z) = op (T x z) (P x) := by
    have ht := root (T x z) x
    change op (T x z) (op (g x) (op (g (T x z)) x)) = g (T x z) at ht
    rw [partner] at ht
    exact ht.symm
  -- This special decoder is the identity, because its square root is `g x`.
  have decoder (x : α) : T x (P x) = x := by
    apply gi
    calc
      g (T x (P x)) = op (T x (P x)) (P x) := root_decoder x (P x)
      _ = g x := by
        have ht := recover (g x) (g (P x)) (g x)
        rw [tgg] at ht
        simpa only [T, xp] using ht
  have r (x y : α) : op (op y x) x = x := by
    simpa only [decoder] using recover x y (P x)
  -- Applying this last identity twice gives idempotence.
  apply subsingleton_of_idempotent h
  intro x
  have ht := r x (op x x)
  rwa [r x x] at ht


/-- Any nontrivial model has an element which is not a square. -/
theorem square_not_surjective {α : Type*} [Nontrivial α] {op : α → α → α}
    (h : Law op) : ¬ Function.Surjective (fun x => op x x) := by
  intro hs
  exact not_subsingleton α (subsingleton_of_surjective_square h hs)

/-- A finite nontrivial model must have a collision in its square map. -/
theorem square_not_injective {α : Type*} [Finite α] [Nontrivial α]
    {op : α → α → α} (h : Law op) : ¬ Function.Injective (fun x => op x x) := by
  intro hi
  exact square_not_surjective h (Finite.surjective_of_injective hi)

theorem exists_square_collision {α : Type*} [Finite α] [Nontrivial α]
    {op : α → α → α} (h : Law op) : ∃ a b, a ≠ b ∧ op a a = op b b := by
  obtain ⟨a, b, heq, hne⟩ := Function.not_injective_iff.mp (square_not_injective h)
  exact ⟨a, b, hne, heq⟩

theorem exists_not_square {α : Type*} [Nontrivial α] {op : α → α → α}
    (h : Law op) : ∃ c, ∀ a, op a a ≠ c := by
  classical
  simpa only [Function.Surjective, not_forall, not_exists] using square_not_surjective h

end Equation17260
