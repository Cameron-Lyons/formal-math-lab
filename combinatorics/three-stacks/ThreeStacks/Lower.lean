import ThreeStacks.Model

namespace ThreeStacks

/-- Delete an arbitrary set of card labels from a legal stack schedule. -/
theorem Pass.filter {i s o : List Nat} (h : Pass i s o) (keep : Nat → Bool) :
    Pass (i.filter keep) (s.filter keep) (o.filter keep) := by
  induction h with
  | done => exact .done
  | @push x i s o _ ih =>
    cases e : keep x <;> simp [e] at ih ⊢
    · exact ih
    · exact .push ih
  | @pop x i s o _ ih =>
    cases e : keep x <;> simp [e] at ih ⊢
    · exact ih
    · exact .pop ih

/-- Apply the same restriction to all three passes, preserving their intermediate orders. -/
theorem SortsTo.filter {p q : List Nat} (h : SortsTo p q) (keep : Nat → Bool) :
    SortsTo (p.filter keep) (q.filter keep) := by
  obtain ⟨A, B, h₁, h₂, h₃⟩ := h
  exact ⟨A.filter keep, B.filter keep, h₁.filter keep, h₂.filter keep, h₃.filter keep⟩

/-- Any universal fixed-length result also covers every shorter deck. -/
theorem allShorterOf {m : Nat} (h : ∀ p, IsDeck m p → Sortable m p)
    (n : Nat) (hn : n ≤ m) (p : List Nat) (hp : IsDeck n p) : Sortable n p := by
  let extra := List.range' (1+n) (m-n)
  let keep := fun x : Nat => decide (x ≤ n)
  have joined : target n ++ extra = target m := by
    simp [target, extra, Nat.add_sub_of_le hn]
  have padded : IsDeck m (p ++ extra) := by
    change (p ++ extra).Perm (target m)
    rw [← joined]
    exact List.Perm.append_right _ hp
  have clean : ∀ l, IsDeck n l → l.filter keep = l := by
    intro l hl
    apply List.filter_eq_self.mpr
    intro x hx
    have hx' := (List.Perm.mem_iff hl).mp hx
    change x ∈ List.range' 1 n at hx'
    have hx'' := List.mem_range'_1.mp hx'
    exact decide_eq_true (by omega)
  have remove : extra.filter keep = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    have hx' := List.mem_range'_1.mp hx
    simp [keep]; omega
  have f := (SortsTo.filter (h _ padded) keep)
  rw [← joined, List.filter_append, List.filter_append, remove, clean p hp,
      clean _ (List.Perm.refl _)] at f
  simpa [Sortable] using f

theorem allShorter (h19 : ∀ p, IsDeck 19 p → Sortable 19 p) :
    ∀ n, n ≤ 19 → ∀ p, IsDeck n p → Sortable n p := allShorterOf h19

end ThreeStacks
