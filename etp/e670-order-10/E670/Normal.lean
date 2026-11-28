import E670.Basic

/-!
# A normal form for the first row

Every ten-element model can be renamed so that

* `0 ◇ y ≤ y + 1` for every `y`, and
* either `0 ◇ 0 ≠ 0` or every element is idempotent.

Names are exchanged two at a time.  First a non-idempotent element, if there is one, exchanges
names with `0`.  Then, for `k = 0, 1, 2, …` in turn, if `0 ◇ k` is larger than `k + 1` it
exchanges names with `k + 1`.  Both are larger than `k`, so the entries `0 ◇ y` with `y < k`,
which involve only names up to `k`, stay as they are.

The argument uses the law only in that renaming preserves it.  It is therefore stated for any
property of tables that renaming preserves (`exists_normal_of`), so that other laws can use it.
-/

namespace E670

/-- A ten-element magma. -/
abbrev Op := Fin 10 → Fin 10 → Fin 10

/-- Exchange `i` and `j`. -/
def swap (i j x : Fin 10) : Fin 10 := if x = i then j else if x = j then i else x

theorem swap_swap (i j x : Fin 10) : swap i j (swap i j x) = x := by
  unfold swap; split <;> split <;> simp_all

theorem swap_right (i j : Fin 10) : swap i j j = i := by
  unfold swap; split <;> simp_all

theorem swap_of_ne {i j x : Fin 10} (hi : x ≠ i) (hj : x ≠ j) : swap i j x = x := by
  simp [swap, hi, hj]

/-- The table after the elements are renamed by `s`, a map that is its own inverse. -/
def rename (s : Fin 10 → Fin 10) (op : Op) : Op := fun x y => s (op (s x) (s y))

theorem rename_law {s : Fin 10 → Fin 10} (hs : ∀ x, s (s x) = x) {op : Op} (h : Law op) :
    Law (rename s op) := by
  intro x y
  simp only [rename, hs]
  rw [h, hs]

theorem rename_idem {s : Fin 10 → Fin 10} (hs : ∀ x, s (s x) = x) {op : Op} {x : Fin 10} :
    rename s op x x = x ↔ op (s x) (s x) = s x :=
  ⟨fun h => by have := congrArg s h; rwa [rename, hs] at this, fun h => by rw [rename, h, hs]⟩

/-- The first row is in chain form. -/
def ChainRow (op : Op) : Prop := ∀ y, (op 0 y).val ≤ y.val + 1

/-- The normal form of a table with the property `P`, with the chain condition required in the
first `k` columns only. -/
def NormalTo (P : Op → Prop) (k : Nat) (op : Op) : Prop :=
  P op ∧ (op 0 0 = 0 → ∀ x, op x x = x) ∧ ∀ y : Fin 10, y.val < k → (op 0 y).val ≤ y.val + 1

variable {P : Op → Prop}

theorem exists_normalTo_zero
    (keep : ∀ (s : Fin 10 → Fin 10) (op : Op), (∀ x, s (s x) = x) → P op → P (rename s op))
    {op : Op} (h : P op) : ∃ op', NormalTo P 0 op' := by
  by_cases hex : ∃ a, op a a ≠ a
  · -- a non-idempotent element `a` exchanges names with `0`
    obtain ⟨a, ha⟩ := hex
    refine ⟨rename (swap a 0) op, keep _ _ (swap_swap a 0) h, fun h0 => ?_,
      fun _ hy => absurd hy (Nat.not_lt_zero _)⟩
    rw [rename_idem (swap_swap a 0), swap_right] at h0
    exact absurd h0 ha
  · exact ⟨op, h, fun _ x => Decidable.byContradiction fun hx => hex ⟨x, hx⟩,
      fun _ hy => absurd hy (Nat.not_lt_zero _)⟩

theorem exists_normalTo_succ
    (keep : ∀ (s : Fin 10 → Fin 10) (op : Op), (∀ x, s (s x) = x) → P op → P (rename s op))
    {op : Op} {k : Nat} (h : NormalTo P k op) : ∃ op', NormalTo P (k + 1) op' := by
  obtain ⟨law, side, chain⟩ := h
  by_cases hk : ∃ y : Fin 10, y.val = k ∧ k + 1 < (op 0 y).val
  · -- `0 ◇ k` exchanges names with `k + 1`; this leaves the names up to `k` alone
    obtain ⟨y, rfl, hy⟩ := hk
    obtain ⟨i, hi⟩ : ∃ i : Fin 10, i.val = y.val + 1 := ⟨⟨y.val + 1, by omega⟩, rfl⟩
    have hs := swap_swap i (op 0 y)
    have fix : ∀ x : Fin 10, x.val ≤ y.val → swap i (op 0 y) x = x := fun x hx =>
      swap_of_ne (by rintro rfl; omega) (by rintro rfl; omega)
    have fix0 := fix 0 (Nat.zero_le _)
    refine ⟨rename (swap i (op 0 y)) op, keep _ _ hs law, fun h0 x => ?_, fun z hz => ?_⟩
    · -- `0 ◇ 0 = 0` held before the exchange too, so every element was and is idempotent
      rw [rename_idem hs, fix0] at h0
      exact (rename_idem hs).mpr (side h0 _)
    · simp only [rename, fix0, fix z (by omega)]
      by_cases hzy : z.val < y.val
      · -- an earlier column: its entry is at most `k` and keeps its name
        have := chain z hzy
        rwa [fix _ (by omega)]
      · -- column `k`: its entry is now called `k + 1`
        obtain rfl : z = y := Fin.ext (by omega)
        rw [swap_right]
        omega
  · -- nothing to do
    refine ⟨op, law, side, fun y hy => ?_⟩
    by_cases hyk : y.val < k
    · exact chain y hyk
    · exact Nat.le_of_not_lt fun hlt => hk ⟨y, by omega, by omega⟩

/-- A table with a property that renaming preserves can be renamed into normal form. -/
theorem exists_normal_of
    (keep : ∀ (s : Fin 10 → Fin 10) (op : Op), (∀ x, s (s x) = x) → P op → P (rename s op))
    {op : Op} (h : P op) :
    ∃ op' : Op, P op' ∧ ChainRow op' ∧ (op' 0 0 = 0 → ∀ x, op' x x = x) := by
  have steps : ∀ k, ∃ op', NormalTo P k op' := by
    intro k
    induction k with
    | zero => exact exists_normalTo_zero keep h
    | succ k ih =>
      obtain ⟨op', h'⟩ := ih
      exact exists_normalTo_succ keep h'
  obtain ⟨op', law, side, chain⟩ := steps 10
  exact ⟨op', law, fun y => chain y y.isLt, side⟩

/-- Every model can be renamed into normal form. -/
theorem exists_normal {op : Op} (h : Law op) :
    ∃ op' : Op, Law op' ∧ ChainRow op' ∧ (op' 0 0 = 0 → ∀ x, op' x x = x) :=
  exists_normal_of (fun _ _ hs => rename_law hs) h

end E670
