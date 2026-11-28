import BoxFree.Basic

namespace BoxFree

/-- A choice of two distinct coordinates, in increasing order. -/
structure AxisPair (n : Nat) where
  lo : Fin n
  hi : Fin n
  lt : lo < hi

def pairs (n : Nat) : List (AxisPair n) :=
  (List.finRange n).flatMap fun i => (List.finRange n).filterMap fun j =>
    if h : i < j then some ⟨i, j, h⟩ else none

abbrev RowColor := AxisPair 6 × Bool
abbrev Slot := RowColor × AxisPair 7

def rowColors : List RowColor :=
  (pairs 6).flatMap fun p => [(p, false), (p, true)]

def slots : List Slot :=
  rowColors.flatMap fun p => (pairs 7).map fun q => (p, q)

private def agrees (p : RowColor) (column : Fin 6 → Bool) : Bool :=
  let (rows, color) := p
  column rows.lo == color && column rows.hi == color

def occupies (L : Layer) (s : Slot) : Bool :=
  let (p, cols) := s
  agrees p (fun i => L i cols.lo) && agrees p (fun i => L i cols.hi)

theorem occupies_iff (L : Layer) (rows : AxisPair 6) (cols : AxisPair 7) (color : Bool) :
    occupies L ((rows, color), cols) = true ↔ Rectangle L rows.lo rows.hi cols.lo cols.hi color := by
  simp [occupies, agrees, Rectangle, and_left_comm, and_assoc]

def rectangleCount (L : Layer) : Nat := slots.countP (occupies L)

private theorem by_patterns {n : Nat} {P : (Fin n → Bool) → Prop}
    (h : ∀ v : Vector Bool n, P (fun i => v[i.val])) (f : Fin n → Bool) : P f := by
  simpa using h (Vector.ofFn f)

private def sharedPairs (f : Fin 7 → Bool) := (pairs 7).countP fun p => f p.lo && f p.hi

/-- Any six entries contain at least six same-color pairs. -/
private theorem column_bound :
    ∀ f : Fin 6 → Bool, 6 ≤ rowColors.countP (fun p => agrees p f) := by
  apply by_patterns
  decide +kernel

/-- A set of k columns determines at least k − 1 pairs of columns. -/
private theorem pair_bound :
    ∀ f : Fin 7 → Bool, (List.finRange 7).countP f ≤ sharedPairs f + 1 := by
  apply by_patterns
  decide +kernel

theorem sum_mono (xs : List α) (f g : α → Nat) (h : ∀ x, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    exact Nat.add_le_add (h x) ih

private theorem sum_add (xs : List α) (f g : α → Nat) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

/-- The number of incidences can be counted in either order. -/
theorem double_count (xs : List α) (ys : List β) (p : α → β → Bool) :
    (xs.map fun x => ys.countP (p x)).sum = (ys.map fun y => xs.countP (fun x => p x y)).sum := by
  have count (q : β → Bool) : ys.countP q = (ys.map (fun y => if q y then 1 else 0)).sum := by
    induction ys <;> simp_all [List.countP_cons, Nat.add_comm]
  induction xs with
  | nil => simp [List.map_const', List.sum_replicate_nat]
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.countP_cons, sum_add, ih, count (p x), Nat.add_comm]

/-- Counting shared columns by columns gives at least 42. Counting them by colored
row pairs gives at most the number of rectangles plus 30. -/
theorem twelve_le (L : Layer) : 12 ≤ rectangleCount L := by
  let shared (j : Fin 7) (p : RowColor) := agrees p (fun i => L i j)
  have enough : 42 ≤ rectangleCount L + 30 := calc
    42 ≤ ((List.finRange 7).map fun j => rowColors.countP (shared j)).sum :=
      sum_mono (List.finRange 7) (fun _ => 6) _ (fun j => column_bound (fun i => L i j))
    _ = (rowColors.map fun p => (List.finRange 7).countP (fun j => shared j p)).sum :=
      double_count _ _ shared
    _ ≤ (rowColors.map fun p => sharedPairs (fun j => shared j p) + 1).sum :=
      sum_mono rowColors _ _ (fun p => pair_bound (fun j => shared j p))
    _ = rectangleCount L + 30 := by
      rw [sum_add]
      rw [show (rowColors.map fun _ => 1).sum = 30 by decide, Nat.add_right_cancel_iff]
      simp [rectangleCount, slots, List.countP_flatMap, Function.comp_def, sharedPairs, shared, occupies]
  omega

end BoxFree
