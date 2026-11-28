import Std

/-! Two squares of each integer side from 1 through 21.
Coordinates denote the lower-left corners of half-open unit cells.

The theorems below use the integer-grid model. Its geometric justification
is as follows. A path avoiding tile vertices propagates the boundary
orientation across shared edge segments. A horizontal or vertical line
avoiding vertices then reaches each crossed edge after a sum of integer
tile widths, measured from the boundary of the rectangle. -/

namespace Squares42

abbrev Cell := Nat × Nat
abbrev Tile := Fin 42
abbrev Placement := Tile → Cell

/-- Indices 0 and 1 have side 1, indices 2 and 3 have side 2, and so on. -/
def side (i : Tile) : Nat := i.val / 2 + 1

def cells (o : Cell) (w h : Nat) : List Cell :=
  (List.range w).flatMap fun u => (List.range h).map fun v => (o.1 + u, o.2 + v)

def piece (p : Placement) (i : Tile) := cells (p i) (side i) (side i)

/-- Equality up to reordering retains multiplicities. Every board cell occurs exactly once. -/
def Tiles (p : Placement) (w h : Nat) : Prop :=
  ((List.finRange 42).flatMap (piece p)).Perm (cells (0, 0) w h)

theorem mem_cells {x y w h : Nat} {o : Cell} :
    (x,y) ∈ cells o w h ↔ o.1 ≤ x ∧ x < o.1+w ∧ o.2 ≤ y ∧ y < o.2+h := by
  simp only [cells, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨u, hu, v, hv, hx, hy⟩
    omega
  · rintro ⟨_, _, _, _⟩
    exact ⟨x-o.1, by omega, y-o.2, by omega, by omega, by omega⟩

private theorem len_cells (o : Cell) (w h : Nat) : (cells o w h).length = w*h := by
  simp [cells, List.map_const', List.sum_replicate_nat]

theorem area {p w h} (t : Tiles p w h) : w*h = 6622 := by
  have eq := t.length_eq
  simp only [List.length_flatMap, piece, len_cells] at eq
  exact eq.symm.trans (by decide)

theorem cells_nodup (o : Cell) (w h : Nat) : (cells o w h).Nodup := by
  simp only [cells, List.Nodup, List.pairwise_flatMap, List.pairwise_map]
  constructor
  · intro a _
    exact (List.nodup_range (n := h)).imp (by grind)
  · apply (List.nodup_range (n := w)).imp
    simp only [List.mem_map]
    grind

theorem inside {p w h} (t : Tiles p w h) (i : Tile) :
    (p i).1 + side i ≤ w ∧ (p i).2 + side i ≤ h := by
  have hs : 0 < side i := by simp [side]
  let c : Cell := ((p i).1 + side i - 1, (p i).2 + side i - 1)
  have hc : c ∈ piece p i := mem_cells.mpr (by omega)
  have hm := t.mem_iff.mp (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, hc⟩)
  have := mem_cells.mp hm
  simp only [Nat.zero_add] at this
  omega

theorem covered {p w h x y} (t : Tiles p w h) (hx : x < w) (hy : y < h) :
    ∃ i, (x,y) ∈ piece p i := by
  have hm : (x,y) ∈ cells (0,0) w h := mem_cells.mpr (by simp [hx,hy])
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp (t.mem_iff.mpr hm)
  exact ⟨i, hi⟩

theorem unique_tile {p w h c} (t : Tiles p w h) {i j : Tile}
    (hi : c ∈ piece p i) (hj : c ∈ piece p j) : i = j := by
  have nd := (t.nodup_iff).mpr (cells_nodup (0,0) w h)
  have pw := (List.pairwise_flatMap.mp nd).2
  have order (a b : Tile) (lt : a.val < b.val) :
      ∀ u ∈ piece p a, ∀ v ∈ piece p b, u ≠ v := by
    simpa using (List.pairwise_iff_getElem.mp pw a.val b.val (by simp) (by simp) lt)
  by_cases h₁ : i.val < j.val
  · exact False.elim (order i j h₁ c hi c hj rfl)
  by_cases h₂ : j.val < i.val
  · exact False.elim (order j i h₂ c hj c hi rfl)
  exact Fin.ext (by omega)

/-- Two half-open squares are disjoint if their projections separate on either axis. -/
def Apart (p : Placement) (i j : Tile) : Prop :=
  (p i).1 + side i ≤ (p j).1 ∨ (p j).1 + side j ≤ (p i).1 ∨
  (p i).2 + side i ≤ (p j).2 ∨ (p j).2 + side j ≤ (p i).2

instance {p i j} : Decidable (Apart p i j) := by unfold Apart; infer_instance

/-- A certificate gives the two origins for each size, in increasing order of side.
The checker uses the area, 42 bounding-box tests, and pairwise separation. -/
def check (p : Placement) (w h : Nat) : Bool :=
  decide (w * h = 6622) && (List.finRange 42).all fun i =>
    decide ((p i).1 + side i ≤ w ∧ (p i).2 + side i ≤ h) &&
      (List.finRange 42).all fun j => decide (i = j ∨ Apart p i j)

theorem check_iff_tiles {p w h} : check p w h = true ↔ Tiles p w h := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, forall_const]
  constructor
  · rintro ⟨ar, tests⟩
    let all := (List.finRange 42).flatMap (piece p)
    let board := cells (0,0) w h
    have nd : all.Nodup := by
      apply List.pairwise_flatMap.mpr
      constructor
      · exact fun i _ => cells_nodup _ _ _
      · apply (List.nodup_finRange 42).imp
        intro i j ij ⟨x,y⟩ hi c hj e
        obtain rfl := e
        have sep := ((tests i).2 j).resolve_left ij
        have := mem_cells.mp hi
        have := mem_cells.mp hj
        unfold Apart at sep
        omega
    have sub : all ⊆ board := by
      rintro ⟨x,y⟩ hm
      obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hm
      have := mem_cells.mp hi
      have := (tests i).1
      exact mem_cells.mpr (by simp only [Nat.zero_add]; omega)
    have eq : all.length = board.length := by
      simp only [all, board, List.length_flatMap, piece, len_cells, ar]
      decide
    apply (List.perm_ext_iff_of_nodup nd (cells_nodup ..)).mpr
    intro c
    refine ⟨fun hc => sub hc, fun hc => ?_⟩
    apply Decidable.byContradiction
    intro hmiss
    have longer : (c :: all).Nodup := List.nodup_cons.mpr ⟨hmiss, nd⟩
    have le := longer.length_le_of_subset (l₂ := board) (by simpa using And.intro hc sub)
    simp only [List.length_cons] at le
    omega
  · intro t
    refine ⟨area t, fun i => ⟨inside t i, fun j => ?_⟩⟩
    by_cases eq : i = j
    · exact Or.inl eq
    right
    apply Decidable.byContradiction
    intro hsep
    unfold Apart at hsep
    let x := max (p i).1 (p j).1
    let y := max (p i).2 (p j).2
    have pi : side i > 0 := by simp [side]
    have pj : side j > 0 := by simp [side]
    have hi : (x,y) ∈ piece p i := mem_cells.mpr (by dsimp [x,y]; omega)
    have hj : (x,y) ∈ piece p j := mem_cells.mpr (by dsimp [x,y]; omega)
    exact eq (unique_tile t hi hj)

private theorem three_units_impossible {a b c : Tile}
    (ha : side a = 1) (hb : side b = 1) (hc : side c = 1)
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) : False := by
  have hab : a.val ≠ b.val := fun e => ab (Fin.ext e)
  have hac : a.val ≠ c.val := fun e => ac (Fin.ext e)
  have hbc : b.val ≠ c.val := fun e => bc (Fin.ext e)
  simp only [side] at ha hb hc
  omega

/-- Three consecutive cells beside a 21-square already require three unit squares. -/
theorem no_width_22 (p : Placement) (h : Nat) : ¬ Tiles p 22 h := by
  intro t
  let big : Tile := 40
  have sz : side big = 21 := by decide
  have bd := inside t big
  rw [sz] at bd
  let x := if (p big).1 = 0 then 21 else 0
  let neighbor := if (p big).1 = 0 then 20 else 1
  have hx : x < 22 := by simp [x]; split <;> decide
  have strip (r : Nat) (hr : r < 21) :
      ∃ i, side i = 1 ∧ (p i).2 = (p big).2 + r := by
    let y := (p big).2 + r
    obtain ⟨i, hi⟩ := covered t hx (show y < h by dsimp [y]; omega)
    have bi := inside t i
    have ranges := mem_cells.mp hi
    have ext : i ≠ big := by
      intro e
      subst i
      rw [sz] at ranges
      dsimp [x] at ranges
      split at ranges <;> omega
    have one : side i = 1 := by
      apply Decidable.byContradiction
      intro hn
      have pos : 0 < side i := by simp [side]
      have hc₁ : (neighbor,y) ∈ piece p big := by
        apply mem_cells.mpr
        rw [sz]
        dsimp [neighbor, y]
        split <;> omega
      have hc₂ : (neighbor,y) ∈ piece p i := by
        apply mem_cells.mpr
        dsimp [neighbor, x] at *
        split <;> split at ranges <;> omega
      exact ext (unique_tile t hc₂ hc₁)
    exact ⟨i, one, by dsimp [y] at ranges; omega⟩
  obtain ⟨a, ha, ay⟩ := strip 0 (by decide)
  obtain ⟨b, hb, by'⟩ := strip 1 (by decide)
  obtain ⟨c, hc, cy⟩ := strip 2 (by decide)
  apply three_units_impossible ha hb hc <;> intro eq <;> subst_vars <;> omega

/-- Take the shorter dimension first. -/
theorem remaining_rectangles {p w h} (t : Tiles p w h) (le : w ≤ h) :
    (w = 43 ∧ h = 154) ∨ (w = 77 ∧ h = 86) := by
  have ar := area t
  have lower := (inside t (40 : Tile)).1
  change (p 40).1 + 21 ≤ w at lower
  have upper : w < 82 := by
    apply Decidable.byContradiction
    intro e
    have el : 82 ≤ w := by omega
    have := Nat.mul_le_mul el (Nat.le_trans el le)
    omega
  have divides : 6622 % w = 0 := by rw [← ar]; simp
  have finite : ∀ i : Fin 82, 21 ≤ i.val → 6622 % i.val = 0 →
      i.val = 22 ∨ i.val = 43 ∨ i.val = 77 := by decide
  rcases finite ⟨w, upper⟩ (show 21 ≤ w by omega) divides with e | e | e <;> change w = _ at e <;> subst w
  · exact False.elim (no_width_22 p h t)
  · left; omega
  · right; omega


/-- Tiles intersecting the half-open horizontal strip from height y to y+1. -/
def active (p : Placement) (y : Nat) : List Tile :=
  (List.finRange 42).filter (fun i => decide ((p i).2 ≤ y ∧ y < (p i).2 + side i))

private theorem count_row_range (o h y : Nat) :
    (List.range h).countP (fun v => o+v == y) =
      if o ≤ y ∧ y < o+h then 1 else 0 := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [List.range_succ, List.countP_append, ih]
    simp only [List.countP_cons, List.countP_nil, Nat.zero_add, beq_iff_eq]
    split <;> split <;> split <;> omega

private theorem count_row_cells (o : Cell) (w h y : Nat) :
    (cells o w h).countP (fun c => c.2 == y) =
      if o.2 ≤ y ∧ y < o.2+h then w else 0 := by
  simp only [cells, List.countP_flatMap, List.countP_map, Function.comp_def,
    count_row_range, List.map_const', List.length_range, List.sum_replicate_nat]
  split <;> simp

private theorem sum_filtered {α} (l : List α) (f : α → Nat) (b : α → Bool) :
    ((l.filter b).map f).sum = (l.map fun x => if b x then f x else 0).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => cases hx : b x <;> simp [hx, ih]

theorem row_width {p w h y} (t : Tiles p w h) (hy : y < h) :
    ((active p y).map side).sum = w := by
  have eq := t.countP_eq (p := fun c => c.2 == y)
  simp only [List.countP_flatMap, Function.comp_def, piece, count_row_cells] at eq
  simpa [active, sum_filtered, hy] using eq

private theorem width_bound (l : List Tile) : (l.map side).sum ≤ 21 * l.length := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have bound := i.isLt
    simp only [List.map_cons, List.sum_cons, List.length_cons, side] at *
    omega

private theorem sum_add_map {α} (l : List α) (f g : α → Nat) :
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]; omega

private theorem sum_exchange {α β} (l : List α) (k : List β) (f : α → β → Nat) :
    (l.map (fun a => (k.map (f a)).sum)).sum =
    (k.map (fun b => (l.map (fun a => f a b)).sum)).sum := by
  induction l with
  | nil => simp [List.map_const', List.sum_replicate_nat]
  | cons a l ih => simp only [List.map_cons, List.sum_cons, sum_add_map, ih]

private theorem rows_per_tile (n o s : Nat) :
    ((List.range n).map (fun y => if o ≤ y ∧ y < o+s then 1 else 0)).sum =
      min (n-o) s := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero, ih]
    split <;> omega

private theorem len_filtered {α} (l : List α) (b : α → Bool) :
    (l.filter b).length = (l.map fun i => if b i then 1 else 0).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => cases ha : b a <;> simp [ha, ih, Nat.add_comm]

theorem total_row_intersections {p w h} (t : Tiles p w h) :
    ((List.range h).map fun y => (active p y).length).sum = 462 := by
  simp only [active, len_filtered, decide_eq_true_eq]
  rw [sum_exchange]
  simp only [rows_per_tile]
  have eq : (List.finRange 42).map (fun i => min (h - (p i).2) (side i)) =
      (List.finRange 42).map side := by
    apply List.map_congr_left
    intro i _
    have := (inside t i).2
    omega
  rw [eq]
  decide

private theorem tight (l : List Nat) (f : Nat → Nat) (hl : ∀ y ∈ l, 3 ≤ f y) :
    3*l.length ≤ (l.map f).sum ∧
    (3*l.length = (l.map f).sum → ∀ y ∈ l, f y = 3) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := hl a List.mem_cons_self
    obtain ⟨le,eq⟩ := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons, List.sum_cons, List.length_cons, List.mem_cons]
    constructor
    · omega
    · intro e y hy
      rcases hy with rfl | hy
      · omega
      · exact eq (by omega) y hy

theorem row_three {p y} (t : Tiles p 43 154) (hy : y < 154) :
    (active p y).length = 3 := by
  have lower (z) (hz : z ∈ List.range 154) : 3 ≤ (active p z).length := by
    have := row_width t (List.mem_range.mp hz)
    have := width_bound (active p z)
    omega
  apply (tight (List.range 154) _ lower).2 _ y (List.mem_range.mpr hy)
  rw [total_row_intersections t, List.length_range]

end Squares42
