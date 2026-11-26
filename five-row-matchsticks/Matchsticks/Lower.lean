import Matchsticks.Geometry

/-! # Direct lower bound via dual-graph components and L-trominoes

For a `5 × n` board with no intact rectangle, form the dual graph on `5n + 1`
vertices (vertex `0` for the exterior, and `1 + 5c + r` for cell `(r, c)`),
adding one edge for each erased stick:

1. Adding `e` edges leaves at least `5n + 1 - e` connected components, so
   `e ≥ 5n - t` where `t` is the number of interior components (those not
   containing vertex `0`).
2. Any union of interior components has an intact boundary and therefore cannot
   be a rectangle. Hence at least one cell joins the exterior, every interior
   component has at least three cells (and none can exist at width `1`), giving
   `3t ≤ 5n - 1` and `3e ≥ 10n + 1`.
3. When `n = 3k + 2`, equality `e = 10k + 7` forces `t = 5k + 3`, exactly one
   exterior cell, and every interior component to be a 3-cell L-tromino.
   An end column avoiding the exterior cell has 5 cells, each covered by an L
   meeting it in 1 or 2 cells; since 5 is odd, some L meets it in a single cell.
   Its turn forces the adjacent end-column cell's L to cover 2 cells of the end
   column and turn the same way, so the two Ls form an intact `3 × 2` rectangle. -/
namespace Matchsticks.LowerProof

/-! ## 1. Finite list helpers -/

private theorem filter_le_of_imp {xs : List Nat} {p q : Nat → Bool}
    (h : ∀ x ∈ xs, p x = true → q x = true) :
    (xs.filter p).length ≤ (xs.filter q).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have ih' := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    simp only [List.filter_cons]
    cases hp : p x
    · cases q x <;> simp <;> omega
    · simp [h x List.mem_cons_self hp]; omega

private theorem filter_le_succ {xs : List Nat} (hnd : xs.Nodup) {p q : Nat → Bool} {a : Nat}
    (h : ∀ x ∈ xs, p x = true → q x = true ∨ x = a) :
    (xs.filter p).length ≤ (xs.filter q).length + 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
    by_cases hxa : x = a
    · subst hxa
      have hsub := filter_le_of_imp (xs := xs) (p := p) (q := q) fun y hy hp =>
        (h y (List.mem_cons_of_mem _ hy) hp).resolve_right (fun hyx => hx (hyx ▸ hy))
      simp only [List.filter_cons]
      cases p x <;> cases q x <;> simp <;> omega
    · have ih' := ih hnd' fun y hy => h y (List.mem_cons_of_mem _ hy)
      simp only [List.filter_cons]
      cases hp : p x
      · cases q x <;> simp <;> omega
      · have hq : q x = true := (h x List.mem_cons_self hp).resolve_right hxa
        simp [hq]; omega

private theorem sum_map_add (ys : List Nat) (f g : Nat → Nat) :
    (ys.map (fun r => f r + g r)).sum = (ys.map f).sum + (ys.map g).sum := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp [ih]; omega

private theorem sum_indicator {ys : List Nat} (hnd : ys.Nodup) {a : Nat} (ha : a ∈ ys) :
    (ys.map (fun r => if a = r then 1 else 0)).sum = 1 := by
  induction ys with
  | nil => cases ha
  | cons y ys ih =>
    obtain ⟨hy, hnd'⟩ := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp ha with rfl | hmem
    · have h0 : ∀ zs : List Nat, a ∉ zs → (zs.map (fun r => if a = r then 1 else 0)).sum = 0 := by
        intro zs hnot
        induction zs with
        | nil => rfl
        | cons z zs ihz =>
          have hne : a ≠ z := fun h => hnot (h ▸ List.mem_cons_self)
          simp [hne, ihz fun h => hnot (List.mem_cons_of_mem _ h)]
      simp [h0 ys hy]
    · have hne : a ≠ y := fun h => hy (h ▸ hmem)
      simp [hne, ih hnd' hmem]

private theorem sum_filter_partition {xs rs : List Nat} (f : Nat → Nat) (hnd : rs.Nodup)
    (hmem : ∀ x ∈ xs, f x ∈ rs) :
    (rs.map (fun r => (xs.filter (fun x => decide (f x = r))).length)).sum = xs.length := by
  induction xs with
  | nil =>
    have h0 : ∀ ys : List Nat, (ys.map (fun _ => 0)).sum = 0 := by
      intro ys; induction ys with
      | nil => rfl
      | cons _ ys ih => simp [ih]
    simpa using h0 rs
  | cons x xs ih =>
    have ih' := ih fun y hy => hmem y (List.mem_cons_of_mem _ hy)
    have hrew : rs.map (fun r => ((x :: xs).filter (fun y => decide (f y = r))).length) =
        rs.map (fun r => (if f x = r then 1 else 0) +
          (xs.filter (fun y => decide (f y = r))).length) := by
      apply List.map_congr_left
      intro r _
      simp only [List.filter_cons]
      by_cases hxr : f x = r
      · simp [hxr]; omega
      · simp [hxr]
    rw [hrew, sum_map_add, sum_indicator hnd (hmem x List.mem_cons_self), ih']
    simp [Nat.add_comm]

private theorem sum_ge_mul {xs : List Nat} {f : Nat → Nat} {k : Nat}
    (h : ∀ x ∈ xs, k ≤ f x) : k * xs.length ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ih' := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.mul_succ]
    omega

private theorem all_eq_of_sum_le {xs : List Nat} {f : Nat → Nat} {k : Nat}
    (hge : ∀ x ∈ xs, k ≤ f x) (hle : (xs.map f).sum ≤ k * xs.length) :
    ∀ x ∈ xs, f x = k := by
  induction xs with
  | nil => intro x hx; cases hx
  | cons x xs ih =>
    have hx := hge x List.mem_cons_self
    have hge' : ∀ y ∈ xs, k ≤ f y := fun y hy => hge y (List.mem_cons_of_mem _ hy)
    have hrest := sum_ge_mul hge'
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.mul_succ] at hle
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hmem
    · omega
    · exact ih hge' (by omega) y hmem

private theorem filter_ne_split {rs : List Nat} (hnd : rs.Nodup) {a : Nat} (ha : a ∈ rs)
    (g : Nat → Nat) :
    rs.length = (rs.filter (· != a)).length + 1 ∧
      (rs.map g).sum = g a + ((rs.filter (· != a)).map g).sum := by
  induction rs with
  | nil => cases ha
  | cons x xs ih =>
    obtain ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp ha with rfl | hmem
    · have hkeep : xs.filter (· != a) = xs :=
        List.filter_eq_self.mpr fun y hy => by simp [show y ≠ a from fun h => hx (h ▸ hy)]
      simp [hkeep]
    · have hne : x ≠ a := fun h => hx (h ▸ hmem)
      obtain ⟨hlen, hsum⟩ := ih hnd' hmem
      simp [bne_iff_ne, hne, hlen, hsum]
      omega

private theorem length_ge_two_of_mem {xs : List Nat} (hnd : xs.Nodup) {a b : Nat}
    (ha : a ∈ xs) (hb : b ∈ xs) (hab : a ≠ b) : 2 ≤ xs.length := by
  obtain ⟨hlen, _⟩ := filter_ne_split hnd ha (fun _ => 0)
  have hmem : b ∈ xs.filter (· != a) := List.mem_filter.mpr ⟨hb, by simp [hab.symm]⟩
  have hpos : 0 < (xs.filter (· != a)).length := List.length_pos_of_mem hmem
  omega

/-! ## 2. Component labeling by folding over edges -/

private def comp : List (Nat × Nat) → Nat → Nat
  | [], v => v
  | (u, w) :: es, v =>
      let f := comp es
      if f v = f u then f w else f v

private theorem comp_idem (es : List (Nat × Nat)) (v : Nat) :
    comp es (comp es v) = comp es v := by
  induction es generalizing v with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨u, w⟩
    simp only [comp]
    by_cases hvu : comp es v = comp es u
    · simp only [hvu, ↓reduceIte, ih w]
      by_cases hwu : comp es w = comp es u <;> simp [hwu]
    · simp only [hvu, ↓reduceIte, ih v]

private theorem comp_lt {V : Nat} (es : List (Nat × Nat))
    (he : ∀ e ∈ es, e.1 < V ∧ e.2 < V) {v : Nat} (hv : v < V) :
    comp es v < V := by
  induction es generalizing v with
  | nil => exact hv
  | cons e es ih =>
    rcases e with ⟨u, w⟩
    have hw : w < V := (he (u, w) List.mem_cons_self).2
    have he' : ∀ e' ∈ es, e'.1 < V ∧ e'.2 < V := fun e' h => he e' (List.mem_cons_of_mem _ h)
    simp only [comp]
    split
    · exact ih he' hw
    · exact ih he' hv

private theorem comp_edge {es : List (Nat × Nat)} {u w : Nat} (h : (u, w) ∈ es) :
    comp es u = comp es w := by
  induction es with
  | nil => cases h
  | cons e es ih =>
    rcases e with ⟨a, b⟩
    simp only [comp]
    rcases List.mem_cons.mp h with heq | hmem
    · cases heq
      by_cases hwu : comp es w = comp es u <;> simp [hwu]
    · rw [ih hmem]

private inductive Reach (es : List (Nat × Nat)) : Nat → Nat → Prop where
  | refl (a : Nat) : Reach es a a
  | step {a b c : Nat} : ((a, b) ∈ es ∨ (b, a) ∈ es) → Reach es b c → Reach es a c

private theorem Reach.trans {es : List (Nat × Nat)} {a b c : Nat}
    (h1 : Reach es a b) (h2 : Reach es b c) : Reach es a c := by
  induction h1 with
  | refl _ => exact h2
  | step e _ ih => exact .step e (ih h2)

private theorem Reach.cons {es : List (Nat × Nat)} {e : Nat × Nat} {a b : Nat}
    (h : Reach es a b) : Reach (e :: es) a b := by
  induction h with
  | refl a => exact .refl a
  | step he _ ih =>
    exact .step (he.imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _)) ih

private theorem comp_reach (es : List (Nat × Nat)) {a b : Nat} (h : comp es a = comp es b) :
    Reach es a b := by
  induction es generalizing a b with
  | nil =>
    simp only [comp] at h
    exact h ▸ .refl a
  | cons e es ih =>
    rcases e with ⟨u, w⟩
    simp only [comp] at h
    by_cases ha : comp es a = comp es u <;> by_cases hb : comp es b = comp es u
    · exact (ih (ha.trans hb.symm)).cons
    · simp only [ha, hb, ↓reduceIte] at h
      exact ((ih ha).cons.trans (Reach.step (Or.inl List.mem_cons_self) (Reach.refl w))).trans
        (ih h).cons
    · simp only [ha, hb, ↓reduceIte] at h
      exact (ih h).cons.trans
        ((Reach.step (Or.inr List.mem_cons_self) (Reach.refl u)).trans (ih hb.symm).cons)
    · simp only [ha, hb, ↓reduceIte] at h
      exact (ih h).cons

private def roots (f : Nat → Nat) (V : Nat) : List Nat :=
  (List.range V).filter (fun v => decide (f v = v))

private theorem roots_add_edges (V : Nat) (es : List (Nat × Nat)) :
    V ≤ (roots (comp es) V).length + es.length := by
  induction es with
  | nil =>
    have h : (List.range V).filter (fun _ => true) = List.range V :=
      List.filter_eq_self.mpr (by simp)
    simp [roots, comp, h]
  | cons e es ih =>
    rcases e with ⟨u, w⟩
    have hstep : (roots (comp es) V).length ≤ (roots (comp ((u, w) :: es)) V).length + 1 := by
      apply filter_le_succ List.nodup_range (a := comp es u)
      intro x _ hx
      have hfx : comp es x = x := of_decide_eq_true hx
      by_cases hxu : x = comp es u
      · exact Or.inr hxu
      · left; simp only [comp, hfx, hxu, ↓reduceIte, decide_eq_true_eq]
    simp only [List.length_cons]
    omega

/-! ## 3. Dual graph of a five-row board -/

private def cellId (r c : Nat) : Nat := 1 + 5 * c + r
private def rowOf (v : Nat) : Nat := (v - 1) % 5
private def colOf (v : Nat) : Nat := (v - 1) / 5

private theorem rowOf_cellId {r c : Nat} (hr : r < 5) : rowOf (cellId r c) = r := by
  simp only [rowOf, cellId]; omega

private theorem colOf_cellId {r c : Nat} (hr : r < 5) : colOf (cellId r c) = c := by
  simp only [colOf, cellId]; omega

private theorem cellId_row_col {v : Nat} (hv : 0 < v) : cellId (rowOf v) (colOf v) = v := by
  simp only [cellId, rowOf, colOf]; omega

private theorem cellId_lt {r c n : Nat} (hr : r < 5) (hc : c < n) : cellId r c < 5 * n + 1 := by
  simp only [cellId]; omega

private theorem cellId_pos (r c : Nat) : 0 < cellId r c := by
  simp only [cellId]; omega

private def vEdge (n x r : Nat) : Nat × Nat :=
  if x = 0 then (0, cellId r 0)
  else if x = n then (cellId r (n - 1), 0)
  else (cellId r (x - 1), cellId r x)

private def hEdge (c r : Nat) : Nat × Nat :=
  if r = 0 then (0, cellId 0 c)
  else if r = 5 then (cellId 4 c, 0)
  else (cellId (r - 1) c, cellId r c)

private def vColEdges (n x mask : Nat) : List (Nat × Nat) :=
  ((List.range 5).filter (fun r => !mask.testBit r)).map (vEdge n x)

private def hColEdges (c mask : Nat) : List (Nat × Nat) :=
  ((List.range 6).filter (fun r => !mask.testBit r)).map (hEdge c)

private def boardEdges (b : Board) : List (Nat × Nat) :=
  ((List.range (b.width + 1)).flatMap (fun x => vColEdges b.width x (b.verticalAt x))) ++
  ((List.range b.width).flatMap (fun c => hColEdges c (b.horizontalAt c)))

private def vCostSum (b : Board) : Nat :=
  ((List.range (b.width + 1)).map fun x =>
    ((List.range 5).filter fun r => !(b.verticalAt x).testBit r).length).sum

private def hCostSum (b : Board) : Nat :=
  ((List.range b.width).map fun c =>
    ((List.range 6).filter fun r => !(b.horizontalAt c).testBit r).length).sum

private theorem costSum_eq_cost (b : Board) : vCostSum b + hCostSum b = b.cost := by
  induction b with
  | left v =>
    simp [vCostSum, hCostSum, Board.width, Board.cost, Board.verticalAt, vCost]
  | snoc b h v ih =>
    have hv : vCostSum (b.snoc h v) = vCostSum b + vCost v := by
      unfold vCostSum
      change ((List.range (b.width + 1 + 1)).map _).sum = _
      rw [List.range_succ (n := b.width + 1), List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton]
      have heq : (List.range (b.width + 1)).map (fun x =>
          ((List.range 5).filter fun r => !((b.snoc h v).verticalAt x).testBit r).length) =
          (List.range (b.width + 1)).map (fun x =>
          ((List.range 5).filter fun r => !(b.verticalAt x).testBit r).length) := by
        apply List.map_congr_left
        intro x hx
        have hlt : x < b.width + 1 := List.mem_range.mp hx
        simp [Board.verticalAt, show x ≠ b.width + 1 by omega]
      rw [heq]; simp [Board.verticalAt, vCost]
    have hh : hCostSum (b.snoc h v) = hCostSum b + hCost h := by
      unfold hCostSum
      change ((List.range (b.width + 1)).map _).sum = _
      rw [List.range_succ (n := b.width), List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton]
      have heq : (List.range b.width).map (fun c =>
          ((List.range 6).filter fun r => !((b.snoc h v).horizontalAt c).testBit r).length) =
          (List.range b.width).map (fun c =>
          ((List.range 6).filter fun r => !(b.horizontalAt c).testBit r).length) := by
        apply List.map_congr_left
        intro c hc
        have hlt : c < b.width := List.mem_range.mp hc
        simp [Board.horizontalAt, show c ≠ b.width by omega]
      rw [heq]; simp [Board.horizontalAt, hCost]
    rw [hv, hh]; simp only [Board.cost]; omega

private theorem boardEdges_length (b : Board) : (boardEdges b).length = b.cost := by
  have hflat : (boardEdges b).length = vCostSum b + hCostSum b := by
    simp [boardEdges, vColEdges, hColEdges, vCostSum, hCostSum, List.length_flatMap]
  rw [hflat, costSum_eq_cost]

private def gridAdj (u w : Nat) : Prop :=
  (rowOf u = rowOf w ∧ (colOf u + 1 = colOf w ∨ colOf w + 1 = colOf u)) ∨
  (colOf u = colOf w ∧ (rowOf u + 1 = rowOf w ∨ rowOf w + 1 = rowOf u))

private theorem gridAdj_symm {u w : Nat} (h : gridAdj u w) : gridAdj w u := by
  rcases h with ⟨hr, hc | hc⟩ | ⟨hc, hr | hr⟩
  · exact Or.inl ⟨hr.symm, Or.inr hc⟩
  · exact Or.inl ⟨hr.symm, Or.inl hc⟩
  · exact Or.inr ⟨hc.symm, Or.inr hr⟩
  · exact Or.inr ⟨hc.symm, Or.inl hr⟩

private theorem gridAdj_irrefl (u : Nat) : ¬ gridAdj u u := by
  rintro (⟨_, h | h⟩ | ⟨_, h | h⟩) <;> omega

private theorem boardEdges_prop {b : Board} (hn : 0 < b.width) {e : Nat × Nat}
    (he : e ∈ boardEdges b) :
    (e.1 < 5 * b.width + 1 ∧ e.2 < 5 * b.width + 1) ∧
    (e.1 ≠ 0 → e.2 ≠ 0 → gridAdj e.1 e.2) := by
  simp only [boardEdges, List.mem_append, List.mem_flatMap, List.mem_range,
    vColEdges, hColEdges, List.mem_map, List.mem_filter] at he
  rcases he with ⟨x, hx, r, ⟨hr, _⟩, rfl⟩ | ⟨c, hc, r, ⟨hr, _⟩, rfl⟩
  · unfold vEdge
    split
    · exact ⟨⟨by omega, cellId_lt hr hn⟩, fun h0 _ => False.elim (h0 rfl)⟩
    · split
      · exact ⟨⟨cellId_lt hr (by omega), by omega⟩, fun _ h0 => False.elim (h0 rfl)⟩
      · refine ⟨⟨cellId_lt hr (by omega), cellId_lt hr (by omega)⟩, fun _ _ => Or.inl ?_⟩
        exact ⟨by simp only [rowOf_cellId hr], by simp only [colOf_cellId hr]; left; omega⟩
  · unfold hEdge
    split
    · exact ⟨⟨by omega, cellId_lt (by omega) hc⟩, fun h0 _ => False.elim (h0 rfl)⟩
    · split
      · exact ⟨⟨cellId_lt (by omega) hc, by omega⟩, fun _ h0 => False.elim (h0 rfl)⟩
      · refine ⟨⟨cellId_lt (by omega) hc, cellId_lt (by omega) hc⟩, fun _ _ => Or.inr ?_⟩
        exact ⟨by simp only [colOf_cellId (show r - 1 < 5 by omega), colOf_cellId (show r < 5 by omega)],
               by simp only [rowOf_cellId (show r - 1 < 5 by omega), rowOf_cellId (show r < 5 by omega)]
                  left; omega⟩

private theorem mem_boardEdges_v {b : Board} {x r : Nat}
    (hx : x ≤ b.width) (hr : r < 5) (hoff : (b.verticalAt x).testBit r = false) :
    vEdge b.width x r ∈ boardEdges b := by
  simp only [boardEdges, List.mem_append, List.mem_flatMap, List.mem_range,
    vColEdges, List.mem_map, List.mem_filter]
  exact Or.inl ⟨x, by omega, r, ⟨hr, by simp [hoff]⟩, rfl⟩

private theorem mem_boardEdges_h {b : Board} {c r : Nat}
    (hc : c < b.width) (hr : r < 6) (hoff : (b.horizontalAt c).testBit r = false) :
    hEdge c r ∈ boardEdges b := by
  simp only [boardEdges, List.mem_append, List.mem_flatMap, List.mem_range,
    hColEdges, List.mem_map, List.mem_filter]
  exact Or.inr ⟨c, hc, r, ⟨hr, by simp [hoff]⟩, rfl⟩

/-- A set of interior cells closed under erased sticks cannot form a rectangle. -/
private theorem closed_not_rect {b : Board} (hrect : ¬ b.HasRectangle)
    {P : Nat → Prop} (h0 : ¬ P 0) (hclosed : ∀ e ∈ boardEdges b, P e.1 ↔ P e.2)
    {a d x y : Nat} (had : a < d) (hd : d ≤ 5) (hxy : x < y) (hy : y ≤ b.width)
    (hmatch : ∀ r c, r < 5 → c < b.width →
      (P (cellId r c) ↔ a ≤ r ∧ r < d ∧ x ≤ c ∧ c < y)) : False := by
  apply hrect
  refine ⟨x, y, a, d, hxy, hy, had, by omega, ?_, ?_, ?_⟩
  · intro i hlo hhi
    cases hbit : (b.verticalAt x).testBit i
    · have hedge := hclosed _ (mem_boardEdges_v (by omega) (by omega) hbit)
      have hin : P (cellId i x) := (hmatch i x (by omega) (by omega)).mpr ⟨hlo, hhi, by omega, hxy⟩
      unfold vEdge at hedge
      by_cases hx0 : x = 0
      · subst hx0; simp only [↓reduceIte] at hedge; exact False.elim (h0 (hedge.mpr hin))
      · have hxn : x ≠ b.width := by omega
        simp only [hx0, hxn, ↓reduceIte] at hedge
        have hout := (hmatch i (x - 1) (by omega) (by omega)).mp (hedge.mpr hin)
        omega
    · rfl
  · intro i hlo hhi
    cases hbit : (b.verticalAt y).testBit i
    · have hedge := hclosed _ (mem_boardEdges_v hy (by omega) hbit)
      have hin : P (cellId i (y - 1)) :=
        (hmatch i (y - 1) (by omega) (by omega)).mpr ⟨hlo, hhi, by omega, by omega⟩
      unfold vEdge at hedge
      by_cases hyn : y = b.width
      · have hne : b.width ≠ 0 := by omega
        rw [hyn] at hedge hin
        simp only [hne, ↓reduceIte] at hedge
        exact False.elim (h0 (hedge.mp hin))
      · have hy0 : y ≠ 0 := by omega
        simp only [hy0, hyn, ↓reduceIte] at hedge
        have hout := (hmatch i y (by omega) (by omega)).mp (hedge.mp hin)
        omega
    · rfl
  · intro k hlo hhi
    constructor
    · cases hbit : (b.horizontalAt k).testBit a
      · have hedge := hclosed _ (mem_boardEdges_h (by omega) (by omega) hbit)
        have hin : P (cellId a k) :=
          (hmatch a k (by omega) (by omega)).mpr ⟨by omega, had, hlo, hhi⟩
        unfold hEdge at hedge
        by_cases ha0 : a = 0
        · subst ha0; simp only [↓reduceIte] at hedge; exact False.elim (h0 (hedge.mpr hin))
        · have ha5 : a ≠ 5 := by omega
          simp only [ha0, ha5, ↓reduceIte] at hedge
          have hout := (hmatch (a - 1) k (by omega) (by omega)).mp (hedge.mpr hin)
          omega
      · rfl
    · cases hbit : (b.horizontalAt k).testBit d
      · have hedge := hclosed _ (mem_boardEdges_h (by omega) (by omega) hbit)
        have hin : P (cellId (d - 1) k) :=
          (hmatch (d - 1) k (by omega) (by omega)).mpr ⟨by omega, by omega, hlo, hhi⟩
        unfold hEdge at hedge
        by_cases hd5 : d = 5
        · rw [hd5] at hedge hin
          simp only [show (5 : Nat) ≠ 0 by decide, ↓reduceIte] at hedge
          exact False.elim (h0 (hedge.mp hin))
        · have hd0 : d ≠ 0 := by omega
          simp only [hd0, hd5, ↓reduceIte] at hedge
          have hout := (hmatch d k (by omega) (by omega)).mp (hedge.mp hin)
          omega
      · rfl

/-! ## 4. Grid connectivity and small interior component shapes -/

private inductive GridReach (S : List Nat) : Nat → Nat → Prop where
  | refl (a : Nat) : GridReach S a a
  | step {a b c : Nat} : b ∈ S → gridAdj a b → GridReach S b c → GridReach S a c

private theorem reach_to_gridReach {b : Board} (hn : 0 < b.width) {r : Nat}
    (hr : r ≠ comp (boardEdges b) 0) {u w : Nat}
    (hreach : Reach (boardEdges b) u w) (hu : comp (boardEdges b) u = r) :
    GridReach ((List.range (5 * b.width + 1)).filter
      (fun v => decide (comp (boardEdges b) v = r))) u w := by
  induction hreach with
  | refl a => exact .refl a
  | @step a x c hedge _ ih =>
    have hax : comp (boardEdges b) a = comp (boardEdges b) x :=
      hedge.elim comp_edge (fun h => (comp_edge h).symm)
    have hx : comp (boardEdges b) x = r := hax.symm.trans hu
    have ha0 : a ≠ 0 := fun h => hr (hu ▸ h ▸ rfl)
    have hx0 : x ≠ 0 := fun h => hr (hx ▸ h ▸ rfl)
    have ⟨hxlt, hadj⟩ : x < 5 * b.width + 1 ∧ gridAdj a x := by
      rcases hedge with h | h
      · obtain ⟨⟨_, hlt⟩, hadj⟩ := boardEdges_prop hn h
        exact ⟨hlt, hadj ha0 hx0⟩
      · obtain ⟨⟨hlt, _⟩, hadj⟩ := boardEdges_prop hn h
        exact ⟨hlt, gridAdj_symm (hadj hx0 ha0)⟩
    have hxmem : x ∈ (List.range (5 * b.width + 1)).filter
        (fun v => decide (comp (boardEdges b) v = r)) :=
      List.mem_filter.mpr ⟨List.mem_range.mpr hxlt, decide_eq_true hx⟩
    exact .step hxmem hadj (ih hx)

private theorem first_step_ne {S : List Nat} {u w : Nat}
    (h : GridReach S u w) (hne : u ≠ w) : ∃ z ∈ S, z ≠ u ∧ gridAdj u z := by
  cases h with
  | refl _ => exact False.elim (hne rfl)
  | step hz hadj _ => exact ⟨_, hz, fun heq => gridAdj_irrefl u (heq ▸ hadj), hadj⟩

/-- Discrete intermediate value theorem for grid paths inside column 0. -/
private theorem gridReach_col0_between {S : List Nat}
    (hcol : ∀ v ∈ S, colOf v = 0) {u w : Nat} (hu : u ∈ S)
    (h : GridReach S u w) {k : Nat} (hlo : rowOf u ≤ k) (hhi : k ≤ rowOf w) :
    ∃ z ∈ S, rowOf z = k := by
  induction h with
  | refl a => exact ⟨a, hu, by omega⟩
  | @step a b c hb hadj _ ih =>
    by_cases hak : rowOf a = k
    · exact ⟨a, hu, hak⟩
    · have hca := hcol a hu
      have hcb := hcol b hb
      have hstep : rowOf a + 1 = rowOf b ∨ rowOf b + 1 = rowOf a := by
        rcases hadj with ⟨_, h1 | h1⟩ | ⟨_, h2⟩
        · omega
        · omega
        · exact h2
      exact ih hb (by omega) hhi

private theorem list_min_max_row {S : List Nat} (hne : S ≠ []) :
    (∃ u ∈ S, ∀ v ∈ S, rowOf u ≤ rowOf v) ∧ (∃ w ∈ S, ∀ v ∈ S, rowOf v ≤ rowOf w) := by
  induction S with
  | nil => exact False.elim (hne rfl)
  | cons x xs ih =>
    cases xs with
    | nil => exact ⟨⟨x, List.mem_cons_self, by simp⟩, ⟨x, List.mem_cons_self, by simp⟩⟩
    | cons y ys =>
      obtain ⟨⟨u, hu, humin⟩, ⟨w, hw, hwmax⟩⟩ := ih (by simp)
      constructor
      · by_cases h : rowOf x ≤ rowOf u
        · exact ⟨x, List.mem_cons_self, fun v hv => (List.mem_cons.mp hv).elim (fun e => e ▸ Nat.le_refl _)
            (fun hm => Nat.le_trans h (humin v hm))⟩
        · exact ⟨u, List.mem_cons_of_mem _ hu, fun v hv => (List.mem_cons.mp hv).elim (fun e => by subst e; omega)
            (humin v)⟩
      · by_cases h : rowOf w ≤ rowOf x
        · exact ⟨x, List.mem_cons_self, fun v hv => (List.mem_cons.mp hv).elim (fun e => e ▸ Nat.le_refl _)
            (fun hm => Nat.le_trans (hwmax v hm) h)⟩
        · exact ⟨w, List.mem_cons_of_mem _ hw, fun v hv => (List.mem_cons.mp hv).elim (fun e => by subst e; omega)
            (hwmax v)⟩

private def IsLTromino (f : Nat → Nat) (n r : Nat) : Prop :=
  ∃ rm cm ra ca, rm < 5 ∧ cm < n ∧ ra < 5 ∧ ca < n ∧
    (rm + 1 = ra ∨ ra + 1 = rm) ∧ (cm + 1 = ca ∨ ca + 1 = cm) ∧
    ∀ row col, row < 5 → col < n →
      (f (cellId row col) = r ↔
        (row = rm ∧ col = cm) ∨ (row = ra ∧ col = cm) ∨ (row = rm ∧ col = ca))

/-- In a rectangle-free board, every interior component has at least 3 cells,
and any 3-cell interior component is an L-tromino. -/
private theorem interior_component_shape {b : Board} (hn : 0 < b.width) (hrect : ¬ b.HasRectangle)
    {r : Nat} (hrlt : r < 5 * b.width + 1) (hrid : comp (boardEdges b) r = r)
    (hrne : r ≠ comp (boardEdges b) 0) :
    let f := comp (boardEdges b)
    let S := (List.range (5 * b.width + 1)).filter (fun v => decide (f v = r))
    3 ≤ S.length ∧ (S.length = 3 → IsLTromino f b.width r) := by
  intro f S
  have hclosed : ∀ e ∈ boardEdges b, f e.1 = r ↔ f e.2 = r := fun e he => by
    have h := comp_edge he; exact ⟨fun h1 => h.symm.trans h1, fun h2 => h.trans h2⟩
  have h0 : ¬ f 0 = r := fun h => hrne h.symm
  have hSnd : S.Nodup := List.nodup_range.filter _
  have hSmem : ∀ v, v ∈ S ↔ v < 5 * b.width + 1 ∧ f v = r := fun v => by
    simp [S, List.mem_filter, List.mem_range]
  have hcell : ∀ v ∈ S, 0 < v ∧ rowOf v < 5 ∧ colOf v < b.width := fun v hv => by
    obtain ⟨hlt, hfv⟩ := (hSmem v).mp hv
    have hv0 : v ≠ 0 := fun h => h0 (h ▸ hfv)
    exact ⟨by omega, by simp [rowOf]; omega, by simp [colOf]; omega⟩
  have hrc : ∀ r' c', r' < 5 → c' < b.width → (f (cellId r' c') = r ↔ cellId r' c' ∈ S) :=
    fun r' c' hr' hc' => by rw [hSmem]; exact ⟨fun h => ⟨cellId_lt hr' hc', h⟩, And.right⟩
  have hreach : ∀ u ∈ S, ∀ w ∈ S, GridReach S u w := fun u hu w hw =>
    reach_to_gridReach hn hrne
      (comp_reach (boardEdges b) (((hSmem u).mp hu).2.trans ((hSmem w).mp hw).2.symm))
      ((hSmem u).mp hu).2
  have hrS : r ∈ S := (hSmem r).mpr ⟨hrlt, hrid⟩
  match S with
  | [] => cases hrS
  | [u] =>
    exfalso
    have hu := hcell u List.mem_cons_self
    apply closed_not_rect hrect (P := fun v => f v = r) h0 hclosed (a := rowOf u) (d := rowOf u + 1)
      (x := colOf u) (y := colOf u + 1) (by omega) (by omega) (by omega) (by omega)
    intro r' c' hr' hc'
    rw [hrc r' c' hr' hc', List.mem_singleton]
    exact ⟨fun heq => by subst heq; simp only [rowOf_cellId hr', colOf_cellId hr']; omega,
           fun h => by rw [show r' = rowOf u by omega, show c' = colOf u by omega, cellId_row_col hu.1]⟩
  | [u, w] =>
    exfalso
    have hnd2 : u ≠ w := by
      simp only [List.nodup_cons, List.mem_singleton] at hSnd; exact hSnd.1
    have hu := hcell u List.mem_cons_self
    have hw := hcell w (List.mem_cons_of_mem _ List.mem_cons_self)
    obtain ⟨z, hz, hzu, hadj⟩ := first_step_ne
      (hreach u List.mem_cons_self w (List.mem_cons_of_mem _ List.mem_cons_self)) hnd2
    have hzw : z = w := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      exact hz.resolve_left hzu
    subst hzw
    apply closed_not_rect hrect (P := fun v => f v = r) h0 hclosed
      (a := min (rowOf u) (rowOf z)) (d := max (rowOf u) (rowOf z) + 1)
      (x := min (colOf u) (colOf z)) (y := max (colOf u) (colOf z) + 1)
      (by omega) (by omega) (by omega) (by omega)
    intro r' c' hr' hc'
    have hiff2 : f (cellId r' c') = r ↔
        (r' = rowOf u ∧ c' = colOf u) ∨ (r' = rowOf z ∧ c' = colOf z) := by
      rw [hrc r' c' hr' hc']
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro (heq | heq)
        · left; rw [← heq, rowOf_cellId hr', colOf_cellId hr']; exact ⟨rfl, rfl⟩
        · right; rw [← heq, rowOf_cellId hr', colOf_cellId hr']; exact ⟨rfl, rfl⟩
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · left; exact cellId_row_col hu.1
        · right; exact cellId_row_col hw.1
    rw [hiff2]
    rcases hadj with ⟨hreq, hc | hc⟩ | ⟨hceq, hr | hr⟩ <;> omega
  | [u, v, w] =>
    refine ⟨by simp, fun _ => ?_⟩
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hSnd
    obtain ⟨⟨huv, huw⟩, hvw, _⟩ := hSnd
    have huS : u ∈ [u, v, w] := List.mem_cons_self
    have hvS : v ∈ [u, v, w] := List.mem_cons_of_mem _ List.mem_cons_self
    have hwS : w ∈ [u, v, w] := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have deg_u : gridAdj u v ∨ gridAdj u w := by
      obtain ⟨z, hz, hzu, hadj⟩ := first_step_ne (hreach u huS v hvS) huv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · exact False.elim (hzu rfl)
      · exact Or.inl hadj
      · exact Or.inr hadj
    have deg_v : gridAdj v u ∨ gridAdj v w := by
      obtain ⟨z, hz, hzv, hadj⟩ := first_step_ne (hreach v hvS u huS) (Ne.symm huv)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · exact Or.inl hadj
      · exact False.elim (hzv rfl)
      · exact Or.inr hadj
    have deg_w : gridAdj w u ∨ gridAdj w v := by
      obtain ⟨z, hz, hzw, hadj⟩ := first_step_ne (hreach w hwS u huS) (Ne.symm huw)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · exact Or.inl hadj
      · exact Or.inr hadj
      · exact False.elim (hzw rfl)
    have hcenter : ∃ m p q, m ∈ [u, v, w] ∧ p ∈ [u, v, w] ∧ q ∈ [u, v, w] ∧ p ≠ q ∧
        gridAdj m p ∧ gridAdj m q ∧ (∀ z ∈ [u, v, w], z = m ∨ z = p ∨ z = q) := by
      by_cases euv : gridAdj u v <;> by_cases evw : gridAdj v w <;> by_cases euw : gridAdj u w
      · exact ⟨u, v, w, huS, hvS, hwS, hvw, euv, euw, fun z hz => by simpa using hz⟩
      · exact ⟨v, u, w, hvS, huS, hwS, huw, gridAdj_symm euv, evw, fun z hz => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl | rfl <;> simp⟩
      · exact ⟨u, v, w, huS, hvS, hwS, hvw, euv, euw, fun z hz => by simpa using hz⟩
      · exfalso; exact deg_w.elim (fun h => euw (gridAdj_symm h)) (fun h => evw (gridAdj_symm h))
      · exact ⟨w, u, v, hwS, huS, hvS, huv, gridAdj_symm euw, gridAdj_symm evw, fun z hz => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl | rfl <;> simp⟩
      · exfalso; exact deg_u.elim euv euw
      · exfalso; exact deg_v.elim (fun h => euv (gridAdj_symm h)) evw
      · exfalso; exact deg_u.elim euv euw
    obtain ⟨m, p, q, hmS, hpS, hqS, hpq, hmp, hmq, hcover⟩ := hcenter
    have hm := hcell m hmS
    have hp := hcell p hpS
    have hq := hcell q hqS
    have hSiff : ∀ r' c', r' < 5 → c' < b.width →
        (f (cellId r' c') = r ↔
          (r' = rowOf m ∧ c' = colOf m) ∨
          (r' = rowOf p ∧ c' = colOf p) ∨
          (r' = rowOf q ∧ c' = colOf q)) := by
      intro r' c' hr' hc'
      rw [hrc r' c' hr' hc']
      constructor
      · intro hmem
        rcases hcover _ hmem with heq | heq | heq
        · left; rw [← heq, rowOf_cellId hr', colOf_cellId hr']; exact ⟨rfl, rfl⟩
        · right; left; rw [← heq, rowOf_cellId hr', colOf_cellId hr']; exact ⟨rfl, rfl⟩
        · right; right; rw [← heq, rowOf_cellId hr', colOf_cellId hr']; exact ⟨rfl, rfl⟩
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · rwa [cellId_row_col hm.1]
        · rwa [cellId_row_col hp.1]
        · rwa [cellId_row_col hq.1]
    rcases hmp with ⟨hrmp, hcmp⟩ | ⟨hcmp, hrmp⟩ <;> rcases hmq with ⟨hrmq, hcmq⟩ | ⟨hcmq, hrmq⟩
    · exfalso
      have hne_c : colOf p ≠ colOf q := fun heq => hpq <| by
        rw [← cellId_row_col hp.1, ← cellId_row_col hq.1, ← hrmp, hrmq, heq]
      apply closed_not_rect hrect (P := fun v => f v = r) h0 hclosed (a := rowOf m) (d := rowOf m + 1)
        (x := colOf m - 1) (y := colOf m + 2) (by omega) (by omega) (by omega) (by omega)
      intro r' c' hr' hc'; rw [hSiff r' c' hr' hc']; omega
    · refine ⟨rowOf m, colOf m, rowOf q, colOf p, hm.2.1, hm.2.2, hq.2.1, hp.2.2,
        hrmq, hcmp, fun r' c' hr' hc' => ?_⟩
      rw [hSiff r' c' hr' hc']; omega
    · refine ⟨rowOf m, colOf m, rowOf p, colOf q, hm.2.1, hm.2.2, hp.2.1, hq.2.2,
        hrmp, hcmq, fun r' c' hr' hc' => ?_⟩
      rw [hSiff r' c' hr' hc']; omega
    · exfalso
      have hne_r : rowOf p ≠ rowOf q := fun heq => hpq <| by
        rw [← cellId_row_col hp.1, ← cellId_row_col hq.1, ← hcmp, hcmq, heq]
      apply closed_not_rect hrect (P := fun v => f v = r) h0 hclosed (a := rowOf m - 1) (d := rowOf m + 2)
        (x := colOf m) (y := colOf m + 1) (by omega) (by omega) (by omega) (by omega)
      intro r' c' hr' hc'; rw [hSiff r' c' hr' hc']; omega
  | _ :: _ :: _ :: _ :: _ => exact ⟨by simp, fun h => by simp at h⟩

/-! ## 5. End-column parity contradiction for widths `n = 3k + 2` -/

private theorem end_column_contradiction {b : Board} (hrect : ¬ b.HasRectangle)
    (c0 c1 : Nat) (hc0 : c0 < b.width) (hc1 : c1 < b.width)
    (hc_adj01 : c0 + 1 = c1 ∨ c1 + 1 = c0)
    (hadj_end : ∀ c, c < b.width → (c0 + 1 = c ∨ c + 1 = c0) → c = c1)
    (hcol_L : ∀ i, i < 5 →
      comp (boardEdges b) (cellId i c0) ≠ comp (boardEdges b) 0 ∧
      IsLTromino (comp (boardEdges b)) b.width (comp (boardEdges b) (cellId i c0))) : False := by
  let f := comp (boardEdges b)
  have hc01 : c0 ≠ c1 := by omega
  -- Every L-tromino meeting column c0 lies entirely within columns {c0, c1}.
  have hstrip : ∀ i, i < 5 →
      let r := f (cellId i c0)
      ∃ rm cm ra ca, rm < 5 ∧ ra < 5 ∧ (rm + 1 = ra ∨ ra + 1 = rm) ∧
        ((cm = c0 ∧ ca = c1) ∨ (cm = c1 ∧ ca = c0)) ∧
        ∀ row col, row < 5 → col < b.width →
          (f (cellId row col) = r ↔
            (row = rm ∧ col = cm) ∨ (row = ra ∧ col = cm) ∨ (row = rm ∧ col = ca)) := by
    intro i hi
    obtain ⟨rm, cm, ra, ca, hrm, hcm, hra, hca, hr_adj, hc_adj, hiff⟩ := (hcol_L i hi).2
    refine ⟨rm, cm, ra, ca, hrm, hra, hr_adj, ?_, hiff⟩
    rcases (hiff i c0 hi hc0).mp rfl with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact Or.inl ⟨rfl, hadj_end ca hca hc_adj⟩
    · exact Or.inl ⟨rfl, hadj_end ca hca hc_adj⟩
    · exact Or.inr ⟨hadj_end cm hcm hc_adj.symm, rfl⟩
  -- Each L meeting c0 covers either 1 cell of c0 (corner in c1) or 2 adjacent cells of c0.
  -- Since 5 is odd, at least one row i0 ∈ {0, 2, 4} belongs to a singleton L on c0.
  have hsingle_or_pair : ∀ i, i < 5 →
      (∃ ra, ra < 5 ∧ (i + 1 = ra ∨ ra + 1 = i) ∧
        ∀ row col, row < 5 → col < b.width →
          (f (cellId row col) = f (cellId i c0) ↔
            (row = i ∧ col = c1) ∨ (row = ra ∧ col = c1) ∨ (row = i ∧ col = c0))) ∨
      (∃ j, j < 5 ∧ (i + 1 = j ∨ j + 1 = i) ∧
        ∀ row, row < 5 → (f (cellId row c0) = f (cellId i c0) ↔ row = i ∨ row = j)) := by
    intro i hi
    obtain ⟨rm, cm, ra, ca, hrm, hra, hradj, hcols, hiff⟩ := hstrip i hi
    rcases hcols with ⟨hcm, hca⟩ | ⟨hcm, hca⟩
    · subst cm; subst ca
      right
      rcases (hiff i c0 hi hc0).mp rfl with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨_, h⟩
      · exact ⟨ra, hra, hradj, fun row hrow => by
          rw [hiff row c0 hrow hc0]; exact ⟨by rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩) <;> omega,
            by rintro (rfl | rfl) <;> simp⟩⟩
      · exact ⟨rm, hrm, hradj.symm, fun row hrow => by
          rw [hiff row c0 hrow hc0]; exact ⟨by rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩) <;> omega,
            by rintro (rfl | rfl) <;> simp⟩⟩
      · omega
    · subst cm; subst ca
      left
      rcases (hiff i c0 hi hc0).mp rfl with ⟨_, h⟩ | ⟨_, h⟩ | ⟨rfl, _⟩
      · omega
      · omega
      · exact ⟨ra, hra, hradj, hiff⟩
  have hex_single : ∃ i0 raA, i0 < 5 ∧ raA < 5 ∧ (i0 + 1 = raA ∨ raA + 1 = i0) ∧
      ∀ row col, row < 5 → col < b.width →
        (f (cellId row col) = f (cellId i0 c0) ↔
          (row = i0 ∧ col = c1) ∨ (row = raA ∧ col = c1) ∨ (row = i0 ∧ col = c0)) := by
    rcases hsingle_or_pair 0 (by decide) with ⟨ra, h⟩ | ⟨j0, hj0, h01, hpair0⟩
    · exact ⟨0, ra, by decide, h⟩
    have hj0_eq : j0 = 1 := by omega
    subst hj0_eq
    have h01_eq : f (cellId 1 c0) = f (cellId 0 c0) := (hpair0 1 (by decide)).mpr (Or.inr rfl)
    have h2_ne_1 : f (cellId 2 c0) ≠ f (cellId 1 c0) := fun h => by
      have := (hpair0 2 (by decide)).mp (h.trans h01_eq); omega
    rcases hsingle_or_pair 2 (by decide) with ⟨ra, h⟩ | ⟨j2, hj2, h23, hpair2⟩
    · exact ⟨2, ra, by decide, h⟩
    have hj2_eq : j2 = 3 := by
      have hne1 : j2 ≠ 1 := fun h => h2_ne_1 ((hpair2 1 (by decide)).mpr (Or.inr h.symm)).symm
      omega
    subst hj2_eq
    have h23_eq : f (cellId 3 c0) = f (cellId 2 c0) := (hpair2 3 (by decide)).mpr (Or.inr rfl)
    have h4_ne_3 : f (cellId 4 c0) ≠ f (cellId 3 c0) := fun h => by
      have := (hpair2 4 (by decide)).mp (h.trans h23_eq); omega
    rcases hsingle_or_pair 4 (by decide) with ⟨ra, h⟩ | ⟨j4, hj4, h43, hpair4⟩
    · exact ⟨4, ra, by decide, h⟩
    have hj4_eq : j4 = 3 := by omega
    subst hj4_eq
    exact False.elim (h4_ne_3 ((hpair4 3 (by decide)).mpr (Or.inr rfl)).symm)
  -- Take this singleton L-tromino rA = {(i0, c0), (i0, c1), (raA, c1)}.
  obtain ⟨rmA, raA, hrmA, hraA, hradjA, hiffA⟩ := hex_single
  let rA := f (cellId rmA c0)
  -- The neighboring end-column cell (raA, c0) belongs to a distinct L-tromino rB.
  let rB := f (cellId raA c0)
  have hrBA : rB ≠ rA := fun heq => by
    rcases (hiffA raA c0 hraA hc0).mp heq with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;> omega
  obtain ⟨rmB, cmB, raB, caB, hrmB, hraB, hradjB, hcolsB, hiffB⟩ := hstrip raA hraA
  -- Cell (raA, c1) already belongs to rA ≠ rB, which forces rB's corner into c0 with rmB ≠ raA!
  have hnotB_ra1 : f (cellId raA c1) ≠ rB := fun h =>
    hrBA (h.symm.trans ((hiffA raA c1 hraA hc1).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  have hnotB_rm0 : f (cellId rmA c0) ≠ rB := fun h => hrBA h.symm
  have hcmB_c0 : cmB = c0 ∧ caB = c1 := by
    rcases hcolsB with h | ⟨hcm, hca⟩
    · exact h
    · subst cmB; subst caB
      exfalso
      rcases (hiffB raA c0 hraA hc0).mp rfl with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩
      · omega
      · omega
      · exact hnotB_ra1 ((hiffB raA c1 hraA hc1).mpr (Or.inl ⟨h, rfl⟩))
  rcases hcmB_c0 with ⟨hcmB_eq, hcaB_eq⟩
  subst cmB; subst caB
  have hrmB_ne : rmB ≠ raA := fun heq =>
    hnotB_ra1 ((hiffB raA c1 hraA hc1).mpr (Or.inr (Or.inr ⟨heq.symm, rfl⟩)))
  have hraB_eq : raB = raA := by
    rcases (hiffB raA c0 hraA hc0).mp rfl with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
    · exact False.elim (hrmB_ne h.symm)
    · exact h.symm
    · omega
  have hrmB_ne_rmA : rmB ≠ rmA := fun heq =>
    hnotB_rm0 ((hiffB rmA c0 hrmA hc0).mpr (Or.inl ⟨heq.symm, rfl⟩))
  -- Together rA ∪ rB = {rmA, raA, rmB} × {c0, c1} is an intact 3 × 2 rectangle.
  have h0_AB : ¬ (f 0 = rA ∨ f 0 = rB) := by
    rintro (h | h)
    · exact (hcol_L rmA hrmA).1 h.symm
    · exact (hcol_L raA hraA).1 h.symm
  have hclosed_AB : ∀ e ∈ boardEdges b, (f e.1 = rA ∨ f e.1 = rB) ↔ (f e.2 = rA ∨ f e.2 = rB) := by
    intro e he; simp only [f]; rw [comp_edge he]
  have hmatch_AB : ∀ r' c', r' < 5 → c' < b.width →
      ((f (cellId r' c') = rA ∨ f (cellId r' c') = rB) ↔
        min rmA rmB ≤ r' ∧ r' < max rmA rmB + 1 ∧ min c0 c1 ≤ c' ∧ c' < max c0 c1 + 1) := by
    intro r' c' hr' hc'
    rw [hiffA r' c' hr' hc', hiffB r' c' hr' hc', hraB_eq]
    have hlo_hi : ∀ x y z : Nat, (x + 1 = y ∨ y + 1 = x) → (z + 1 = y ∨ y + 1 = z) → z ≠ x →
        (min x z ≤ r' ∧ r' < max x z + 1 ↔ r' = x ∨ r' = y ∨ r' = z) := fun x y z _ _ _ => by omega
    have hcol_hi : ∀ x y : Nat, (x + 1 = y ∨ y + 1 = x) →
        (min x y ≤ c' ∧ c' < max x y + 1 ↔ c' = x ∨ c' = y) := fun x y _ => by omega
    rw [← and_assoc, hlo_hi rmA raA rmB hradjA (hraB_eq ▸ hradjB) hrmB_ne_rmA, hcol_hi c0 c1 hc_adj01]
    constructor
    · rintro ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)) <;> simp
    · rintro ⟨rfl | rfl | rfl, rfl | rfl⟩ <;> simp
  exact closed_not_rect hrect (P := fun v => f v = rA ∨ f v = rB) h0_AB hclosed_AB
    (a := min rmA rmB) (d := max rmA rmB + 1) (x := min c0 c1) (y := max c0 c1 + 1)
    (Nat.lt_succ_of_le (Nat.le_trans (Nat.min_le_left _ _) (Nat.le_max_left _ _)))
    (Nat.succ_le_of_lt (Nat.max_lt.mpr ⟨hrmA, hrmB⟩))
    (Nat.lt_succ_of_le (Nat.le_trans (Nat.min_le_left _ _) (Nat.le_max_left _ _)))
    (Nat.succ_le_of_lt (Nat.max_lt.mpr ⟨hc0, hc1⟩))
    hmatch_AB

/-! ## 6. Main lower-bound theorem -/

theorem lower_of_no_rectangle (b : Board) (hn : 0 < b.width) (hrect : ¬ b.HasRectangle) :
    target b.width ≤ b.cost := by
  let n := b.width
  let V := 5 * n + 1
  let es := boardEdges b
  let f := comp es
  let ext := f 0
  have he_lt : ∀ e ∈ es, e.1 < V ∧ e.2 < V := fun e he => (boardEdges_prop hn he).1
  have hclosed_eq : ∀ r, ∀ e ∈ es, f e.1 = r ↔ f e.2 = r := fun r e he => by
    simp only [f]; rw [comp_edge he]
  let rs := roots f V
  have hrs_nd : rs.Nodup := List.nodup_range.filter _
  have hext_lt : ext < V := comp_lt es he_lt (by omega)
  have hext_in : ext ∈ rs :=
    List.mem_filter.mpr ⟨List.mem_range.mpr hext_lt, decide_eq_true (comp_idem es 0)⟩
  let intRoots := rs.filter (· != ext)
  let mem (r : Nat) : List Nat := (List.range V).filter (fun v => decide (f v = r))
  -- Graph component bound: 5n ≤ intRoots.length + b.cost.
  obtain ⟨hrs_len, hrs_sum⟩ := filter_ne_split hrs_nd hext_in (fun r => (mem r).length)
  have hrs_len' : rs.length = intRoots.length + 1 := hrs_len
  have hrs_sum' : (rs.map (fun r => (mem r).length)).sum =
      (mem ext).length + (intRoots.map (fun r => (mem r).length)).sum := hrs_sum
  have hcomp_bound : 5 * n ≤ intRoots.length + b.cost := by
    have h1 := roots_add_edges V es
    rw [boardEdges_length b] at h1
    change 5 * n + 1 ≤ rs.length + b.cost at h1
    omega
  -- Vertex partition: (mem ext).length + ∑_{r ∈ intRoots} (mem r).length = 5n + 1.
  have hpart : (mem ext).length + (intRoots.map (fun r => (mem r).length)).sum = 5 * n + 1 := by
    have htot : (rs.map (fun r => (mem r).length)).sum = V := by
      simpa [mem] using sum_filter_partition (xs := List.range V) (rs := rs) f hrs_nd fun v hv =>
        List.mem_filter.mpr ⟨List.mem_range.mpr (comp_lt es he_lt (List.mem_range.mp hv)),
          decide_eq_true (comp_idem es v)⟩
    omega
  -- At least one cell belongs to the exterior component, so (mem ext).length ≥ 2.
  have hext_ge2 : 2 ≤ (mem ext).length := by
    have hex : ∃ v, 0 < v ∧ v < V ∧ f v = ext :=
      Classical.byContradiction fun hnone => by
        apply closed_not_rect hrect (P := fun v => v ≠ 0) (fun h => h rfl) ?_
          (a := 0) (d := 5) (x := 0) (y := n) (by decide) (by decide) hn (Nat.le_refl _)
          (fun r c hr hc => by
            have hpos := cellId_pos r c
            exact ⟨fun _ => ⟨Nat.zero_le _, hr, Nat.zero_le _, hc⟩, fun _ => by omega⟩)
        intro e he
        have hlt := he_lt e he
        have hce : f e.1 = f e.2 := comp_edge he
        constructor <;> intro hne hzero
        · exact hnone ⟨e.1, by omega, hlt.1, hce.trans (hzero ▸ rfl)⟩
        · exact hnone ⟨e.2, by omega, hlt.2, hce.symm.trans (hzero ▸ rfl)⟩
    obtain ⟨v, hv0, hvlt, hfv⟩ := hex
    have h0m : 0 ∈ mem ext := List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), by simp [ext]⟩
    have hvm : v ∈ mem ext := List.mem_filter.mpr ⟨List.mem_range.mpr hvlt, decide_eq_true hfv⟩
    exact length_ge_two_of_mem (List.nodup_range.filter _) h0m hvm (by omega)
  -- Case n = 1: no interior component can exist.
  by_cases hn1 : b.width = 1
  · have hint0 : intRoots = [] := by
      match h : intRoots with
      | [] => rfl
      | r :: _ =>
        exfalso
        have hr_in : r ∈ intRoots := h ▸ List.mem_cons_self
        have hr_rs := (List.mem_filter.mp hr_in).1
        have hrne : r ≠ ext := by simpa [bne_iff_ne] using (List.mem_filter.mp hr_in).2
        have hrlt : r < V := List.mem_range.mp (List.mem_filter.mp hr_rs).1
        have hrid : f r = r := of_decide_eq_true (List.mem_filter.mp hr_rs).2
        have hmem_ne : mem r ≠ [] := by
          intro hempty
          have hrS : r ∈ mem r := List.mem_filter.mpr ⟨List.mem_range.mpr hrlt, decide_eq_true hrid⟩
          rw [hempty] at hrS; cases hrS
        have hcol0 : ∀ v ∈ mem r, colOf v = 0 := fun v hv => by
          have hvlt := List.mem_range.mp (List.mem_filter.mp hv).1
          have hfv := of_decide_eq_true (List.mem_filter.mp hv).2
          have hv0 : v ≠ 0 := fun h => hrne (hfv ▸ h ▸ rfl)
          simp only [colOf]; omega
        obtain ⟨⟨u, hu, humin⟩, ⟨w, hw, hwmax⟩⟩ := list_min_max_row hmem_ne
        have hw_lt5 : rowOf w < 5 := by simp [rowOf]; omega
        have hgr : GridReach (mem r) u w :=
          reach_to_gridReach hn hrne
            (comp_reach es ((of_decide_eq_true (List.mem_filter.mp hu).2).trans
              (of_decide_eq_true (List.mem_filter.mp hw).2).symm))
            (of_decide_eq_true (List.mem_filter.mp hu).2)
        apply closed_not_rect hrect (P := fun v => f v = r) (fun h => hrne h.symm)
          (hclosed_eq r) (a := rowOf u) (d := rowOf w + 1) (x := 0) (y := 1)
          (by have := humin w hw; omega) (by omega) (by decide) (by omega)
        intro r' c' hr' hc'
        have hc0 : c' = 0 := by omega
        subst hc0
        constructor
        · intro hfr'
          have hmem' : cellId r' 0 ∈ mem r :=
            List.mem_filter.mpr ⟨List.mem_range.mpr (cellId_lt hr' (by omega)), decide_eq_true hfr'⟩
          have hlo := humin _ hmem'
          have hhi := hwmax _ hmem'
          rw [rowOf_cellId hr'] at hlo hhi; omega
        · intro ⟨hlo, hhi, _, _⟩
          obtain ⟨z, hz, hzr⟩ := gridReach_col0_between hcol0 hu hgr hlo (by omega)
          have hzf := of_decide_eq_true (List.mem_filter.mp hz).2
          have hz0 : z ≠ 0 := fun h => hrne (hzf ▸ h ▸ rfl)
          have hzeq : cellId r' 0 = z := by
            rw [← hzr, ← hcol0 z hz, cellId_row_col (by omega)]
          rwa [hzeq]
    simp only [target, hn1, ↓reduceIte]
    rw [hint0] at hcomp_bound; simp at hcomp_bound; omega
  -- Case n ≥ 2: every interior component has size ≥ 3.
  have hge3 : ∀ r ∈ intRoots, 3 ≤ (mem r).length := by
    intro r hr
    have hr_rs := (List.mem_filter.mp hr).1
    have hrne : r ≠ ext := by simpa [bne_iff_ne] using (List.mem_filter.mp hr).2
    have hrlt : r < V := List.mem_range.mp (List.mem_filter.mp hr_rs).1
    have hrid : f r = r := of_decide_eq_true (List.mem_filter.mp hr_rs).2
    exact (interior_component_shape hn hrect hrlt hrid hrne).1
  have h3t : 3 * intRoots.length ≤ 5 * n - 1 := by
    have hmul := sum_ge_mul hge3; omega
  simp only [target, ite_eq_right hn1]
  by_cases hmod : n % 3 = 2
  · -- Remaining case n = 3k + 2: rule out b.cost < (10n + 4) / 3.
    exact Classical.byContradiction fun hlt => by
      have htight : 3 * b.cost ≤ 10 * n + 1 := by omega
      have hext_eq2 : (mem ext).length = 2 := by
        have := sum_ge_mul hge3; omega
      have hall3 : ∀ r ∈ intRoots, (mem r).length = 3 :=
        all_eq_of_sum_le hge3 (by omega)
      have huniq_ext : ∃ vext, ∀ v, 0 < v → v < V → f v = ext → v = vext := by
        match hm : mem ext with
        | [a, c] =>
          have h0m : 0 ∈ mem ext := List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), by simp [ext]⟩
          rw [hm] at h0m; simp only [List.mem_cons, List.not_mem_nil, or_false] at h0m
          rcases h0m with rfl | rfl
          · refine ⟨c, fun v hv0 hvlt hfv => ?_⟩
            have hvm : v ∈ mem ext := List.mem_filter.mpr ⟨List.mem_range.mpr hvlt, decide_eq_true hfv⟩
            rw [hm] at hvm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hvm
            exact hvm.resolve_left (by omega)
          · refine ⟨a, fun v hv0 hvlt hfv => ?_⟩
            have hvm : v ∈ mem ext := List.mem_filter.mpr ⟨List.mem_range.mpr hvlt, decide_eq_true hfv⟩
            rw [hm] at hvm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hvm
            exact hvm.resolve_right (by omega)
        | [] | [_] | _ :: _ :: _ :: _ => rw [hm] at hext_eq2; simp at hext_eq2
      obtain ⟨vext, hvext⟩ := huniq_ext
      have hL_of_ne : ∀ r, r < V → f r = r → r ≠ ext → IsLTromino f n r := fun r hrlt hrid hrne => by
        have hr_in : r ∈ intRoots :=
          List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨List.mem_range.mpr hrlt, decide_eq_true hrid⟩,
            by simp [bne_iff_ne, hrne]⟩
        exact (interior_component_shape hn hrect hrlt hrid hrne).2 (hall3 r hr_in)
      have hcol_ok : ∀ c0, c0 < n → (∀ i, i < 5 → cellId i c0 ≠ vext) →
          ∀ i, i < 5 → f (cellId i c0) ≠ ext ∧ IsLTromino f n (f (cellId i c0)) := by
        intro c0 hc0 havoid i hi
        have hne : f (cellId i c0) ≠ ext := fun heq =>
          havoid i hi (hvext _ (cellId_pos i c0) (cellId_lt hi hc0) heq)
        exact ⟨hne, hL_of_ne _ (comp_lt es he_lt (cellId_lt hi hc0)) (comp_idem es _) hne⟩
      -- Pick an end column (0 or n - 1) that omits vext.
      by_cases h0_ok : colOf vext ≠ 0
      · exact end_column_contradiction hrect 0 1 (by omega) (by omega) (by decide)
          (fun c _ h => by omega)
          (hcol_ok 0 (by omega) fun i hi heq => h0_ok (heq ▸ colOf_cellId hi))
      · exact end_column_contradiction hrect (n - 1) (n - 2) (by omega) (by omega) (by omega)
          (fun c hc h => by omega)
          (hcol_ok (n - 1) (by omega) fun i hi heq => by
            have : colOf vext = n - 1 := heq ▸ colOf_cellId hi; omega)
  · omega

end Matchsticks.LowerProof

namespace Matchsticks

/-- Every rectangle-free board of positive width meets the lower bound. -/
theorem lower (b : Board) (hn : 0 < b.width) (hrect : ¬ b.HasRectangle) :
    target b.width ≤ b.cost :=
  LowerProof.lower_of_no_rectangle b hn hrect

end Matchsticks
