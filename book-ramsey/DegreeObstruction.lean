import BookRamsey

namespace BookRamsey.Graph

/-- The pointwise bounds whose sums over the two blocks give the degree
inequalities. The nonedge inequality is written without truncated subtraction. -/
theorem codegree_bounds (g : Graph 254) (ok : g.check 63 64 = true) (u v : Fin 254)
    (huv : u ≠ v) :
    (g.adj u v = true → g.commonCount u v ≤ 62) ∧
    (g.adj u v = false → g.commonCount u v + 189 ≤ g.degree u + g.degree v) := by
  obtain ⟨hr, hb⟩ := (check_iff ..).mp ok
  constructor
  · intro red
    exact Nat.le_of_lt_succ ((g.not_hasBook_iff 63).mp hr u v red)
  · intro blue
    have hc := (g.complement.not_hasBook_iff 64).mp hb u v (by simp [complement, huv, blue])
    have := nonedge_commonCount g u v huv blue
    omega

end BookRamsey.Graph

namespace BookRamsey.DegreeObstruction

/-!
Consider two sets of 127 vertices with constant internal red degrees `a` and `c`
and constant red degree `b` across the partition. The three inequalities below
are the red two-step-walk counts for pairs inside the first set, inside the
second set, and across the partition. All subtraction in a codegree bound has
been moved to the opposite side so that natural numbers represent it faithfully.
-/
abbrev insideBound (a b : Nat) : Prop :=
  a * (a - 1) + b * (b - 1) + (126 - a) * 189 ≤
    62 * a + (126 - a) * (2 * (a + b))

abbrev acrossBound (a c b : Nat) : Prop :=
  (a + c) * b + (127 - b) * 189 ≤
    62 * b + (127 - b) * (a + c + 2 * b)

def feasible (a c b : Nat) : Bool :=
  decide (a ≤ 126 ∧ c ≤ 126 ∧ b ≤ 127) &&
  decide (insideBound a b) && decide (insideBound c b) && decide (acrossBound a c b)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem sweep (h : Nat) (hh : h = 7 ∨ h = 9) :
    ∀ a : Fin 127, 2 * h ∣ a.val → ∀ c : Fin 127, 2 * h ∣ c.val →
    ∀ b : Fin 128, b.val % h ≤ 1 → feasible a.val c.val b.val = false := by
  rcases hh with rfl | rfl <;> decide +kernel

/-- An odd-order multiplier subgroup of order `h` on the two circulant blocks
has internal orbit sizes `2*h` after imposing inversion closure. Cross-block
orbits have size `h`, together with the optional zero difference. This theorem
excludes all degree triples with those arithmetic properties at orders 7 and 9. -/
theorem excludes_degrees {h a c b : Nat} (hh : h = 7 ∨ h = 9)
    (ha : a ≤ 126) (hc : c ≤ 126) (hb : b ≤ 127)
    (hda : 2 * h ∣ a) (hdc : 2 * h ∣ c) (hr : b % h ≤ 1) :
    ¬ (insideBound a b ∧ insideBound c b ∧ acrossBound a c b) := by
  have fail := sweep h hh ⟨a, by omega⟩ hda ⟨c, by omega⟩ hdc ⟨b, by omega⟩ hr
  intro ⟨first, second, across⟩
  simp [feasible, ha, hc, hb, first, second, across] at fail


open Graph

abbrev Vert := Fin 254

/-- An equitable partition into two sets of 127 vertices. The order of each
list is irrelevant. The parameters are the internal degrees and the cross degree. -/
structure Blocks (g : Graph 254) (a c b : Nat) where
  left : List Vert
  right : List Vert
  partition : (left ++ right).Perm (List.finRange 254)
  leftSize : left.length = 127
  rightSize : right.length = 127
  degreesLeft : ∀ u ∈ left, left.countP (g.adj u) = a ∧ right.countP (g.adj u) = b
  degreesRight : ∀ u ∈ right, left.countP (g.adj u) = b ∧ right.countP (g.adj u) = c

def total (xs : List α) (f : α → Nat) := (xs.map f).sum

theorem total_const (xs : List α) (k : Nat) : total xs (fun _ => k) = xs.length * k := by
  simp [total, List.map_const', List.sum_replicate_nat]

theorem total_add (xs : List α) (f g : α → Nat) :
    total xs (fun x => f x + g x) = total xs f + total xs g := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [total, List.map_cons, List.sum_cons] at *; omega

theorem total_indicator (xs : List α) (p : α → Bool) (v : Nat) :
    total xs (fun x => if p x then v else 0) = xs.countP p * v := by
  induction xs with
  | nil => simp [total]
  | cons a xs ih =>
    cases h : p a <;>
      simp [total, h, Nat.add_mul, Nat.add_comm] at * <;> assumption

theorem total_congr (xs : List α) (f t : α → Nat) (h : ∀ x ∈ xs, f x = t x) :
    total xs f = total xs t := congrArg List.sum (List.map_congr_left h)

theorem total_swap (xs : List α) (ys : List β) (f : α → β → Nat) :
    total xs (fun x => total ys (f x)) = total ys (fun y => total xs (fun x => f x y)) := by
  induction xs with
  | nil =>
    change 0 = total ys (fun _ => 0)
    simp [total_const]
  | cons x xs ih =>
    change total ys (f x) + total xs _ = total ys (fun y => f x y + total xs _)
    rw [total_add, ih]

-- Count walks u--w--v by the middle vertex instead of by the last vertex.
theorem walks (g : Graph n) (u : Fin n) (ends middle : List (Fin n)) :
    total ends (fun v => middle.countP fun w => g.adj u w && g.adj v w) =
    total middle (fun w => if g.adj u w then ends.countP (g.adj w) else 0) := by
  let path (v w : Fin n) := if g.adj u w && g.adj v w then 1 else 0
  have byEnd (v) : total middle (path v) = middle.countP (fun w => g.adj u w && g.adj v w) := by
    simp only [path, total_indicator, Nat.mul_one]
  rw [← total_congr _ _ _ (fun v _ => byEnd v), total_swap]
  apply total_congr
  intro w _
  have sym (v) : g.adj v w = g.adj w v := g.symm v w
  cases h : g.adj u w <;> simp [path, h, sym, total_const, total_indicator]

def other (g : Graph n) (u : Fin n) (xs : List (Fin n)) :=
  xs.countP fun v => !decide (u = v) && !g.adj u v

theorem split_count (g : Graph n) (u : Fin n) (xs : List (Fin n)) :
    xs.count u + xs.countP (g.adj u) + other g u xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons v xs ih =>
    simp only [other, List.countP_cons, List.count_cons, List.length_cons] at *
    by_cases he : u = v
    · subst v; simp [g.loopless]; omega
    · cases hv : g.adj u v <;> simp [he, Ne.symm he] <;> omega

-- A sum of the pointwise red and blue bounds, allowing u to belong to xs.
private theorem sum_bound (g : Graph 254) (ok : g.check 63 64 = true) (u : Vert)
    (xs : List Vert) (d cost : Nat)
    (nonedge : ∀ v ∈ xs, u ≠ v → g.adj u v = false → g.commonCount u v + cost ≤ g.degree u + d) :
    total xs (g.commonCount u) + cost * other g u xs ≤
      xs.count u * g.degree u + 62 * xs.countP (g.adj u) +
        (g.degree u + d) * other g u xs := by
  induction xs with
  | nil => simp [total, other]
  | cons v xs ih =>
    have ih' := ih (fun w hw => nonedge w (List.mem_cons_of_mem _ hw))
    simp only [other, total, List.map_cons, List.sum_cons, List.countP_cons, List.count_cons] at *
    by_cases he : u = v
    · subst v
      have self : g.commonCount u u = g.degree u := by simp [Graph.commonCount, Graph.degree]
      simp [Nat.add_mul] at ih'
      simp [self, g.loopless, Nat.add_mul]
      omega
    · cases hv : g.adj u v
      · have bound := nonedge v (.head _) he hv
        simp [he, Ne.symm he, Nat.mul_add]
        omega
      · have bound := (g.codegree_bounds ok u v he).1 hv
        simp [he, Ne.symm he, Nat.mul_add]
        omega


theorem walks_blocks {g : Graph 254} (p : Blocks g a c b) (u : Vert)
    (ends : List Vert) (l r : Nat)
    (hl : ∀ w ∈ p.left, ends.countP (g.adj w) = l)
    (hr : ∀ w ∈ p.right, ends.countP (g.adj w) = r) :
    total ends (g.commonCount u) = p.left.countP (g.adj u) * l +
      p.right.countP (g.adj u) * r := by
  let f (w : Vert) := if g.adj u w then ends.countP (g.adj w) else 0
  have expand : total ends (g.commonCount u) = total (p.left ++ p.right) f := by
    rw [← walks g u ends (p.left ++ p.right)]
    apply total_congr
    intro v _
    exact (p.partition.countP_eq _).symm
  rw [expand]
  have halve : total (p.left ++ p.right) f = total p.left f + total p.right f := by
    simp [total]
  rw [halve]
  congr 1
  · rw [← total_indicator]
    exact total_congr _ _ _ (fun w hw => by simp [f, hl w hw])
  · rw [← total_indicator]
    exact total_congr _ _ _ (fun w hw => by simp [f, hr w hw])

theorem Blocks.leftDegree {g : Graph 254} (p : Blocks g a c b)
    (u : Vert) (hu : u ∈ p.left) : g.degree u = a + b := by
  unfold Graph.degree
  rw [← p.partition.countP_eq, List.countP_append, (p.degreesLeft u hu).1, (p.degreesLeft u hu).2]

def Blocks.swap {g : Graph 254} (p : Blocks g a c b) : Blocks g c a b where
  left := p.right
  right := p.left
  partition := (List.perm_append_comm ..).trans p.partition
  leftSize := p.rightSize
  rightSize := p.leftSize
  degreesLeft w hw := ⟨(p.degreesRight w hw).2, (p.degreesRight w hw).1⟩
  degreesRight w hw := ⟨(p.degreesLeft w hw).2, (p.degreesLeft w hw).1⟩

theorem Blocks.leftVertex {g : Graph 254} (p : Blocks g a c b) :
    ∃ u, u ∈ p.left := by
  exact List.exists_mem_of_length_pos (by rw [p.leftSize]; decide)

theorem Blocks.counts {g : Graph 254} (p : Blocks g a c b)
    (u : Vert) (hu : u ∈ p.left) : p.left.count u = 1 ∧ p.right.count u = 0 := by
  have h := (p.partition.countP_eq (· == u))
  change (p.left ++ p.right).count u = (List.finRange 254).count u at h
  rw [List.count_append, (List.nodup_finRange 254).count_of_mem (List.mem_finRange u)] at h
  have pos := List.count_pos_iff.mpr hu
  omega

theorem Blocks.separate {g : Graph 254} (p : Blocks g a c b)
    (hu : u ∈ p.left) (hv : v ∈ p.right) : u ≠ v := by
  rintro rfl
  have := (p.counts u hu).2
  have := List.count_pos_iff.mpr hv
  omega

theorem Blocks.degreeBounds {g : Graph 254} (p : Blocks g a c b) : a ≤ 126 ∧ b ≤ 127 := by
  obtain ⟨u, hu⟩ := p.leftVertex
  obtain ⟨hl, hr⟩ := p.degreesLeft u hu
  have inside := split_count g u p.left
  have across := List.countP_le_length (p := g.adj u) (l := p.right)
  rw [(p.counts u hu).1, hl, p.leftSize] at inside
  rw [hr, p.rightSize] at across
  omega

private theorem mul_pred (k : Nat) : k * (k - 1) + k = k * k := by
  cases k with
  | zero => rfl
  | succ k => simp [Nat.mul_add]

theorem inside_walk_bound {g : Graph 254} (ok : g.check 63 64 = true)
    (p : Blocks g a c b) : insideBound a b := by
  obtain ⟨u, hu⟩ := p.leftVertex
  obtain ⟨hl, hr⟩ := p.degreesLeft u hu
  have cnt := (p.counts u hu).1
  have split := split_count g u p.left
  rw [cnt, hl, p.leftSize] at split
  have nOther : other g u p.left = 126 - a := by omega
  have lim := sum_bound g ok u p.left (a + b) 189 (fun v hv ne h => by
    simpa only [p.leftDegree v hv] using (g.codegree_bounds ok u v ne).2 h)
  have eqsum := walks_blocks p u p.left a b (fun v hv => (p.degreesLeft v hv).1)
      (fun v hv => (p.degreesRight v hv).1)
  rw [eqsum, nOther, p.leftDegree u hu, hl, hr, cnt] at lim
  simp only [Nat.one_mul] at lim
  have double : a + b + (a + b) = 2 * (a + b) := by omega
  rw [double, Nat.mul_comm 189 _, Nat.mul_comm (2 * (a + b)) _,
    ← mul_pred a, ← mul_pred b] at lim
  unfold insideBound
  omega

/-- Count the walks from a left vertex to all right vertices. The Cayley
case uses the stronger nonedge bound with cost 190 supplied by parity. -/
theorem across_walk_bound_of_nonedge {g : Graph 254} (ok : g.check 63 64 = true)
    (p : Blocks g a c b) (cost : Nat)
    (nonedge : ∀ u ∈ p.left, ∀ v ∈ p.right, g.adj u v = false →
      g.commonCount u v + cost ≤ (a + b) + (c + b)) :
    (a + c) * b + (127 - b) * cost ≤ 62 * b + (127 - b) * (a + c + 2 * b) := by
  obtain ⟨u, hu⟩ := p.leftVertex
  obtain ⟨hl, hr⟩ := p.degreesLeft u hu
  have cnt := (p.counts u hu).2
  have split := split_count g u p.right
  rw [cnt, hr, p.rightSize] at split
  have nOther : other g u p.right = 127 - b := by omega
  have lim := sum_bound g ok u p.right (c + b) cost (fun v hv _ h => by
    rw [p.leftDegree u hu]; exact nonedge u hu v hv h)
  have eqsum := walks_blocks p u p.right b c (fun v hv => (p.degreesLeft v hv).2)
      (fun v hv => (p.degreesRight v hv).2)
  rw [eqsum, nOther, p.leftDegree u hu, hl, hr, cnt] at lim
  have dsum : a + b + (c + b) = a + c + 2 * b := by omega
  simpa only [Nat.add_mul, Nat.zero_mul, Nat.zero_add, dsum,
    Nat.mul_comm cost _, Nat.mul_comm (a+c+2*b) _, Nat.mul_comm b c] using lim

private theorem across_walk_bound {g : Graph 254} (ok : g.check 63 64 = true)
    (p : Blocks g a c b) : acrossBound a c b := by
  apply across_walk_bound_of_nonedge ok p 189
  intro u hu v hv h
  simpa only [p.leftDegree u hu, p.swap.leftDegree v hv] using
    (g.codegree_bounds ok u v (p.separate hu hv)).2 h

/-- A graph satisfying the book bounds cannot have two equally sized regular
blocks with internal and cross degrees in the indicated residue classes. -/
theorem no_equitable_blocks {g : Graph 254} {h a c b : Nat}
    (hh : h = 7 ∨ h = 9) (hda : 2 * h ∣ a) (hdc : 2 * h ∣ c)
    (hr : b % h ≤ 1) (p : Blocks g a c b) : g.check 63 64 = false := by
  apply Bool.eq_false_iff.mpr
  intro ok
  exact excludes_degrees hh p.degreeBounds.1 p.swap.degreeBounds.1 p.degreeBounds.2 hda hdc hr
    ⟨inside_walk_bound ok p, inside_walk_bound ok p.swap, across_walk_bound ok p⟩

end BookRamsey.DegreeObstruction
