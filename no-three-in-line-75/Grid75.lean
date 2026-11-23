import Std

/-! Bounds for the no-three-in-line problem on the lattice {0,…,74}².

Two points per row give the upper bound 150. Prellberg's 148-point example
gives the lower bound. The unrestricted target is `Achievable 150`. -/

namespace Grid75

abbrev Point := Fin 75 × Fin 75

/-- Signed twice-area, using integer subtraction in both coordinates. -/
def det (a b c : Point) : Int :=
  ((b.1.val : Int) - a.1.val) * ((c.2.val : Int) - a.2.val) -
  ((b.2.val : Int) - a.2.val) * ((c.1.val : Int) - a.1.val)

/-- Picking three positions in increasing list order tests each triple once.
The zero-determinant condition is independent of the order of the three points. -/
def NoThree (s : List Point) : Prop :=
  ∀ ⦃a b c⦄, [a, b, c].Sublist s → det a b c ≠ 0

def Achievable (k : Nat) : Prop :=
  ∃ s : List Point, s.length = k ∧ s.Nodup ∧ NoThree s

/-- At most two selected points can lie on a given line. -/
theorem NoThree.line_bound {s : List Point} (valid : NoThree s) (onLine : Point → Bool)
    (col : ∀ a b c, onLine a → onLine b → onLine c → det a b c = 0) :
    (s.filter onLine).length ≤ 2 := by
  generalize eq : s.filter onLine = t
  rcases t with _ | ⟨a, _ | ⟨b, _ | ⟨c, tail⟩⟩⟩ <;> try simp
  have sub : [a, b, c].Sublist (s.filter onLine) := eq ▸ List.sublist_append_left _ tail
  have on {p} (hp : p ∈ [a, b, c]) := (List.mem_filter.mp (sub.subset hp)).2
  exact False.elim (valid (sub.trans List.filter_sublist)
    (col a b c (on (by simp)) (on (by simp)) (on (by simp))))

/-- The selected points whose indicated coordinate is i. -/
def fiber (coord : Point → Fin 75) (s : List Point) (i : Fin 75) : List Point :=
  s.filter fun p => coord p == i

private theorem fiber_bound (coord : Point → Fin 75)
    (axis : ∀ a b c, coord a = coord b → coord b = coord c → det a b c = 0)
    {s : List Point} (h : NoThree s) (i : Fin 75) : (fiber coord s i).length ≤ 2 := by
  apply h.line_bound
  intro a b c ha hb hc
  simp at ha hb hc
  exact axis a b c (ha.trans hb.symm) (hb.trans hc.symm)

private theorem cover (coord : Point → Fin 75) {s : List Point} (nd : s.Nodup) :
    s.length ≤ ((List.finRange 75).flatMap (fiber coord s)).length := by
  apply nd.length_le_of_subset
  intro p hp
  exact List.mem_flatMap.mpr ⟨coord p, List.mem_finRange _, by simp [fiber, hp]⟩

private theorem count_fibers (f : Fin 75 → List Point) (hb : ∀ i, (f i).length ≤ 2)
    (rows : List (Fin 75)) :
    (rows.flatMap f).length ≤ 2 * rows.length ∧
    ((rows.flatMap f).length = 2 * rows.length → ∀ i ∈ rows, (f i).length = 2) := by
  induction rows with
  | nil => simp
  | cons a t ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.mem_cons]
    have ha := hb a
    obtain ⟨ht, he⟩ := ih
    constructor
    · omega
    · rintro h i (rfl | hi)
      · omega
      · exact he (by omega) i hi

private theorem row_axis (a b c : Point) (h : a.2 = b.2) (h' : b.2 = c.2) :
    det a b c = 0 := by simp [det, h, h']

private theorem col_axis (a b c : Point) (h : a.1 = b.1) (h' : b.1 = c.1) :
    det a b c = 0 := by simp [det, h, h']

/-- The 75 rows cover the board, and each contains at most two chosen points. -/
theorem upper_bound {k : Nat} (h : Achievable k) : k ≤ 150 := by
  obtain ⟨s, rfl, nd, h⟩ := h
  exact Nat.le_trans (cover Prod.snd nd) (by
    simpa using (count_fibers _ (fiber_bound Prod.snd row_axis h) (List.finRange 75)).1)

/-- Reaching 150 uses both places in every row and, by the same count, every column. -/
theorem equality_forces_two_per_row_and_column {s : List Point} (size : s.length = 150)
    (nd : s.Nodup) (h : NoThree s) (i : Fin 75) :
    (fiber Prod.snd s i).length = 2 ∧ (fiber Prod.fst s i).length = 2 := by
  suffices H : ∀ (coord : Point → Fin 75), (∀ i, (fiber coord s i).length ≤ 2) →
      (fiber coord s i).length = 2 from
    ⟨H Prod.snd (fiber_bound _ row_axis h), H Prod.fst (fiber_bound _ col_axis h)⟩
  intro coord hb
  obtain ⟨le, eq⟩ := count_fibers _ hb (List.finRange 75)
  apply eq _ i (List.mem_finRange _)
  have lower := cover coord nd
  rw [List.length_finRange] at le ⊢
  omega

/-- Thomas Prellberg's first 74 × 74 example in Flammenkamp's database,
embedded in the lower 74 rows and columns.
https://wwwhomes.uni-bielefeld.de/achim/no3in/download/configurations/n74_rot4.few -/
def witness148 : List Point := [
  (25, 0), (45, 0), (44, 1), (54, 1), (22, 2), (40, 2), (15, 3), (69, 3),
  (3, 4), (18, 4), (30, 5), (50, 5), (36, 6), (46, 6), (40, 7), (50, 7),
  (19, 8), (55, 8), (11, 9), (53, 9), (37, 10), (44, 10), (32, 11), (64, 11),
  (21, 12), (25, 12), (14, 13), (27, 13), (51, 14), (60, 14), (42, 15), (70, 15),
  (16, 16), (57, 16), (39, 17), (53, 17), (8, 18), (69, 18), (1, 19), (65, 19),
  (9, 20), (17, 20), (45, 21), (61, 21), (14, 22), (71, 22), (5, 23), (7, 23),
  (26, 24), (30, 24), (61, 25), (73, 25), (34, 26), (49, 26), (6, 27), (60, 27),
  (0, 28), (21, 28), (1, 29), (10, 29), (49, 30), (68, 30), (15, 31), (38, 31),
  (35, 32), (62, 32), (2, 33), (7, 33), (17, 34), (47, 34), (31, 35), (41, 35),
  (10, 36), (67, 36), (6, 37), (63, 37), (32, 38), (42, 38), (26, 39), (56, 39),
  (66, 40), (71, 40), (11, 41), (38, 41), (35, 42), (58, 42), (5, 43), (24, 43),
  (63, 44), (72, 44), (52, 45), (73, 45), (13, 46), (67, 46), (24, 47), (39, 47),
  (0, 48), (12, 48), (43, 49), (47, 49), (66, 50), (68, 50), (2, 51), (59, 51),
  (12, 52), (28, 52), (56, 53), (64, 53), (8, 54), (72, 54), (4, 55), (65, 55),
  (20, 56), (34, 56), (16, 57), (57, 57), (3, 58), (31, 58), (13, 59), (22, 59),
  (46, 60), (59, 60), (48, 61), (52, 61), (9, 62), (41, 62), (29, 63), (36, 63),
  (20, 64), (62, 64), (18, 65), (54, 65), (23, 66), (33, 66), (27, 67), (37, 67),
  (23, 68), (43, 68), (55, 69), (70, 69), (4, 70), (58, 70), (33, 71), (51, 71),
  (19, 72), (29, 72), (28, 73), (48, 73)]

/-- A new point is admissible if it forms a nonzero determinant with each old pair. -/
theorem noThree_cons_of_det {a : Point} {s : List Point}
    (pairs : s.Pairwise (fun b c => det a b c ≠ 0)) (tail : NoThree s) : NoThree (a :: s) := by
  intro p q r sub
  cases sub with
  | cons _ sub => exact tail sub
  | cons_cons _ sub => exact pairs.forall_sublist sub

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem lower_bound : Achievable 148 := by
  refine ⟨witness148, by decide, by decide +kernel, ?_⟩
  iterate 148
    apply noThree_cons_of_det
    decide +kernel
  intro a b c sub
  cases sub

theorem maximum_in_range : ∃ m, Achievable m ∧ (∀ k, Achievable k → k ≤ m) ∧
    (m = 148 ∨ m = 149 ∨ m = 150) := by
  by_cases h150 : Achievable 150
  · exact ⟨150, h150, fun _ => upper_bound, by simp⟩
  by_cases h149 : Achievable 149
  · refine ⟨149, h149, ?_, by simp⟩
    intro k hk
    have := upper_bound hk
    grind
  · refine ⟨148, lower_bound, ?_, by simp⟩
    intro k hk
    have := upper_bound hk
    grind

/-! ## Further results about lines and symmetries -/

/-- A vertical line has slope `none`. Every other slope is an exact rational. -/
private def slope (a b : Point) : Option Rat :=
  if b.1 = a.1 then none
  else some (Rat.divInt ((b.2.val : Int) - a.2.val) ((b.1.val : Int) - a.1.val))

private theorem slope_eq_of_collinear (a b c : Point) (hb : b ≠ a) (hc : c ≠ a)
    (col : det a b c = 0) : slope a b = slope a c := by
  unfold det at col
  by_cases vb : b.1 = a.1 <;> by_cases vc : c.1 = a.1
  · simp [slope, vb, vc]
  · simp [vb, Int.mul_eq_zero] at col
    grind [Prod.ext_iff, Fin.ext_iff]
  · simp [vc, Int.mul_eq_zero] at col
    grind [Prod.ext_iff, Fin.ext_iff]
  · simp only [slope, vb, vc, ite_false, Option.some.injEq]
    apply (Rat.divInt_eq_divInt_iff (by grind [Fin.ext_iff]) (by grind [Fin.ext_iff])).mpr
    grind

/-- Give each rational slope an index in the bitset used by the search checker. -/
private def slopeKey (a b : Point) : Nat :=
  match slope a b with
  | none => 0
  | some r => 1 + 150 * r.den + (r.num + 74).toNat

/-- A bit records whether the corresponding slope has appeared. -/
private def fresh (seen : Nat) : List Nat → Bool
  | [] => true
  | k :: ks => !seen.testBit k && fresh (seen ||| (1 <<< k)) ks

private theorem fresh_sound {ks : List Nat} {seen : Nat} (h : fresh seen ks = true) :
    ks.Nodup ∧ ∀ k ∈ ks, seen.testBit k = false := by
  induction ks generalizing seen with
  | nil => simp
  | cons k ks ih =>
    obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨nd, unused⟩ := ih tail
    have U (j : Nat) (hj : j ∈ ks) := unused j hj
    simp only [Nat.testBit_or, Bool.or_eq_false_iff] at U
    constructor
    · refine List.nodup_cons.mpr ⟨?_, nd⟩
      intro hk
      have hf := (U k hk).2
      simp [Nat.shiftLeft_eq] at hf
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · simpa using head
      · exact (U _ hj).1

/-- At each anchor, check that the slopes to all later points are distinct. -/
def slopesOK : List Point → Bool
  | [] => true
  | a :: t => fresh 0 (t.map (slopeKey a)) && slopesOK t

theorem slopes_sound {s : List Point} (nd : s.Nodup) (ok : slopesOK s = true) :
    NoThree s := by
  intro a b c sub
  induction s with
  | nil => cases sub
  | cons p t ih =>
    obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp ok
    obtain ⟨hp, nt⟩ := List.nodup_cons.mp nd
    cases sub with
    | cons _ sub => exact ih nt tail sub
    | cons_cons _ sub =>
      have hb : b ≠ a := fun e => hp (e ▸ sub.subset (by simp))
      have hc : c ≠ a := fun e => hp (e ▸ sub.subset (by simp))
      have pair := (fresh_sound head).1.sublist (sub.map (slopeKey a))
      intro col
      simp [slopeKey, slope_eq_of_collinear a b c hb hc col] at pair

/-- Three distinct selected points have nonzero determinant in any order. -/
theorem NoThree.exclude_triple {s : List Point} (hs : NoThree s) {a b c : Point}
    (nd : [a, b, c].Nodup) (h : det a b c = 0)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) : False := by
  let marked := fun p : Point => decide (p ∈ [a, b, c])
  have bound := hs.line_bound marked (by
    intro x y z hx hy hz
    simp [marked] at hx hy hz
    grind [det])
  have sub : [a, b, c] ⊆ s.filter marked := by
    intro p hp
    exact List.mem_filter.mpr ⟨by simp at hp; grind, by simpa [marked] using hp⟩
  have lower := nd.length_le_of_subset sub
  simp at lower
  omega

private theorem witness_fibers : ∀ i : Fin 75, i.val < 74 →
    (fiber Prod.snd witness148 i).length = 2 ∧ (fiber Prod.fst witness148 i).length = 2 := by
  set_option maxRecDepth 10000 in decide +kernel

/-- With this witness fixed, the last row and column force (74, 74) as the
only possible addition. Two marked points on its diagonal already block it. -/
theorem witness_cannot_extend (q : Point) : ¬ NoThree (q :: witness148) := by
  intro valid
  have edge (coord : Point → Fin 75)
      (axis : ∀ a b c, coord a = coord b → coord b = coord c → det a b c = 0)
      (sat : ∀ i : Fin 75, i.val < 74 → (fiber coord witness148 i).length = 2) :
      (coord q).val = 74 := by
    have b := fiber_bound coord axis valid (coord q)
    have eq : fiber coord (q :: witness148) (coord q) =
        q :: fiber coord witness148 (coord q) := by simp [fiber]
    rw [eq, List.length_cons] at b
    have lt := (coord q).isLt
    by_cases h : (coord q).val < 74
    · have := sat (coord q) h
      omega
    · omega
  have x := edge Prod.fst col_axis (fun i hi => (witness_fibers i hi).2)
  have y := edge Prod.snd row_axis (fun i hi => (witness_fibers i hi).1)
  have corner : q = (74, 74) := Prod.ext (Fin.ext x) (Fin.ext y)
  have pair : [(16, 16), (57, 57)].Sublist witness148 := by
    set_option maxRecDepth 10000 in decide +kernel
  apply valid (pair.cons_cons q)
  rw [corner]
  decide

/-- Counterclockwise rotation around the grid centre (37, 37). -/
def quarterTurn (p : Point) : Point := (p.2.rev, p.1)

/-- One quadrant, including one of its two bounding rays. -/
private def sector (p : Point) : Bool := decide (37 < p.1.val ∧ 37 ≤ p.2.val)

private def center : Point := (37, 37)

private theorem sector_partition (s : List Point) :
    s.length = s.countP sector + s.countP (sector ∘ quarterTurn)
      + s.countP ((sector ∘ quarterTurn) ∘ quarterTurn)
      + s.countP (((sector ∘ quarterTurn) ∘ quarterTurn) ∘ quarterTurn)
      + s.count center := by
  induction s with
  | nil => rfl
  | cons p ps ih =>
    rw [List.length_cons, List.count_cons]
    simp only [List.countP_cons]
    have point_partition : ∀ x y : Fin 75,
        let a : Point := (x, y)
        (if sector a then 1 else 0) + (if sector (quarterTurn a) then 1 else 0)
        + (if sector (quarterTurn (quarterTurn a)) then 1 else 0)
        + (if sector (quarterTurn (quarterTurn (quarterTurn a))) then 1 else 0)
        + (if a == center then 1 else 0) = 1 := by
      set_option maxRecDepth 5000 in
        decide +kernel
    rcases p with ⟨x, y⟩
    have hp := point_partition x y
    dsimp only at hp
    simp only [Function.comp_apply]
    omega

/-- A finite set invariant under the quarter-turn consists of four-point
orbits together with the centre if present. -/
private theorem quarterTurn_count {s : List Point}
    (invariant : (s.map quarterTurn).Perm s) :
    s.length = 4 * s.countP sector + s.count center := by
  have invariantCount (f : Point → Bool) : s.countP (f ∘ quarterTurn) = s.countP f := by
    simpa only [List.countP_map] using invariant.countP_eq f
  have h := sector_partition s
  rw [invariantCount ((sector ∘ quarterTurn) ∘ quarterTurn),
    invariantCount (sector ∘ quarterTurn), invariantCount sector] at h
  omega

/-- In particular no set of 150 distinct lattice points is invariant under
quarter-turn about the centre of the 75 by 75 grid. -/
theorem no_quarterTurn_150 {s : List Point} (distinct : s.Nodup)
    (invariant : (s.map quarterTurn).Perm s) : s.length ≠ 150 := by
  have h := quarterTurn_count invariant
  have hc := List.nodup_iff_count.mp distinct center
  omega

end Grid75
