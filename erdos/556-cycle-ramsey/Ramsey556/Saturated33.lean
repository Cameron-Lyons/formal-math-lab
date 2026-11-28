import Ramsey556.DenseCore
import Ramsey556.PathDensity
import Ramsey556.BicliqueObstruction

namespace Ramsey556.Saturated33

/-- In a saturated coloring every pair of different vertices either has a
red edge or an eight-edge red path between them. -/
theorem red_distances {c : Coloring 33} (sat : PathSaturated c) {x y : Fin 33} (ne : x ≠ y) :
    c.edge x y = 0 ∨ HasPath8In c 0 x y := by
  by_cases h : c.edge x y = 0
  · exact .inl h
  · exact .inr (sat x y ne _ (by omega))

private theorem red_of_separate {c : Coloring 33} (sat : PathSaturated c)
    {x y : Fin 33} (gap : ¬ ColorJoined c 1 x y) : c.edge x y = 0 := by
  have ne : x ≠ y := fun e => gap (e ▸ .refl _)
  have notBlue : c.edge x y ≠ 1 := fun eq => gap (.edge eq)
  apply Classical.byContradiction
  intro nonred
  exact gap (sat _ _ ne 1 (by omega)).joined

private theorem no_gap {c : Coloring 33} (free : ¬ HasMonoC9 c) (sat : PathSaturated c)
    (a : Fin 4 → Fin 33) (b : Fin 16 → Fin 33)
    (ai : ∀ ⦃i j⦄, a i = a j → i = j) (bi : ∀ ⦃i j⦄, b i = b j → i = j)
    (gap : ∀ i j, ¬ ColorJoined c 1 (a i) (b j)) : False := by
  have ne (i j) : a i ≠ b j := fun eq => gap i j (eq ▸ .refl _)
  apply free
  apply BicliqueObstruction.hasMonoC9_of_four_sixteen c 0 a b (@ai) (@bi) ne
  exact fun i j => red_of_separate sat (gap i j)

private theorem no_three_twenty_gap {c : Coloring 33} (free : ¬ HasMonoC9 c) (sat : PathSaturated c)
    (a : Fin 3 → Fin 33) (b : Fin 20 → Fin 33)
    (ai : ∀ ⦃i j⦄, a i = a j → i = j) (bi : ∀ ⦃i j⦄, b i = b j → i = j)
    (gap : ∀ i j, ¬ ColorJoined c 1 (a i) (b j)) : False :=
  free (BicliqueObstruction.hasMonoC9_of_three_twenty c 0 a b (@ai) (@bi)
    (fun i j e => gap i j (e ▸ .refl _)) (fun i j => red_of_separate sat (gap i j)))

private theorem choose_from {m n} (xs : List (Fin n)) (nd : xs.Nodup) (large : m ≤ xs.length) :
    ∃ f : Fin m → Fin n, (∀ ⦃i j⦄, f i = f j → i = j) ∧ ∀ i, f i ∈ xs := by
  let f (i : Fin m) := xs[i.val]'(by omega)
  exact ⟨f,fun {_ _} h => Fin.ext (nd.eq_of_getElem_eq _ _ h),fun _ => List.getElem_mem ..⟩

private theorem union_le {α} (l : List α) (p q : α → Bool) :
    l.countP (fun x => p x || q x) ≤ l.countP p + l.countP q := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    cases p a <;> cases q a <;> simp <;> omega

/-- At least thirty-one vertices belong to a single blue component in the
path-saturated normal form. -/
theorem blue_giant {c : Coloring 33} (free : ¬ HasMonoC9 c) (sat : PathSaturated c) :
    ∃ (z : Fin 33) (v : Fin 31 → Fin 33), (∀ ⦃i j⦄, v i = v j → i = j) ∧
      ∀ i, ColorJoined c 1 z (v i) := by
  classical
  let xs := List.finRange 33
  let a (i : Fin 4) : Fin 33 := ⟨i.val,by omega⟩
  have ai : ∀ ⦃i j⦄, a i = a j → i = j := fun {_ _} h => Fin.ext (congrArg (fun x : Fin 33 => x.val) h)
  let cc (i : Fin 4) (x) := decide (ColorJoined c 1 (a i) x)
  let p (x) := cc 0 x || cc 1 x || cc 2 x || cc 3 x
  let far := xs.filter (fun x => !(p x))
  have far_small : far.length ≤ 15 := by
    apply Nat.le_of_not_gt
    intro big
    obtain ⟨b,bi,bm⟩ := choose_from far ((List.nodup_finRange _).filter _) (by omega : 16 ≤ far.length)
    apply no_gap free sat a b (@ai) (@bi)
    intro i j
    have hf : p (b j) = false := by simpa [far,xs] using bm j
    simp [p,cc] at hf
    have ix : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases ix with rfl|rfl|rfl|rfl <;> simp_all
  have total : xs.countP p + far.length = 33 := by
    simpa [xs,far,← List.countP_eq_length_filter] using (List.length_eq_countP_add_countP p (l := xs)).symm
  have U := union_le xs (fun x => cc 0 x || cc 1 x || cc 2 x) (cc 3)
  have V := union_le xs (fun x => cc 0 x || cc 1 x) (cc 2)
  have W := union_le xs (cc 0) (cc 1)
  change xs.countP p ≤ _ at U
  obtain ⟨t,large⟩ : ∃ t : Fin 4, 4 ≤ xs.countP (cc t) := by
    by_cases h0 : 4 ≤ xs.countP (cc 0)
    · exact ⟨0,h0⟩
    by_cases h1 : 4 ≤ xs.countP (cc 1)
    · exact ⟨1,h1⟩
    by_cases h2 : 4 ≤ xs.countP (cc 2)
    · exact ⟨2,h2⟩
    exact ⟨3,by omega⟩
  let inside := xs.filter (cc t)
  let outside := xs.filter (fun x => !(cc t x))
  have part : inside.length + outside.length = 33 := by
    simpa [inside,outside,xs,← List.countP_eq_length_filter] using
      (List.length_eq_countP_add_countP (cc t) (l := xs)).symm
  have atLeast : 4 ≤ inside.length := by simpa [inside,← List.countP_eq_length_filter] using large
  have ind : inside.Nodup := (List.nodup_finRange _).filter _
  have ond : outside.Nodup := (List.nodup_finRange _).filter _
  have yes (x) (h : x ∈ inside) : ColorJoined c 1 (a t) x := by simpa [inside,xs,cc] using h
  have no (x) (h : x ∈ outside) : ¬ ColorJoined c 1 (a t) x := by simpa [outside,xs,cc] using h
  have sep (x) (hx : x ∈ inside) (y) (hy : y ∈ outside) : ¬ ColorJoined c 1 x y :=
    fun h => no y hy ((yes x hx).trans h)
  have big : 31 ≤ inside.length := by
    apply Nat.le_of_not_gt
    intro small
    by_cases twenty : 20 ≤ inside.length
    · obtain ⟨u,ui,um⟩ := choose_from outside ond (by omega : 3 ≤ outside.length)
      obtain ⟨v,vi,vm⟩ := choose_from inside ind twenty
      exact no_three_twenty_gap free sat u v (@ui) (@vi) (fun i j q => sep _ (vm j) _ (um i) q.symm)
    by_cases enough : 16 ≤ inside.length
    · obtain ⟨u,ui,um⟩ := choose_from outside ond (by omega : 4 ≤ outside.length)
      obtain ⟨v,vi,vm⟩ := choose_from inside ind enough
      exact no_gap free sat u v (@ui) (@vi) (fun i j q => sep _ (vm j) _ (um i) q.symm)
    · obtain ⟨u,ui,um⟩ := choose_from inside ind atLeast
      obtain ⟨v,vi,vm⟩ := choose_from outside ond (by omega : 16 ≤ outside.length)
      exact no_gap free sat u v (@ui) (@vi) (fun i j => sep _ (um i) _ (vm j))
  obtain ⟨v,vi,vm⟩ := choose_from inside ind big
  exact ⟨a t,v,@vi,fun i => yes _ (vm i)⟩

/-- The ordered, saturated case suffices for K₃₃. The red graph then
has at least 176 edges and diameter at most eight; the blue graph has
a component on at least 31 vertices. -/
theorem k33_iff_ordered_saturated :
    K33Claim ↔ ∀ c : Coloring 33, PathSaturated c → 176 ≤ CycleStructure.tally c 0 →
      CycleStructure.tally c 2 ≤ CycleStructure.tally c 1 → CycleStructure.tally c 1 ≤ CycleStructure.tally c 0 →
      (∃ (z : Fin 33) (v : Fin 31 → Fin 33), (∀ ⦃i j⦄, v i = v j → i = j) ∧ ∀ i, ColorJoined c 1 z (v i)) →
      HasMonoC9 c := by
  refine ⟨fun h c _ _ _ _ _ => h c, ?_⟩
  intro h c
  apply Classical.byContradiction
  intro free
  obtain ⟨d,df,sat,many,gb,br⟩ := CycleStructure.ordered_saturated_counterexample c free
  exact df (h d sat many gb br (blue_giant df sat))

private theorem prefix_bound {α} (r : α → α → Bool) (xs ys : List α) (small : xs.length + ys.length ≤ 33) :
    DeletionCount.pairs r (xs++ys) ≤ 33*xs.length + DeletionCount.pairs r ys := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons] at small ⊢
    have sub := ih (by omega)
    have count : (xs++ys).countP (r x) ≤ 33 := Nat.le_trans List.countP_le_length
      (by simp only [List.length_append]; omega)
    simp only [List.cons_append,DeletionCount.pairs]
    omega

/-- In the fully saturated form the blue component spans all 33 vertices.
A vertex missing from the giant would send red edges to the entire giant.
Its red graph therefore has no eight-vertex path and too few edges. -/
theorem blue_connected {c : Coloring 33} (free : ¬ HasMonoC9 c) (sat : PathSaturated c)
    (many : 176 ≤ CycleStructure.tally c 0) : ∀ x y, ColorJoined c 1 x y := by
  classical
  obtain ⟨z,v,vi,links⟩ := blue_giant free sat
  have all (y : Fin 33) : ColorJoined c 1 z y := by
    apply Classical.byContradiction
    intro remote
    let xs := List.finRange 33
    let pred (u) := decide (ColorJoined c 1 z u)
    let inside := xs.filter pred
    let outside := xs.filter (fun u => !(pred u))
    have perm : (outside++inside).Perm xs :=
      (List.perm_append_comm ..).trans (List.filter_append_perm pred xs)
    have sizes : outside.length+inside.length=33 := by
      simpa only [List.length_append,xs,List.length_finRange] using perm.length_eq
    have nd : ((List.finRange 31).map v).Nodup :=
      (List.nodup_finRange 31).map v (fun _ _ ne eq => ne (vi eq))
    have large : 31 ≤ inside.length := by
      have sub : ∀ ⦃u⦄, u∈(List.finRange 31).map v → u∈inside := by
        rintro u h
        obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
        exact List.mem_filter.mpr ⟨List.mem_finRange _,decide_eq_true (links i)⟩
      simpa only [List.length_map,List.length_finRange] using nd.length_le_of_subset sub
    have apart (w) (hw : w∈inside) : ¬ ColorJoined c 1 y w := by
      have zw : ColorJoined c 1 z w := of_decide_eq_true (List.mem_filter.mp hw).2
      exact fun yw => remote (zw.trans yw.symm)
    let r := colorAdjacent c 0
    have pathFree : ¬ Nonempty (PathDensity.Path r inside 8) := by
      rintro ⟨p⟩
      apply free (closeC9Through c 0 (fun i => p.vertex i.val) y ?_ ?_ ?_ ?_ ?_)
      · exact fun {_ _} eq => Fin.ext (p.inj _ _ (by omega) (by omega) eq)
      · exact fun i eq => apart _ (p.mem _ i.isLt) (eq ▸ .refl _)
      · intro i hi
        exact (of_decide_eq_true (p.edges i.val hi) : _ ∧ _).2
      · exact red_of_separate sat (apart _ (p.mem 0 (by decide)))
      · exact red_of_separate sat (apart _ (p.mem 7 (by decide)))
    have cap := PathDensity.edge_bound r (DeletionCount.adjacent_sym c 0)
      (fun x => by simp [r,colorAdjacent]) inside ((List.nodup_finRange _).filter _) pathFree
    have total := prefix_bound r outside inside (by omega)
    rw [DeletionCount.perm r (DeletionCount.adjacent_sym c 0) perm] at total
    change colorEdgeCount c 0 ≤ _ at total
    rw [colorEdgeCount33_eq_tally] at total
    omega
  exact fun x y => (all x).symm.trans (all y)

/-- It suffices to test fully saturated, size-ordered colorings with red
and blue both connected. Every pair has a red edge or a red eight-edge path. -/
theorem k33_iff_ordered_saturated_connected_blue :
    K33Claim ↔ ∀ c : Coloring 33, PathSaturated c → 176 ≤ CycleStructure.tally c 0 →
      CycleStructure.tally c 2 ≤ CycleStructure.tally c 1 → CycleStructure.tally c 1 ≤ CycleStructure.tally c 0 →
      (∀ x y, ColorJoined c 1 x y) → HasMonoC9 c := by
  refine ⟨fun h c _ _ _ _ _ => h c, ?_⟩
  intro h c
  apply Classical.byContradiction
  intro free
  obtain ⟨d,df,sat,many,gb,br⟩ := CycleStructure.ordered_saturated_counterexample c free
  exact df (h d sat many gb br (blue_connected df sat many))

end Ramsey556.Saturated33
