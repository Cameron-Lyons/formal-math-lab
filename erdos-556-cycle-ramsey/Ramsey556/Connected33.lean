import Ramsey556.CycleStructure
import Ramsey556.BicliqueObstruction
import Ramsey556.VertexSets

namespace Ramsey556

/-- All three monochromatic graphs span a single component each. -/
def AllColorsConnected {n} (c : Coloring n) : Prop := ∀ k x y, ColorJoined c k x y

namespace Connected33
open CycleStructure

/-- If an edge crosses a component cut of color r, repainting it r must
disconnect its endpoints in the old color. This is the extremality property
used below. -/
private def BridgesOnCuts {n} (c : Coloring n) : Prop :=
  ∀ x y r, ¬ ColorJoined c r x y → ¬ ColorJoined (paint c x y r) (c.edge x y) x y

private def triples (n : Nat) : List (Fin 3 × Fin n × Fin n) :=
  (List.finRange 3).flatMap fun k => (List.finRange n).flatMap fun x =>
    (List.finRange n).map fun y => (k,x,y)

private noncomputable def disconnectedCount {n} (c : Coloring n) : Nat := by
  classical exact (triples n).countP fun (k,x,y) => decide (¬ ColorJoined c k x y)

private theorem count_strict {α} (p q : α → Bool) (less : ∀ z, p z = true → q z = true)
    (xs : List α) : xs.countP p ≤ xs.countP q ∧
    ((∃ z ∈ xs, p z = false ∧ q z = true) → xs.countP p < xs.countP q) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have order := less x
    simp only [List.countP_cons, List.mem_cons]
    constructor
    · cases a : p x <;> cases b : q x <;> simp_all <;> omega
    · rintro ⟨z,hz,pz,qz⟩
      rcases hz with rfl | hz
      · simp only [pz,qz,↓reduceIte,Bool.false_eq_true,Nat.add_zero]
        omega
      · have := ih.2 ⟨z,hz,pz,qz⟩
        cases a : p x <;> cases b : q x <;> simp_all <;> omega

private theorem preserved_by_paint {n} (c : Coloring n) (x y : Fin n) (r : Fin 3)
    (alternate : ColorJoined (paint c x y r) (c.edge x y) x y) (k : Fin 3) (a b : Fin n)
    (old : ColorJoined c k a b) : ColorJoined (paint c x y r) k a b := by
  induction old with
  | refl a => exact .refl _
  | @edge u v e =>
    by_cases hit : samePair x y u v
    · rcases hit with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · rw [← e]; exact alternate
      · rw [← e,c.symm u v]; exact alternate.symm
    · exact .edge (by simpa [paint,hit] using e)
  | trans _ _ p q => exact .trans p q

private theorem optimal {n} (c : Coloring n) (free : ¬ HasMonoC9 c) :
    ∃ d : Coloring n, (¬ HasMonoC9 d) ∧ BridgesOnCuts d := by
  classical
  generalize key : disconnectedCount c = w
  induction w using Nat.strongRecOn generalizing c with
  | ind w ih =>
    by_cases h : BridgesOnCuts c
    · exact ⟨c,free,h⟩
    unfold BridgesOnCuts at h
    simp only [Classical.not_forall] at h
    obtain ⟨x,y,r,diff,nn⟩ := h
    have alternate := Classical.byContradiction nn
    let d := paint c x y r
    have gained : ColorJoined d r x y := .edge (by simp [d,paint,samePair])
    have neFree : ¬ HasMonoC9 d := fun made => diff (path_of_paint free made).joined
    have strict : disconnectedCount d < disconnectedCount c := by
      unfold disconnectedCount
      apply (count_strict _ _ ?_ _).2
      · exact ⟨(r,x,y), by simp [triples], by simp [gained], by simp [diff]⟩
      · rintro ⟨k,a,b⟩
        simp only [decide_eq_true_eq]
        exact fun nd inC => nd (preserved_by_paint c x y r alternate k a b inC)
    rw [key] at strict
    exact ih _ strict d neFree rfl

private theorem unchanged {n} (c : Coloring n) (x y r) {a b : Fin n}
    (h : ¬ samePair x y a b) : (paint c x y r).edge a b = c.edge a b := by simp [paint,h]

/-- Distinct neighbors reached by bridges of color k from a common vertex
have no edge of color k between them. -/
private theorem independent_neighbors {n} {c : Coloring n} (opt : BridgesOnCuts c)
    (x u v : Fin n) (r k : Fin 3) (du : ¬ ColorJoined c r x u) (dv : ¬ ColorJoined c r x v)
    (ne : u ≠ v) (hu : c.edge x u = k) (hv : c.edge x v = k) : c.edge u v ≠ k := by
  intro uv
  have xu : x ≠ u := fun eq => du (eq ▸ .refl _)
  have xv : x ≠ v := fun eq => dv (eq ▸ .refl _)
  apply opt x u r du
  rw [hu]
  have a : ¬ samePair x u x v := by simp [samePair,Ne.symm ne,xu]
  have b : ¬ samePair x u v u := by simp [samePair,Ne.symm xv,Ne.symm ne]
  exact .trans (.edge ((unchanged c x u r a).trans hv))
    (.edge ((unchanged c x u r b).trans ((c.symm _ _).trans uv)))

/-- No monochromatic rectangle can cross the component cut. -/
private theorem no_rectangle {n} {c : Coloring n} (opt : BridgesOnCuts c) {x z u v : Fin n}
    {r k : Fin 3} (cut : ¬ ColorJoined c r x u)
    (xz : x ≠ z) (uv : u ≠ v) (xu : x ≠ u) (xv : x ≠ v) (zu : z ≠ u)
    (a : c.edge x u = k) (b : c.edge x v = k)
    (e : c.edge z u = k) (f : c.edge z v = k) : False := by
  apply opt x u r cut
  rw [a]
  have h1 : ¬ samePair x u x v := by simp [samePair,xu,Ne.symm uv]
  have h2 : ¬ samePair x u v z := by simp [samePair,Ne.symm xv,Ne.symm uv]
  have h3 : ¬ samePair x u z u := by simp [samePair,Ne.symm xz,zu]
  exact .trans (.edge ((unchanged c x u r h1).trans b))
    (.trans (.edge ((unchanged c x u r h2).trans ((c.symm _ _).trans f)))
      (.edge ((unchanged c x u r h3).trans e)))

private def leftRow (t : Fin 6) : Fin 3 := #v[0,0,1,0,0,1][t]
private def rightRow (t : Fin 6) : Fin 3 := #v[1,2,2,1,2,2][t]
private def hue (r : Fin 3) (t : Fin 6) : Fin 3 := if t.val < 3 then r+1 else r+2

private theorem pickPair : ∀ r a b c : Fin 3, a ≠ r → b ≠ r → c ≠ r →
    ∃ t : Fin 6, (#v[a,b,c])[leftRow t] = hue r t ∧ (#v[a,b,c])[rightRow t] = hue r t := by decide

private theorem two_columns (f : Fin 7 → Fin 6) : ∃ i j, i ≠ j ∧ f i = f j := by
  apply Classical.byContradiction
  intro no
  have inj {i j} (eq : f i = f j) : i = j := by
    apply Classical.byContradiction
    exact fun ne => no ⟨i,j,ne,eq⟩
  have nd : ((List.finRange 7).map f).Nodup := (List.nodup_finRange 7).map f (fun _ _ h e => h (inj e))
  have bad := nd.length_le_of_subset (l₂ := List.finRange 6) (fun {_} _ => List.mem_finRange _)
  simp at bad

private theorem three_seven {c : Coloring 33} (opt : BridgesOnCuts c) (r : Fin 3)
    (a : Fin 3 → Fin 33) (b : Fin 7 → Fin 33)
    (ai : ∀ ⦃i j⦄, a i = a j → i = j) (bi : ∀ ⦃i j⦄, b i = b j → i = j)
    (apart : ∀ i j, ¬ ColorJoined c r (a i) (b j)) : False := by
  classical
  have miss (i j) : c.edge (a i) (b j) ≠ r := fun e => apart i j (.edge e)
  have select (j) : ∃ t : Fin 6, c.edge (a (leftRow t)) (b j) = hue r t ∧
      c.edge (a (rightRow t)) (b j) = hue r t := by
    obtain ⟨t,ht⟩ := pickPair r _ _ _ (miss 0 j) (miss 1 j) (miss 2 j)
    have read (i : Fin 3) : (#v[c.edge (a 0) (b j),c.edge (a 1) (b j),c.edge (a 2) (b j)])[i] =
        c.edge (a i) (b j) := by
      have z : i=0 ∨ i=1 ∨ i=2 := by omega
      rcases z with rfl|rfl|rfl <;> rfl
    exact ⟨t,by simpa only [read] using ht⟩
  let tag j := (select j).choose
  obtain ⟨i,j,ne,eq⟩ := two_columns tag
  have hi := (select i).choose_spec
  have hj := (select j).choose_spec
  change _ = hue r (tag i) ∧ _ = hue r (tag i) at hi
  change _ = hue r (tag j) ∧ _ = hue r (tag j) at hj
  change c.edge (a (leftRow (tag i))) (b i) = _ ∧ c.edge (a (rightRow (tag i))) (b i) = _ at hi
  rw [eq] at hi
  have disj (u v) : a u ≠ b v := fun e => apart u v (e ▸ .refl _)
  exact no_rectangle opt (apart _ i)
    (fun e => (show ∀ t, leftRow t ≠ rightRow t by decide) _ (ai e)) (fun e => ne (bi e))
    (disj _ _) (disj _ _) (disj _ _) hi.1 hj.1 hi.2 hj.2

private theorem many_neighbors {c : Coloring 33} (free : ¬ HasMonoC9 c) (opt : BridgesOnCuts c)
    (r : Fin 3) (x : Fin 33) (ys : List (Fin 33)) (nd : ys.Nodup) (large : 31 ≤ ys.length)
    (apart : ∀ y ∈ ys, ¬ ColorJoined c r x y) : False := by
  let first (y) := c.edge x y == r+1
  obtain ⟨b,hb⟩ := large_side ys first 15 (by omega)
  obtain ⟨u,inj,mem⟩ := select_vertices _ (nd.filter _) 16 hb
  let k := if b then r+1 else r+2
  have hy (i) : u i ∈ ys := (List.mem_filter.mp (mem i)).1
  have hk (i) : c.edge x (u i) = k := by
    have ne : c.edge x (u i) ≠ r := fun e => apart _ (hy i) (.edge e)
    have ht : (c.edge x (u i) == r+1) = b := beq_iff_eq.mp (List.mem_filter.mp (mem i)).2
    exact (show ∀ r s : Fin 3, ∀ b : Bool, s ≠ r → (s == r+1) = b →
      s = (if b then r+1 else r+2) by decide) _ _ _ ne ht
  apply free
  apply hasMonoC9_of_independent16 twoColorOctets16 c u (@inj) k
  exact fun i j ne => independent_neighbors opt x _ _ r k (apart _ (hy i)) (apart _ (hy j))
    (fun h => ne (inj h)) (hk i) (hk j)

private theorem cut_impossible {c : Coloring 33} (free : ¬ HasMonoC9 c) (opt : BridgesOnCuts c)
    (r : Fin 3) (xs ys : List (Fin 33)) (xn : xs.Nodup) (yn : ys.Nodup)
    (total : xs.length + ys.length = 33) (order : xs.length ≤ ys.length) (present : xs ≠ [])
    (apart : ∀ x ∈ xs, ∀ y ∈ ys, ¬ ColorJoined c r x y) : False := by
  by_cases small : xs.length < 3
  · exact many_neighbors free opt r (xs.head present) ys yn (by omega) (apart _ (List.head_mem present))
  obtain ⟨a,ai,am⟩ := select_vertices xs xn 3 (by omega)
  obtain ⟨b,bi,bm⟩ := select_vertices ys yn 7 (by omega)
  exact three_seven opt r a b (@ai) (@bi) (fun i j => apart _ (am i) _ (bm j))

private theorem connected_of_optimal {c : Coloring 33} (free : ¬ HasMonoC9 c) (opt : BridgesOnCuts c) :
    AllColorsConnected c := by
  classical
  intro r u v
  apply Classical.byContradiction
  intro miss
  let side (x) := decide (ColorJoined c r u x)
  let cell (b : Bool) := (List.finRange 33).filter (fun x => side x == b)
  have total : (cell true).length + (cell false).length = 33 := by
    simpa [cell,List.countP_eq_length_filter] using (List.length_eq_countP_add_countP side (l := List.finRange 33)).symm
  have nd (b) : (cell b).Nodup := (List.nodup_finRange _).filter _
  have ht : u ∈ cell true := by simp [cell,side,ColorJoined.refl]
  have hf : v ∈ cell false := by simp [cell,side,miss]
  have cut (x) (hx : x ∈ cell true) (y) (hy : y ∈ cell false) : ¬ ColorJoined c r x y := by
    have ox : ColorJoined c r u x := by simpa [cell,side] using hx
    have oy : ¬ ColorJoined c r u y := by simpa [cell,side] using hy
    exact fun h => oy (ox.trans h)
  by_cases order : (cell true).length ≤ (cell false).length
  · exact cut_impossible free opt r _ _ (nd _) (nd _) total order (List.ne_nil_of_mem ht) cut
  · exact cut_impossible free opt r _ _ (nd _) (nd _) (by omega) (by omega) (List.ne_nil_of_mem hf)
      (fun y hy x hx h => cut x hx y hy h.symm)

/-- If a counterexample exists, there is one with all three colors connected. -/
theorem connected_counterexample (c : Coloring 33) (free : ¬ HasMonoC9 c) :
    ∃ d : Coloring 33, (¬ HasMonoC9 d) ∧ AllColorsConnected d := by
  obtain ⟨d,df,opt⟩ := optimal c free
  exact ⟨d,df,connected_of_optimal df opt⟩

theorem k33_iff_connected :
    K33Claim ↔ ∀ c : Coloring 33, AllColorsConnected c → HasMonoC9 c := by
  refine ⟨fun h c _ => h c, ?_⟩
  intro h c
  apply Classical.byContradiction
  intro free
  obtain ⟨d,df,con⟩ := connected_counterexample c free
  exact df (h d con)

/-- On an edge which lies on a cycle of its own color, repainting does
not disconnect its color graph. Such edges can be saturated while all
three colors stay connected. -/
def SaturatedOffBridges (c : Coloring 33) : Prop :=
  ∀ x y, x ≠ y → ∀ k, k < c.edge x y →
    ColorJoined (paint c x y k) (c.edge x y) x y → HasPath8In c k x y

theorem connected_saturated_counterexample (c : Coloring 33) (free : ¬ HasMonoC9 c) :
    ∃ d : Coloring 33, (¬ HasMonoC9 d) ∧ AllColorsConnected d ∧ SaturatedOffBridges d := by
  obtain ⟨d,df,dc⟩ := connected_counterexample c free
  obtain ⟨e,ec,ef,sat⟩ := saturated_within AllColorsConnected d dc df
  refine ⟨e,ef,ec,fun x y ne k lt link => sat x y ne k lt ?_⟩
  exact fun q u v => preserved_by_paint e x y k link q u v (ec q u v)

theorem k33_iff_connected_saturated :
    K33Claim ↔ ∀ c : Coloring 33, AllColorsConnected c → SaturatedOffBridges c → HasMonoC9 c := by
  refine ⟨fun h c _ _ => h c, ?_⟩
  intro h c
  apply Classical.byContradiction
  intro free
  obtain ⟨d,df,con,sat⟩ := connected_saturated_counterexample c free
  exact df (h d con sat)

end Connected33
end Ramsey556
