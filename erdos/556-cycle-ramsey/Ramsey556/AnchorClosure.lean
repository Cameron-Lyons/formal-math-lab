import Ramsey556.AnchorSupport

namespace Ramsey556.AnchorSupport

variable {c : Coloring 33} {size : Nat}

private theorem short_of_independent (classify : TwoColorOctets16) (free : ¬ HasMonoC9 c)
    (xs : List (Fin 33)) (ind : xs.Pairwise (fun x y => x ≠ y ∧ c.edge x y ≠ 0)) : xs.length ≤ 15 := by
  apply Nat.le_of_not_gt
  intro enough
  let f (i : Fin 16) := xs[i.val]'(by omega)
  have forward {i j : Fin 16} (lt : i < j) : f i ≠ f j ∧ c.edge (f i) (f j) ≠ 0 :=
    ind.rel_getElem_of_lt (by omega) (by omega) lt
  have nd : xs.Nodup := ind.imp (fun h => h.1)
  apply free (hasMonoC9_of_independent16 classify c f
    (fun {_ _} h => Fin.ext (nd.eq_of_getElem_eq _ _ h)) 0 ?_)
  intro i j ne
  by_cases lt : i < j
  · exact (forward lt).2
  · rw [c.symm]
    exact (forward (show j < i by omega)).2

private theorem short_union (S : AnchorSupport c size) (classify : TwoColorOctets16) (free : ¬ HasMonoC9 c)
    (xs : List (Fin 17)) (ys : List (Fin size)) (nx : xs.Nodup) (ny : ys.Nodup)
    (inner : ∀ i ∈ xs, ∀ j ∈ xs, i ≠ j → c.edge (S.outer i) (S.outer j) ≠ 0)
    (cross : ∀ i ∈ xs, ∀ a ∈ ys, c.edge (S.outer i) (S.anchor a) ≠ 0) :
    xs.length + ys.length ≤ 15 := by
  let vertices := xs.map S.outer ++ ys.map S.anchor
  suffices bound : vertices.length ≤ 15 by simpa [vertices] using bound
  apply short_of_independent classify free vertices
  refine List.pairwise_append.mpr ⟨List.pairwise_map.mpr ?_, List.pairwise_map.mpr ?_, ?_⟩
  · exact nx.imp_of_mem (fun hi hj ne => ⟨fun eq => ne (S.outerInj eq), inner _ hi _ hj ne⟩)
  · exact ny.imp (fun ne => ⟨fun eq => ne (S.anchorInj eq), S.independent _ _ ne⟩)
  · rintro _ hi _ ha
    obtain ⟨i,memI,rfl⟩ := List.mem_map.mp hi
    obtain ⟨a,memA,rfl⟩ := List.mem_map.mp ha
    exact ⟨S.oa i a, cross i memI a memA⟩

/-- In a bipartite graph with no two disjoint edges, one vertex meets every edge. -/
private theorem matching_or_star {α β : Type} [Inhabited α] (r : α → β → Prop) :
    (∃ x y a b, x ≠ y ∧ a ≠ b ∧ r x a ∧ r y b) ∨
    (∃ x, ∀ y b, r y b → y = x) ∨ (∃ a, ∀ x b, r x b → b = a) := by
  classical
  by_cases matching : ∃ x y a b, x ≠ y ∧ a ≠ b ∧ r x a ∧ r y b
  · exact Or.inl matching
  right
  by_cases row : ∃ x, ∀ y b, r y b → y = x
  · exact Or.inl row
  simp only [not_exists, Classical.not_forall] at row
  obtain ⟨x,a,xa,_⟩ := row default
  obtain ⟨y,b,yb,yx⟩ := row x
  refine Or.inr ⟨a,fun z d zd => ?_⟩
  by_cases zx : z = x <;> grind

private theorem noEdge_small (S : AnchorSupport c size) (classify : TwoColorOctets16) (free : ¬ HasMonoC9 c)
    (big : Fin 2) (large : 13 ≤ (S.members big).length)
    (inner : ∀ i j, i ≠ j → S.tag i = big → S.tag j = big → c.edge (S.outer i) (S.outer j) ≠ 0)
    {u v : Fin 17} (ne : u ≠ v) (other : S.tag u ≠ big) (same : S.tag u = S.tag v) :
    c.edge (S.outer u) (S.outer v) ≠ 0 := by
  intro edge
  let xs := S.members big
  let ys := S.neighbors u v
  have nx : xs.Nodup := (List.nodup_finRange 17).filter _
  have ny : ys.Nodup := (List.nodup_finRange size).filter _
  have xl : 13 ≤ xs.length := large
  have yl : 4 ≤ ys.length := S.common u v same
  have tag {p} (h : p ∈ xs) : S.tag p = big := by simpa [xs,members] using h
  have adj {a} (h : a ∈ ys) : S.Via u v a := by simpa [ys,neighbors,Via] using h
  have ind {i j} (hi : i ∈ xs) (hj : j ∈ xs) (ne : i ≠ j) := inner i j ne (tag hi) (tag hj)
  let link (p a) := p ∈ xs ∧ a ∈ ys ∧ c.edge (S.outer p) (S.anchor a) = 0
  rcases matching_or_star link with ⟨p,q,a,b,pq,ab,⟨hp,ha,pa⟩,hq,hb,qb⟩ | ⟨x,star⟩ | ⟨y,star⟩
  · obtain ⟨w,hw,nw⟩ := S.freshOuter big [p,q] (by simp; omega)
    have pBig := tag hp
    have qBig := tag hq
    obtain ⟨e,ne',pw⟩ := S.freshAnchor p w (pBig.trans hw.symm) [a,b] (by simp)
    obtain ⟨f,nf,wq⟩ := S.freshAnchor w q (hw.trans qBig.symm) [a,b,e] (by simp)
    apply free
    apply S.alternatingCycle ⟨(adj ha).1, pa⟩ pw wq ⟨qb, (adj hb).2⟩ edge <;> simp_all <;> grind
  · have h := S.short_union classify free (xs.erase x) ys (nx.erase _) ny
      (fun _ hi _ hj => ind (List.mem_of_mem_erase hi) (List.mem_of_mem_erase hj))
      (fun i hi a ha e => (nx.mem_erase_iff.mp hi).1 (star i a ⟨List.mem_of_mem_erase hi,ha,e⟩))
    have := List.le_length_erase (a := x) (l := xs)
    omega
  · have h := S.short_union classify free xs (ys.erase y) nx (ny.erase _)
      (fun _ hi _ hj => ind hi hj)
      (fun i hi a ha e => (ny.mem_erase_iff.mp ha).1 (star i a ⟨hi,List.mem_of_mem_erase ha,e⟩))
    have := List.le_length_erase (a := y) (l := ys)
    omega

private theorem outer_edge_avoiding (S : AnchorSupport c size) (classify : TwoColorOctets16)
    (free : ¬ HasMonoC9 c) (z : Fin 17) :
    ∃ p q, p ≠ z ∧ q ≠ z ∧ p ≠ q ∧ c.edge (S.outer p) (S.outer q) = 0 := by
  apply Classical.byContradiction
  intro fail
  let xs := (List.finRange 17).erase z
  have away {i} (h : i ∈ xs) : i ≠ z := ((List.nodup_finRange 17).mem_erase_iff.mp h).1
  have bound := S.short_union classify free xs [] ((List.nodup_finRange 17).erase z) (by simp)
    (fun i hi j hj ne edge => fail ⟨i,j,away hi,away hj,ne,edge⟩) (by simp)
  simp [xs] at bound

private theorem no_mixed (S : AnchorSupport c size) (classify : TwoColorOctets16) (free : ¬ HasMonoC9 c)
    (big : Fin 2) (large : 5 ≤ (S.members big).length)
    (inner : ∀ i j, i ≠ j → S.tag i = S.tag j → c.edge (S.outer i) (S.outer j) ≠ 0)
    (a : Fin size) (i j : Fin 17) (hi : S.tag i = big) (hj : S.tag j ≠ big)
    (ai : c.edge (S.anchor a) (S.outer i) = 0) : c.edge (S.anchor a) (S.outer j) ≠ 0 := by
  intro aj
  obtain ⟨x,y,hx,hy,xy,edge⟩ := S.outer_edge_avoiding classify free i
  have diff : S.tag x ≠ S.tag y := fun eq => inner x y xy eq edge
  obtain ⟨p,q,hp,hq,pn,bridge⟩ : ∃ p q, S.tag p = big ∧ S.tag q ≠ big ∧ p ≠ i ∧
      c.edge (S.outer p) (S.outer q) = 0 := by
    by_cases eq : S.tag x = big
    · exact ⟨x,y,eq,fun e => diff (eq.trans e.symm),hx,edge⟩
    · exact ⟨y,x,by omega,eq,hy,flip edge⟩
  obtain ⟨u,hu,nu⟩ := S.freshOuter big [i,p] (by simp; omega)
  obtain ⟨b,nb,iu⟩ := S.freshAnchor i u (hi.trans hu.symm) [a] (by simp)
  have ji : S.Via j i a := ⟨flip aj, flip ai⟩
  by_cases close : q = j
  · subst q
    obtain ⟨v,hv,nv⟩ := S.freshOuter big [i,p,u] (by simp; omega)
    obtain ⟨d,nd,uv⟩ := S.freshAnchor u v (hu.trans hv.symm) [a,b] (by simp)
    obtain ⟨e,ne,vp⟩ := S.freshAnchor v p (hv.trans hp.symm) [a,b,d] (by simp)
    apply free
    apply S.alternatingCycle ji iu uv vp (flip bridge) <;> simp_all <;> grind
  · obtain ⟨e,ne,up⟩ := S.freshAnchor u p (hu.trans hp.symm) [a,b] (by simp)
    obtain ⟨f,nf,qj⟩ := S.freshAnchor q j (by omega) [a,b,e] (by simp)
    apply free
    apply S.alternatingCycle qj ji iu up (flip bridge) <;> simp_all <;> grind

private theorem sizes (S : AnchorSupport c size) : ∃ big small : Fin 2, big ≠ small ∧
    9 ≤ (S.members big).length ∧ (S.members big).length + (S.members small).length = 17 := by
  have complement (i : Fin 17) : (decide ¬ (S.tag i == 0) = true) = (S.tag i == 1) :=
    (by decide : ∀ t : Fin 2, (decide ¬ (t == 0) = true) = (t == 1)) (S.tag i)
  have total := List.length_eq_countP_add_countP (fun i => S.tag i == 0) (l := List.finRange 17)
  simp only [complement, List.countP_eq_length_filter, List.length_finRange] at total
  change 17 = (S.members 0).length + (S.members 1).length at total
  by_cases h : 9 ≤ (S.members 0).length
  · exact ⟨0,1,by decide,h,total.symm⟩
  · exact ⟨1,0,by decide,by omega,by omega⟩

/-- Each exterior group is red-independent, and an anchor can meet at most one
group in red. Put each anchor with a group it misses. The resulting two
red-independent sets cover at least 31 vertices, so one contains at least 16. -/
theorem forces_cycle_of_size (S : AnchorSupport c size) (enough : 14 ≤ size) (classify : TwoColorOctets16) : HasMonoC9 c := by
  classical
  apply Classical.byContradiction
  intro free
  obtain ⟨big,small,diff,large,total⟩ := S.sizes
  have one (i j : Fin 17) := @noEdge_large c size S free big (by omega) i j
  have inner (i j : Fin 17) (ne : i ≠ j) (same : S.tag i = S.tag j) : c.edge (S.outer i) (S.outer j) ≠ 0 := by
    by_cases hi : S.tag i = big
    · exact one i j ne hi (same ▸ hi)
    by_cases enough : 5 ≤ (S.members small).length
    · exact S.noEdge_large free small enough ne (by omega) (by omega)
    exact S.noEdge_small classify free big (by omega) one ne hi same
  let hit (a : Fin size) := decide (∃ i, S.tag i = big ∧ c.edge (S.anchor a) (S.outer i) = 0)
  let anchors := List.finRange size
  have tag {s i} (h : i ∈ S.members s) : S.tag i = s := by simpa [members] using h
  have independent (s : Fin 2) (p : Fin size → Bool)
      (absent : ∀ i a, S.tag i = s → p a → c.edge (S.anchor a) (S.outer i) ≠ 0) :=
    S.short_union classify free (S.members s) (anchors.filter p) ((List.nodup_finRange 17).filter _)
      ((List.nodup_finRange size).filter _) (fun i hi j hj n => inner i j n ((tag hi).trans (tag hj).symm))
      (fun i hi a ha e => absent i a (tag hi) (List.mem_filter.mp ha).2 (flip e))
  have first := independent big (fun a => decide (¬ hit a = true)) (by
    intro i a hi miss e
    have yes : hit a = true := decide_eq_true ⟨i,hi,e⟩
    simp [yes] at miss)
  have second := independent small hit (by
    intro j a hj ha
    obtain ⟨i,hi,e⟩ := of_decide_eq_true ha
    exact S.no_mixed classify free big (by omega) inner a i j hi (by omega) e)
  have sum := List.length_eq_countP_add_countP hit (l := anchors)
  simp only [List.countP_eq_length_filter, anchors, List.length_finRange] at sum first second
  omega

theorem forces_cycle (S : AnchorSupport c) (classify : TwoColorOctets16) : HasMonoC9 c :=
  S.forces_cycle_of_size (by decide) classify

end Ramsey556.AnchorSupport
