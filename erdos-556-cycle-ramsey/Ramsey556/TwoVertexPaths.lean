import Ramsey556.TwoVertexFrame

namespace Ramsey556

namespace SupportedOctets

private theorem chooseOuter {c : Coloring 33} (S : SupportedOctets c)
    (s : Fin 2) (used : List (Fin 17)) (enough : used.length < (S.members s).length) :
    ∃ v, S.tag v = s ∧ v ∉ used := by
  classical
  apply Classical.byContradiction
  intro fail
  have sub : S.members s ⊆ used := by
    intro i hi
    exact Classical.byContradiction (fun ne => fail ⟨i,by simpa [members] using hi,ne⟩)
  have nd : (S.members s).Nodup := (List.nodup_finRange _).filter _
  exact (Nat.not_lt_of_ge (nd.length_le_of_subset sub)) enough

/-- Two exterior vertices of the same type have six common neighbors in their octet. -/
private theorem common {c : Coloring 33} (S : SupportedOctets c)
    (s : Fin 2) (i j : Fin 17) (hi : S.tag i = s) (hj : S.tag j = s)
    (used : List (Fin 33)) (room : used.length ≤ 5) :
    ∃ a : Fin 8, S.anchor s a ∉ used ∧ c.edge (S.outer i) (S.anchor s a) = 0 ∧
      c.edge (S.outer j) (S.anchor s a) = 0 := by
  obtain ⟨u, hu⟩ := S.supports i
  obtain ⟨v, hv⟩ := S.supports j
  rw [hi] at hu
  rw [hj] at hv
  let blocked := S.anchor s u :: S.anchor s v :: used
  have fresh : ∃ a, S.anchor s a ∉ blocked := by
    apply Classical.byContradiction
    intro h
    have sub : (List.finRange 8).map (S.anchor s) ⊆ blocked := by
      intro w hw
      obtain ⟨a,_,rfl⟩ := List.mem_map.mp hw
      exact Classical.byContradiction (fun hn => h ⟨a,hn⟩)
    have nd : ((List.finRange 8).map (S.anchor s)).Nodup :=
      (List.nodup_finRange 8).map _ (fun _ _ h e => h (S.anchorInj e).2)
    have le := nd.length_le_of_subset sub
    simp [blocked] at le
    omega
  obtain ⟨a,ha⟩ := fresh
  simp only [blocked,List.mem_cons,not_or] at ha
  exact ⟨a,ha.2.2,hu _ (fun e => ha.1 (congrArg _ e)),hv _ (fun e => ha.2.1 (congrArg _ e))⟩

theorem cycle {c : Coloring 33} (a b d e f g h i j : Fin 33)
    (nd : [a,b,d,e,f,g,h,i,j].Nodup)
    (ab : c.edge a b = 0) (bd : c.edge b d = 0) (de : c.edge d e = 0)
    (ef : c.edge e f = 0) (fg : c.edge f g = 0) (gh : c.edge g h = 0)
    (hi : c.edge h i = 0) (ij : c.edge i j = 0) (ja : c.edge j a = 0) : HasMonoC9 c := by
  let xs := [a,b,d,e,f,g,h,i,j]
  let point (k : Fin 9) : Fin 33 := xs[k.val]'k.isLt
  refine ⟨0, point, fun {_ _} eq => Fin.ext (nd.eq_of_getElem_eq _ _ eq), ?_⟩
  intro k
  have cases : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> assumption

private theorem reverseEdge {c : Coloring 33} {x y : Fin 33} (h : c.edge x y = 0) :
    c.edge y x = 0 := (c.symm _ _).trans h

private theorem outerEq {c : Coloring 33} (S : SupportedOctets c) (a b : Fin 17) :
    S.outer a = S.outer b ↔ a = b := ⟨fun h => S.outerInj h, congrArg _⟩

private theorem oa {c : Coloring 33} (S : SupportedOctets c) (a : Fin 17) (s : Fin 2) (i : Fin 8) :
    S.outer a ≠ S.anchor s i := (S.disjoint _ _ _).symm

private theorem anchorEq {c : Coloring 33} (S : SupportedOctets c) (s t : Fin 2) (i j : Fin 8) :
    S.anchor s i = S.anchor t j ↔ s = t ∧ i = j := by
  constructor
  · exact fun h => S.anchorInj h
  · rintro ⟨rfl,rfl⟩
    rfl

-- These list goals record the explicitly chosen distinct vertices of one cycle.
local macro "cycle_distinct" : tactic =>
  `(tactic| (simp only [List.nodup_cons,List.nodup_nil,List.mem_cons,List.not_mem_nil,
      List.mem_nil_iff,not_or,or_false,and_true,outerEq,SupportedOctets.disjoint,oa,anchorEq] at * <;> grind))

/-- Five or more exterior vertices of a given type form a red-independent set. -/
theorem noEdge_large_type {c : Coloring 33} (S : SupportedOctets c) (free : ¬ HasMonoC9 c)
    (s : Fin 2) (size : 5 ≤ (S.members s).length) {i j : Fin 17}
    (hne : i ≠ j) (hi : S.tag i = s) (hj : S.tag j = s) : c.edge (S.outer i) (S.outer j) ≠ 0 := by
  intro edge
  obtain ⟨u,hu,nu⟩ := S.chooseOuter s [i,j] (by simpa using (show 2 < (S.members s).length by omega))
  obtain ⟨v,hv,nv⟩ := S.chooseOuter s [i,j,u] (by simpa using (show 3 < (S.members s).length by omega))
  obtain ⟨w,hw,nw⟩ := S.chooseOuter s [i,j,u,v] (by simpa using (show 4 < (S.members s).length by omega))
  obtain ⟨a,_,ia,ua⟩ := S.common s i u hi hu [] (by decide)
  obtain ⟨b,nb,ub,vb⟩ := S.common s u v hu hv [S.anchor s a] (by simp)
  obtain ⟨d,nd,vd,wd⟩ := S.common s v w hv hw [S.anchor s a,S.anchor s b] (by simp)
  obtain ⟨e,ne,we,je⟩ := S.common s w j hw hj [S.anchor s a,S.anchor s b,S.anchor s d] (by simp)
  apply free
  apply cycle (S.outer i) (S.anchor s a) (S.outer u) (S.anchor s b) (S.outer v)
    (S.anchor s d) (S.outer w) (S.anchor s e) (S.outer j) _ ia (reverseEdge ua)
    ub (reverseEdge vb) vd (reverseEdge wd) we (reverseEdge je) (reverseEdge edge)
  cycle_distinct

/-- A red edge among the smaller type also closes a cycle if two disjoint
links join the larger type to its endpoints' anchor neighbors. -/
theorem noEdge_of_two_links {c : Coloring 33} (S : SupportedOctets c) (free : ¬ HasMonoC9 c)
    (big small : Fin 2) (hbs : big ≠ small) (size : 5 ≤ (S.members big).length)
    {u v p q : Fin 17} {a b : Fin 8} (uv : u ≠ v) (hu : S.tag u = small) (hv : S.tag v = small)
    (pq : p ≠ q) (ab : a ≠ b) (hp : S.tag p = big) (hq : S.tag q = big)
    (pa : c.edge (S.outer p) (S.anchor small a) = 0) (qb : c.edge (S.outer q) (S.anchor small b) = 0)
    (ua : c.edge (S.outer u) (S.anchor small a) = 0) (vb : c.edge (S.outer v) (S.anchor small b) = 0) :
    c.edge (S.outer u) (S.outer v) ≠ 0 := by
  intro edge
  obtain ⟨w, hw, nw⟩ := S.chooseOuter big [p,q] (by simpa using (show 2 < (S.members big).length by omega))
  obtain ⟨e,_,pe,we⟩ := S.common big p w hp hw [] (by decide)
  obtain ⟨f,nf,wf,qf⟩ := S.common big w q hw hq [S.anchor big e] (by simp)
  apply free
  apply cycle (S.outer u) (S.anchor small a) (S.outer p) (S.anchor big e) (S.outer w)
    (S.anchor big f) (S.outer q) (S.anchor small b) (S.outer v) _
    ua (reverseEdge pa) pe (reverseEdge we) wf (reverseEdge qf) qb (reverseEdge vb) (reverseEdge edge)
  cycle_distinct

/-- With two disjoint red bridges between the exterior types, any anchor
having red neighbors of both types closes a nine-cycle. -/
theorem no_mixed_anchor {c : Coloring 33} (S : SupportedOctets c) (free : ¬ HasMonoC9 c)
    (big : Fin 2) (size : 5 ≤ (S.members big).length) (M : OuterMatching S big)
    (s : Fin 2) (a : Fin 8) (i j : Fin 17) (hi : S.tag i = big) (hj : S.tag j ≠ big)
    (ai : c.edge (S.anchor s a) (S.outer i) = 0) : c.edge (S.anchor s a) (S.outer j) ≠ 0 := by
  intro aj
  obtain ⟨m, diff⟩ : ∃ m, M.left m ≠ i := by
    by_cases h : M.left 0 = i
    · exact ⟨1, fun e => M.leftNe (h.trans e.symm)⟩
    · exact ⟨0,h⟩
  let p := M.left m
  let q := M.right m
  have hp : S.tag p = big := M.leftType m
  have hq : S.tag q ≠ big := M.rightType m
  have bridge : c.edge (S.outer p) (S.outer q) = 0 := M.edge m
  have pn : p ≠ i := diff
  obtain ⟨u, hu, nu⟩ := S.chooseOuter big [i,p] (by simpa using (show 2 < (S.members big).length by omega))
  obtain ⟨b,nb,ib,ub⟩ := S.common big i u hi hu [S.anchor s a] (by simp)
  by_cases close : q = j
  · obtain ⟨v, hv, nv⟩ := S.chooseOuter big [i,p,u] (by simpa using (show 3 < (S.members big).length by omega))
    obtain ⟨d,nd,ud,vd⟩ := S.common big u v hu hv [S.anchor s a,S.anchor big b] (by simp)
    obtain ⟨e,ne,ve,pe⟩ := S.common big v p hv hp [S.anchor s a,S.anchor big b,S.anchor big d] (by simp)
    apply free
    apply cycle (S.outer i) (S.anchor big b) (S.outer u) (S.anchor big d) (S.outer v)
      (S.anchor big e) (S.outer p) (S.outer j) (S.anchor s a) _
      ib (reverseEdge ub) ud (reverseEdge vd) ve (reverseEdge pe) (close ▸ bridge) (reverseEdge aj) ai
    cycle_distinct
  · obtain ⟨e,ne,ue,pe⟩ := S.common big u p hu hp [S.anchor s a,S.anchor big b] (by simp)
    have same : S.tag q = S.tag j := by omega
    obtain ⟨f,nf,qf,jf⟩ := S.common (S.tag j) q j same rfl [S.anchor s a,S.anchor big b,S.anchor big e] (by simp)
    apply free
    apply cycle (S.outer i) (S.anchor big b) (S.outer u) (S.anchor big e) (S.outer p)
      (S.outer q) (S.anchor (S.tag j) f) (S.outer j) (S.anchor s a) _
      ib (reverseEdge ub) ue (reverseEdge pe) bridge qf (reverseEdge jf) (reverseEdge aj) ai
    cycle_distinct

end SupportedOctets
end Ramsey556
