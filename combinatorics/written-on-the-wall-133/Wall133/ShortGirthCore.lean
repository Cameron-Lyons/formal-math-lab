module

public import Wall133.ShortGirthExact

@[expose] public section

namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem saturated_independence_bound {u v : V} (p : G.Walk u v) (hp : Chordless p)
    (h4 : NoFourCycle G) (hn : 2 ≤ p.length)
    (sat : ∀ w, G.Adj u w → w ∉ p.support → ∃ i ≤ p.length,i≠0 ∧ G.Adj w (p.getVert i)) :
    G.indepNeighborsCard u ≤ p.length-2+1 := by
  classical
  let P := chainOfChordless p hp
  obtain ⟨A⟩ := exists_independent_options P hn h4
  have wfresh (w : A.points) : w.val∉p.support := by
    intro he
    obtain ⟨i,hi,eq⟩ := (Walk.mem_support_iff_exists_getVert.mp he)
    exact A.fresh w w.property i eq hi.symm
  choose idx hi hpos ha using fun w : A.points => sat w.val (by
    simpa [P,chainOfChordless] using A.adj w w.property) (wfresh w)
  have lo (w : A.points) := A.lower _ w.property (idx w) (hi w) (hpos w) (ha w)
  let f (w : A.points) : Fin (p.length-2) := ⟨idx w-3,by have := lo w; have := hi w; omega⟩
  have fi : Function.Injective f := by
    intro w z e
    have he := congrArg Fin.val e
    change idx w-3=idx z-3 at he
    have eq : idx w=idx z := by have := lo w; have := lo z; omega
    have ne : P.vertex 0≠P.vertex (idx w) := fun h => by have := P.inj (Nat.zero_le _) (hi w) h; have := hpos w; omega
    exact Subtype.ext (h4 ne (A.adj w w.property) (ha w).symm (A.adj z z.property) (eq ▸ (ha z).symm))
  have cnt : A.points.card ≤ p.length-2 := by simpa using Fintype.card_le_of_injective f fi
  have h := A.size
  simpa [P,chainOfChordless] using h.trans (Nat.add_le_add_right cnt 1)

/-- From any specified vertex, grow an induced path ending at that vertex. -/
theorem exists_long_chordless_ending (h4 : NoFourCycle G) {d : ℕ} (hd : 2 ≤ d)
    (hmin : ∀ u,d≤G.indepNeighborsCard u) (a : V) :
    ∃ (u : V) (p : G.Walk u a), Chordless p ∧ d+1 ≤ p.length := by
  classical
  have hdeg := (hmin a).trans (indepNeighborsCard_le_degree a)
  obtain ⟨b,hb⟩ := (G.degree_pos_iff_exists_adj a).mp (by omega)
  let W := (G.neighborFinset b).filter (fun w => w≠a ∧ ¬G.Adj a w)
  have wm (w) : w∈W ↔ G.Adj b w ∧ w≠a ∧ ¬G.Adj a w := by simp [W]
  have cnt := (eligible_neighbors_card h4 hb.symm W wm).1
  have db := hmin b
  obtain ⟨z,hz⟩ := Finset.card_pos.mp (by omega : 0<W.card)
  obtain ⟨hbz,hza,haz⟩ := (wm z).mp hz
  let start : G.Walk z a := .cons hbz.symm (.cons hb.symm .nil)
  have hstart : Chordless start := by
    refine ⟨?_,?_⟩
    · simp [start,Walk.isPath_def,hbz.ne.symm,hb.ne.symm,hza]
    · intro i j hi hj ha'
      change i≤2 at hi
      change j≤2 at hj
      interval_cases i <;> interval_cases j <;>
        simp_all [start,Walk.getVert_cons_succ,G.adj_comm]
  obtain ⟨u,p,_,_,hp,hl,_,sat⟩ := exists_saturated Set.univ start hstart (Set.mem_univ _)
  have h2 : 2≤p.length := by change p.length=_+2 at hl; omega
  have pu := saturated_independence_bound p hp h4 h2 (fun w => sat w (Set.mem_univ _))
  have := hmin u
  exact ⟨u,p,hp,by omega⟩

/-- A vertex with more than the minimum number of independent neighbors
gives one extra vertex on an induced path, also when the graph has triangles. -/
theorem min_neighborhood_independence_path_bound (h4 : NoFourCycle G) {d : ℕ} (hd : 2 ≤ d)
    (hmin : ∀ u,d≤G.indepNeighborsCard u) (a : V) :
    d+2+(if d<G.indepNeighborsCard a then 1 else 0) ≤ G.path := by
  classical
  obtain ⟨u,p,hp,pu⟩ := exists_long_chordless_ending h4 hd hmin a
  obtain ⟨v,q,s,_,hq,hqL,hqS,qsat⟩ := exists_saturated Set.univ p.reverse hp.reverse (Set.mem_univ _)
  have ql : q.length=s+p.length := by simpa using hqL
  have qv := saturated_independence_bound q hq h4 (by omega) (fun w => qsat w (Set.mem_univ _))
  have pgu := hmin u
  have verts := G.length_le_path_of_isInducedPath _ (isInducedPath_support_of_isPath_of_adj_getVert q
    hq.simple hq.consecutive)
  rw [Walk.length_support] at verts
  split_ifs with high
  · by_cases hs : s=0
    · subst s
      have eq : v=a := by simpa using hqS 0
      have hα := congrArg (fun w => G.indepNeighborsCard w) eq
      omega
    · omega
  · omega

end Wall133
