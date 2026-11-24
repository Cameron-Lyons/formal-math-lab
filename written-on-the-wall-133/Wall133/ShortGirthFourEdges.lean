import Wall133.ShortGirthSingleTail
namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A high core vertex and a four-edge geodesic to a non-simplicial
endpoint force a path on eight vertices. -/
theorem eight_of_nonsimplicial_end (P : Chain G 4) (h4 : NoFourCycle G) (hc : G.Connected)
    (geo : ∀ i≤4,G.dist (P.vertex 0) (P.vertex i)=i) (S : Set V)
    (atRoot : IndependentCoreStar G S (P.vertex 0) 4)
    (core : ∀ w∈S, Nonempty (IndependentCoreStar G S w 3))
    {z : V} (adj : G.Adj z (P.vertex 4)) (ne : z≠P.vertex 3) (fresh : ¬G.Adj z (P.vertex 3)) :
    8≤G.path := by
  classical
  have small (j) (hj : j≤4) (ha : G.Adj z (P.vertex j)) : 2 ≤ j := by
    have tr := hc.dist_triangle (u:=P.vertex 0) (v:=P.vertex j) (w:=P.vertex 4)
    have tr' := hc.dist_triangle (u:=P.vertex j) (v:=z) (w:=P.vertex 4)
    rw [geo 4 (by decide),geo j hj] at tr
    rw [dist_eq_one_iff_adj.mpr ha.symm,dist_eq_one_iff_adj.mpr adj] at tr'
    omega
  have two : ¬G.Adj z (P.vertex 2) := by
    intro ha
    have diff : P.vertex 2 ≠ P.vertex 4 := by intro e; have := P.inj (by decide : 2≤4) (by decide : 4≤4) e; omega
    exact ne (h4 diff ha.symm adj.symm ((P.edges (by decide : 2≤4) (by decide : 3≤4)).2 (Or.inl rfl))
      ((P.edges (by decide : 4≤4) (by decide : 3≤4)).2 (Or.inr rfl)))
  have clean : Good P.reverse z := by
    refine ⟨adj.symm,?_,?_⟩
    · intro i hi e
      change z=P.vertex (4-i) at e
      have h := (P.edges (show 4-i≤4 by omega) (by decide : 4≤4)).1 (e ▸ adj)
      exact ne ((show 4-i=3 by omega) ▸ e)
    · intro i hi ip ha
      change G.Adj z (P.vertex (4-i)) at ha
      have := small (4-i) (by omega) ha
      rcases (show 4-i=2 ∨ 4-i=3 by omega) with e|e
      · exact two (e ▸ ha)
      · exact fresh (e ▸ ha)
  let R := (grow P.reverse z clean).reverse
  have pref (i) (hi : i≤4) : R.vertex i=P.vertex i := by interval_cases i <;> rfl
  have atR : IndependentCoreStar G S (R.vertex 0) 4 := by rw [pref 0 (by decide)]; exact atRoot
  obtain ⟨A,inside,indep⟩ := atR.options h4 (by decide)
  let good := A.points.filter (Good R)
  let bad := A.points.filter (fun w => ¬Good R w)
  have last {w} (hw : w∈bad) : G.Adj w (R.vertex 5) := by
    obtain ⟨hw,nw⟩ := Finset.mem_filter.mp hw
    by_contra no
    apply nw
    refine ⟨A.adj _ hw,A.fresh _ hw,?_⟩
    intro i hi ip ha
    have low := A.lower _ hw i hi ip ha
    change i≤5 at hi
    by_cases k : i=5
    · exact no (k ▸ ha)
    · have step := hc.dist_triangle (u:=R.vertex 0) (v:=w) (w:=R.vertex i)
      rw [dist_eq_one_iff_adj.mpr (A.adj w hw),dist_eq_one_iff_adj.mpr ha,
        pref 0 (by decide),pref i (by omega),geo i (by omega)] at step
      omega
  have bcnt : bad.card≤1 := Finset.card_le_one.mpr (by
    intro x hx y hy
    exact h4 (fun e => by have := R.inj (Nat.zero_le _) (by decide : 5≤5) e; omega)
      (A.adj _ (Finset.mem_filter.mp hx).1) (last hx).symm
      (A.adj _ (Finset.mem_filter.mp hy).1) (last hy).symm)
  have count := Finset.card_filter_add_card_filter_not (s:=A.points) (Good R)
  change good.card+bad.card=A.points.card at count
  have := A.size
  obtain ⟨x,y,hx,hy,hxy⟩ := Finset.one_lt_card_iff.mp (by omega : 1<good.card)
  obtain ⟨xA,hx'⟩ := Finset.mem_filter.mp hx
  obtain ⟨yA,hy'⟩ := Finset.mem_filter.mp hy
  obtain ⟨sx⟩ := core x (inside x xA)
  obtain ⟨sy⟩ := core y (inside y yA)
  have geoR (i) (hi : i<5) : G.dist (R.vertex 0) (R.vertex i)=i := by
    rw [pref 0 (by decide),pref i (by omega),geo i (by omega)]
  exact path_of_three_contact_sites R (by decide) h4 hc geoR hx' hy' hxy (indep xA yA hxy)
    (Or.inl sx.ambient) (Or.inl sy.ambient)

end Wall133
