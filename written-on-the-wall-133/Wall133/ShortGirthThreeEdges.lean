module

public import Wall133.ShortGirthStars

@[expose] public section
namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A high core vertex and a three-edge geodesic to a non-simplicial
endpoint force a path on seven vertices. -/
theorem seven_of_nonsimplicial_end (P : Chain G 3) (h4 : NoFourCycle G) (hc : G.Connected)
    (geo : ∀ i≤3,G.dist (P.vertex 0) (P.vertex i)=i) (S : Set V)
    (atRoot : IndependentCoreStar G S (P.vertex 0) 4)
    (core : ∀ w∈S, Nonempty (IndependentCoreStar G S w 3))
    {z : V} (adj : G.Adj z (P.vertex 3)) (ne : z≠P.vertex 2) (fresh : ¬G.Adj z (P.vertex 2)) :
    7≤G.path := by
  classical
  have h0 : ¬G.Adj z (P.vertex 0) := by
    intro h
    have d := hc.dist_triangle (u:=P.vertex 0) (v:=z) (w:=P.vertex 3)
    rw [geo 3 (by decide),dist_eq_one_iff_adj.mpr h.symm,dist_eq_one_iff_adj.mpr adj] at d
    omega
  have h1 : ¬G.Adj z (P.vertex 1) := by
    intro hz
    have diff : P.vertex 1 ≠ P.vertex 3 := by intro e; have := P.inj (by decide : 1≤3) (by decide : 3≤3) e; omega
    exact ne (h4 diff hz.symm adj.symm ((P.edges (by decide : 1≤3) (by decide : 2≤3)).2 (Or.inl rfl))
      ((P.edges (by decide : 3≤3) (by decide : 2≤3)).2 (Or.inr rfl)))
  have clean : Good P.reverse z := by
    refine ⟨adj.symm,?_,?_⟩
    · intro i hi e
      change z=P.vertex (3-i) at e
      have h := (P.edges (show 3-i≤3 by omega) (by decide : 3≤3)).1 (e ▸ adj)
      exact ne ((show 3-i=2 by omega) ▸ e)
    · intro i hi ip
      change ¬G.Adj z (P.vertex (3-i))
      rcases (show 3-i=0 ∨ 3-i=1 ∨ 3-i=2 by omega) with e|e|e
      · rwa [e]
      · rwa [e]
      · rwa [e]
  let R := (grow P.reverse z clean).reverse
  have pref (i) (hi : i≤3) : R.vertex i=P.vertex i := by interval_cases i <;> rfl
  have atR : IndependentCoreStar G S (R.vertex 0) 4 := by rw [pref 0 (by decide)]; exact atRoot
  obtain ⟨A,inside,indep⟩ := atR.options h4 (by decide)
  let good := A.points.filter (Good R)
  let bad := A.points.filter (fun w => ¬Good R w)
  have last {w} (hw : w∈bad) : G.Adj w (R.vertex 4) := by
    obtain ⟨hw,nw⟩ := Finset.mem_filter.mp hw
    by_contra no
    apply nw
    refine ⟨A.adj _ hw,A.fresh _ hw,?_⟩
    intro i hi ip ha
    have low := A.lower _ hw i hi ip ha
    change i≤4 at hi
    rcases (show i=3 ∨ i=4 by omega) with rfl|rfl
    · have step := hc.dist_triangle (u:=R.vertex 0) (v:=w) (w:=R.vertex 3)
      rw [dist_eq_one_iff_adj.mpr (A.adj w hw),dist_eq_one_iff_adj.mpr ha,pref 0 (by decide),
        pref 3 (by decide),geo 3 (by decide)] at step
      omega
    · exact no ha
  have bcnt : bad.card≤1 := Finset.card_le_one.mpr (by
    intro x hx y hy
    exact h4 (fun e => by have := R.inj (Nat.zero_le _) (by decide : 4≤4) e; omega)
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
  exact seven_of_two_low_rows R h4 hx' hy' hxy (indep xA yA hxy) (Or.inl sx.ambient) (Or.inl sy.ambient)

end Wall133
