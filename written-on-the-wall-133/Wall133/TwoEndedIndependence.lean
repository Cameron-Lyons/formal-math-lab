import Wall133.ShortGirthSingleTail

namespace Wall133
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

private structure TwoStep (P : Chain G n) where
  path : Chain G (n+2)
  suffix : ∀ i,5 ≤ i → i≤n+2 → path.vertex i=P.vertex (i-2)
  near : ∀ i,i≤4 → G.dist (P.vertex 0) (path.vertex i) ≤ max (2-i) (i-2)

/-- The distance from the near endpoint of the five modified vertices is
at most 2,1,0,1,2. This keeps all extra contact sites away from the other end. -/
private theorem crossed_tail (P : Chain G n) (hn : 5≤n) (h4 : NoFourCycle G) (hc : G.Connected)
    {x y b c : V} (gx : Good P x) (gy : Good P y) (xy : x≠y) (nxy : ¬G.Adj x y)
    (xb : G.Adj x b) (yc : G.Adj y c) (b2 : Off P b (·=2)) (c3 : Off P c (·=3)) :
    Nonempty (TwoStep P) := by
  let f : ℕ → V
    | 0 => b | 1 => x | 2 => P.vertex 0 | 3 => y | 4 => c | j+5 => P.vertex (j+3)
  have ay := offGood gy
  have ax := offGood gx
  have nxc : ¬G.Adj x c := fun e => c3.fresh 0 (by omega) (h4 xy e yc gx.1.symm gy.1.symm)
  have nyb : ¬G.Adj y b := fun e => b2.fresh 0 (by omega) (h4 xy xb e gx.1.symm gy.1.symm)
  have nbc : ¬G.Adj b c := fun e => c3.fresh 2 (by omega) (h4 (b2.fresh 3 (by omega))
    e ((c3.contact 3 (by omega)).2 rfl).symm ((b2.contact 2 (by omega)).2 rfl)
    ((P.edges (by omega : 3≤n) (by omega : 2≤n)).2 (Or.inr rfl)))
  have edges (i j : ℕ) (hi : i≤n+2) (hj : j≤n+2) :
      G.Adj (f i) (f j) ↔ i+1=j ∨ j+1=i := by
    rcases i with _|_|_|_|_|i <;> rcases j with _|_|_|_|_|j <;> dsimp [f]
    all_goals first
      | rw [P.edges (by omega) (by omega)]; omega
      | rw [b2.contact _ (by omega)]; omega
      | rw [c3.contact _ (by omega)]; omega
      | rw [ax.contact _ (by omega)]; omega
      | rw [ay.contact _ (by omega)]; omega
      | rw [G.adj_comm,b2.contact _ (by omega)]; omega
      | rw [G.adj_comm,c3.contact _ (by omega)]; omega
      | rw [G.adj_comm,ax.contact _ (by omega)]; omega
      | rw [G.adj_comm,ay.contact _ (by omega)]; omega
      | simp [xb,xb.symm,yc,yc.symm,nyb,mt Adj.symm nyb,nxc,mt Adj.symm nxc,
          nxy,mt Adj.symm nxy,nbc,mt Adj.symm nbc]
  have separate (i j : ℕ) (lt : i<j) (hj : j≤n+2) (eq : f i=f j) : False := by
    have row (k : ℕ) (hk : k≤n+2) : (i+1=k ∨ k+1=i) ↔ (j+1=k ∨ k+1=j) := by
      rw [←edges i k (by omega) hk,←edges j k hj hk,eq]
    by_cases lo : 0 < i
    · have := row (i-1) (by omega); omega
    · have := row 1 (by omega); have := row 3 (by omega); omega
  let X : Chain G (n+2) := ⟨f,fun {i j} hi hj eq => by
    rcases lt_trichotomy i j with h|h|h
    · exact (separate i j h hj eq).elim
    · exact h
    · exact (separate j i h hi eq.symm).elim,fun {_ _} hi hj => edges _ _ hi hj⟩
  refine ⟨⟨X,?_,?_⟩⟩
  · intro i hi _
    change f i=P.vertex (i-2)
    rw [show i=(i-5)+5 by omega]
    change P.vertex (i-5+3)=_
    congr 1
  · intro i hi
    have dx := dist_eq_one_iff_adj.mpr gx.1
    have dy := dist_eq_one_iff_adj.mpr gy.1
    have db := hc.dist_triangle (u:=P.vertex 0) (v:=x) (w:=b)
    have dc := hc.dist_triangle (u:=P.vertex 0) (v:=y) (w:=c)
    rw [dx,dist_eq_one_iff_adj.mpr xb] at db
    rw [dy,dist_eq_one_iff_adj.mpr yc] at dc
    interval_cases i <;> dsimp [X,f] <;> first | exact db | exact dx.le | exact dc | exact dy.le | simp

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private theorem two_step_from_core (P : Chain G n) (hn : 5≤n) (h4 : NoFourCycle G) (hc : G.Connected)
    (geo : ∀ i≤n,G.dist (P.vertex 0) (P.vertex i)=i) {S:Set V}
    (star : IndependentCoreStar G S (P.vertex 0) 3) (core : ∀ x∈S,3≤G.indepNeighborsCard x) :
    Nonempty (TwoStep P) := by
  classical
  obtain ⟨A,inside,ind⟩ := star.options h4 (by omega)
  have good (x) (hx : x∈A.points) : Good P x := by
    refine ⟨A.adj _ hx,A.fresh _ hx,?_⟩
    intro i hi pos edge
    have := A.lower x hx i hi pos edge
    have dist := hc.dist_triangle (u:=P.vertex 0) (v:=x) (w:=P.vertex i)
    rw [geo i hi,dist_eq_one_iff_adj.mpr (A.adj _ hx),dist_eq_one_iff_adj.mpr edge] at dist
    omega
  have size := A.size
  obtain ⟨x,y,hx,hy,ne⟩ := Finset.one_lt_card_iff.mp (by omega : 1<A.points.card)
  have alternative (w) (hw : w∈A.points) : Nonempty (TwoStep P) ∨
      ∀ j,2 ≤ j → j≤3 → ∃ b,G.Adj w b ∧ Off P b (·=j) := by
    let R := grow P w (good w hw)
    have deg : 3≤G.indepNeighborsCard (R.vertex 0) := core _ (inside _ hw)
    obtain ⟨B⟩ := exists_contact_options R (by omega) h4 (Or.inl deg)
    by_cases growable : ∃ z∈B.points,Good R z
    · obtain ⟨z,hz,zg⟩ := growable
      let T := grow R z zg
      refine Or.inl ⟨⟨T,?_,?_⟩⟩
      · intro i hi _
        rw [show i=(i-2)+2 by omega]
        change P.vertex (i-2)=P.vertex (i-2+2-2)
        congr 1
      · intro i hi
        have dw := dist_eq_one_iff_adj.mpr (A.adj _ hw)
        have dz := hc.dist_triangle (u:=P.vertex 0) (v:=w) (w:=z)
        rw [dw,dist_eq_one_iff_adj.mpr (show G.Adj w z from B.adj _ hz)] at dz
        have d1 := geo 1 (by omega)
        have d2 := geo 2 (by omega)
        interval_cases i <;> dsimp [T,R,grow,Chain.prepend] <;> first | exact dz | exact dw.le | exact d1.le | exact d2.le | simp
    right
    have hits (z) (hz:z∈B.points) : ∃ i≤n,G.Adj z (P.vertex i) := by
      by_contra! none
      apply growable
      refine ⟨z,hz,B.adj _ hz,B.fresh _ hz,?_⟩
      rintro (_|i) hi pos e
      · exact pos rfl
      · exact none i (by omega) e
    have whereHit (z) (hz:z∈B.points) (i) (hi:i≤n) (edge:G.Adj z (P.vertex i)) : i=2 ∨ i=3 := by
      have := B.lower _ hz (i+1) (by omega) (by omega) edge
      have dist := hc.dist_triangle (u:=P.vertex 0) (v:=w) (w:=P.vertex i)
      have dist' := hc.dist_triangle (u:=w) (v:=z) (w:=P.vertex i)
      rw [geo i hi,dist_eq_one_iff_adj.mpr (A.adj _ hw)] at dist
      rw [dist_eq_one_iff_adj.mpr (show G.Adj w z from B.adj _ hz),dist_eq_one_iff_adj.mpr edge] at dist'
      omega
    have szB := B.size
    obtain ⟨b,c,hb,hc',bc⟩ := Finset.one_lt_card_iff.mp (by omega : 1<B.points.card)
    obtain ⟨k,hk,bk⟩ := hits b hb
    obtain ⟨l,hl,cl⟩ := hits c hc'
    have unique (z z' : V) (hb:z∈B.points) (hc':z'∈B.points) (bc:z≠z') (i) (hi:i≤n)
        (bi:G.Adj z (P.vertex i)) (ci:G.Adj z' (P.vertex i)) : False :=
      bc (h4 ((good w hw).2.1 _ hi) (B.adj _ hb) bi.symm (B.adj _ hc') ci.symm)
    have kl : k≠l := fun e => unique b c hb hc' bc k hk bk (e ▸ cl)
    have K := whereHit b hb k hk bk
    have L := whereHit c hc' l hl cl
    have privateAt (z z' : V) (hz:z∈B.points) (hz':z'∈B.points) (zz:z≠z') (k l : ℕ)
        (zk:G.Adj z (P.vertex k)) (zl:G.Adj z' (P.vertex l)) (choices : k=2 ∧ l=3 ∨ k=3 ∧ l=2) :
        ∃ z,G.Adj w z ∧ Off P z (·=k) := by
      refine ⟨z,B.adj _ hz,⟨fun i hi => B.fresh _ hz (i+1) (by omega),?_⟩⟩
      intro i hi
      constructor
      · intro zi
        have := whereHit z hz i hi zi
        by_contra nk
        have e : i=l := by omega
        exact unique z z' hz hz' zz i hi zi (e ▸ zl)
      · rintro rfl; exact zk
    intro j jl ju
    by_cases eq : j=k
    · subst j; exact privateAt b c hb hc' bc k l bk cl (by omega)
    · have e : j=l := by omega
      subst j; exact privateAt c b hc' hb bc.symm l k cl bk (by omega)
  rcases alternative x hx with H|X
  · exact H
  rcases alternative y hy with H|Y
  · exact H
  obtain ⟨b,xb,b2⟩ := X 2 (by decide) (by decide)
  obtain ⟨c,yc,c3⟩ := Y 3 (by decide) (by decide)
  exact crossed_tail P hn h4 hc (good x hx) (good y hy) ne (ind hx hy ne) xb yc b2 c3

/-- Two vertices of a minimum-three independence core at distance D≥5
force an induced path on at least D+5 vertices in the ambient graph. -/
theorem distance_add_five_of_two_core_vertices (h4 : NoFourCycle G) (hc : G.Connected)
    {S : Set V} {u v : V} (left : IndependentCoreStar G S u 3) (right : IndependentCoreStar G S v 3)
    (core : ∀ x∈S,3≤G.indepNeighborsCard x) (far : 5≤G.dist u v) :
    G.dist u v+5≤G.path := by
  classical
  obtain ⟨q,_,hq⟩ := hc.exists_path_of_dist v u
  have base : q.length=G.dist u v := hq.trans (G.dist_comm (u:=v) (v:=u))
  let P := chainOfChordless q ⟨q.isPath_of_length_eq_dist hq,
    fun i j hi hj => (adj_getVert_iff_consecutive_of_length_eq_dist q hq hi hj).1⟩
  have start : P.vertex 0=v := q.getVert_zero
  have geo (i) (hi : i≤q.length) : G.dist (P.vertex 0) (P.vertex i)=i := by
    change G.dist (q.getVert 0) (q.getVert i)=i
    simpa using dist_getVert_eq_sub_of_le_of_length_eq_dist q hq (Nat.zero_le i) hi
  have right' : IndependentCoreStar G S (P.vertex 0) 3 := by rw [start]; exact right
  obtain ⟨X⟩ := two_step_from_core P (by omega) h4 hc geo right' core
  let R := X.path.reverse
  have root : R.vertex 0=u := by
    change X.path.vertex (q.length+2-0)=u
    rw [Nat.sub_zero,X.suffix _ (by omega) le_rfl,Nat.add_sub_cancel]
    exact q.getVert_length
  have distances (i) (hi : i≤q.length+2) :
      (3 ≤ i → 3≤G.dist (R.vertex 0) (R.vertex i)) ∧
      (4 ≤ i → i<q.length+2 → 4≤G.dist (R.vertex 0) (R.vertex i)) := by
    rw [root]
    let j := q.length+2-i
    have ji : j+i=q.length+2 := Nat.sub_add_cancel hi
    change (3 ≤ i → 3≤G.dist u (X.path.vertex j)) ∧
      (4 ≤ i → i<q.length+2 → 4≤G.dist u (X.path.vertex j))
    by_cases old : 5 ≤ j
    · rw [X.suffix _ old (by omega)]
      have metric := dist_getVert_eq_sub_of_le_of_length_eq_dist q hq
        (show j-2≤q.length by omega) le_rfl
      rw [Walk.getVert_length,G.dist_comm] at metric
      change G.dist u (P.vertex (j-2))=q.length-(j-2) at metric
      omega
    · have near := X.near j (by omega)
      rw [start] at near
      have tri := hc.dist_triangle (u:=v) (v:=X.path.vertex j) (w:=u)
      rw [←hq,G.dist_comm (u:=X.path.vertex j) (v:=u)] at tri
      omega
  have left' : IndependentCoreStar G S (R.vertex 0) 3 := by rw [root]; exact left
  obtain ⟨A,inside,ind⟩ := left'.options h4 (by omega)
  have good (z) (hz : z∈A.points) : Good R z := by
    refine ⟨A.adj _ hz,A.fresh _ hz,?_⟩
    intro i hi pos hit
    have large := (distances i hi).1 (A.lower _ hz i hi pos hit)
    have tri := hc.dist_triangle (u:=R.vertex 0) (v:=z) (w:=R.vertex i)
    rw [dist_eq_one_iff_adj.mpr (A.adj _ hz),dist_eq_one_iff_adj.mpr hit] at tri
    omega
  have size := A.size
  obtain ⟨x,y,hx,hy,ne⟩ := Finset.one_lt_card_iff.mp (by omega : 1<A.points.card)
  have := path_of_three_metric_sites R (by omega) h4 hc (fun i h4i hi => (distances i hi.le).2 h4i hi)
    (good _ hx) (good _ hy) ne (ind hx hy ne) (Or.inl (core x (inside _ hx))) (Or.inl (core y (inside _ hy)))
  omega

end Wall133
