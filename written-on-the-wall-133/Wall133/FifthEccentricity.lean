import Wall133.OddRootedGrowth
import Wall133.TwoEndedIndependence

namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every geodesic of length at least four issuing from a minimum-three
independence core forces an induced path with three more vertices than
the geodesic has edges. The distant endpoint can be outside the core. -/
theorem distance_add_three_of_independence_core (h4 : NoFourCycle G) (hc : G.Connected)
    {S : Set V} {u v : V} (star : IndependentCoreStar G S u 3)
    (core : ∀ x∈S,3≤G.indepNeighborsCard x) (far : 4≤G.dist u v) :
    G.dist u v+3≤G.path := by
  classical
  obtain ⟨q,_,hq⟩ := hc.exists_path_of_dist u v
  let P := chainOfChordless q ⟨q.isPath_of_length_eq_dist hq,
    fun i j hi hj => (adj_getVert_iff_consecutive_of_length_eq_dist q hq hi hj).1⟩
  have root : P.vertex 0=u := q.getVert_zero
  have geo (i : ℕ) (hi : i≤q.length) : G.dist (P.vertex 0) (P.vertex i)=i := by
    change G.dist (q.getVert 0) (q.getVert i)=i
    simpa using dist_getVert_eq_sub_of_le_of_length_eq_dist q hq (Nat.zero_le i) hi
  have starP : IndependentCoreStar G S (P.vertex 0) 3 := by rw [root]; exact star
  obtain ⟨A,inside,ind⟩ := starP.options h4 (by omega)
  have good (w) (hw : w∈A.points) : Good P w := by
    refine ⟨A.adj _ hw,A.fresh _ hw,?_⟩
    intro i hi pos edge
    have := A.lower w hw i hi pos edge
    have dist := hc.dist_triangle (u:=P.vertex 0) (v:=w) (w:=P.vertex i)
    rw [geo i hi,dist_eq_one_iff_adj.mpr (A.adj _ hw),dist_eq_one_iff_adj.mpr edge] at dist
    omega
  have size := A.size
  obtain ⟨x,y,hx,hy,ne⟩ := Finset.one_lt_card_iff.mp (by omega : 1<A.points.card)
  have bound := path_of_three_contact_sites P (by omega) h4 hc (fun i hi => geo i hi.le)
    (good x hx) (good y hy) ne (ind hx hy ne) (Or.inl (core _ (inside _ hx))) (Or.inl (core _ (inside _ hy)))
  rwa [hq] at bound

private theorem path_of_core_at_extended_geodesic {n : ℕ} (P : Chain G n) (hn : 4≤n)
    (h4 : NoFourCycle G) (hc : G.Connected) {S : Set V}
    (star : IndependentCoreStar G S (P.vertex 0) 4)
    (core : ∀ x∈S,3≤G.indepNeighborsCard x)
    (geo : ∀ i<n,G.dist (P.vertex 0) (P.vertex i)=i) : n+3≤G.path := by
  classical
  obtain ⟨A,inside,ind⟩ := star.options h4 (by omega)
  let good := A.points.filter (Good P)
  let bad := A.points.filter (fun w => ¬Good P w)
  have last {w} (hw : w∈bad) : G.Adj w (P.vertex n) := by
    obtain ⟨hw,nw⟩ := Finset.mem_filter.mp hw
    by_contra no
    apply nw
    refine ⟨A.adj _ hw,A.fresh _ hw,?_⟩
    intro i hi pos edge
    have := A.lower w hw i hi pos edge
    by_cases eq : i=n
    · exact no (eq ▸ edge)
    · have dist := hc.dist_triangle (u:=P.vertex 0) (v:=w) (w:=P.vertex i)
      rw [geo i (by omega),dist_eq_one_iff_adj.mpr (A.adj _ hw),dist_eq_one_iff_adj.mpr edge] at dist
      omega
  have cap : bad.card≤1 := Finset.card_le_one.mpr (by
    intro x hx y hy
    have ne : P.vertex 0≠P.vertex n := fun e => by have := P.inj (Nat.zero_le _) le_rfl e; omega
    exact h4 ne (A.adj _ (Finset.mem_filter.mp hx).1) (last hx).symm
      (A.adj _ (Finset.mem_filter.mp hy).1) (last hy).symm)
  have cnt := Finset.card_filter_add_card_filter_not (s:=A.points) (Good P)
  change good.card+bad.card=A.points.card at cnt
  have size := A.size
  obtain ⟨x,y,hx,hy,ne⟩ := Finset.one_lt_card_iff.mp (by omega : 1<good.card)
  obtain ⟨xA,xg⟩ := Finset.mem_filter.mp hx
  obtain ⟨yA,yg⟩ := Finset.mem_filter.mp hy
  exact path_of_three_contact_sites P hn h4 hc geo xg yg ne (ind xA yA ne)
    (Or.inl (core _ (inside _ xA))) (Or.inl (core _ (inside _ yA)))

/-- A higher core vertex gains four vertices beyond its distance to any
endpoint with two independent neighbors or degree at least three. -/
theorem distance_add_four_of_high_core (h4 : NoFourCycle G) (hc : G.Connected)
    {S : Set V} {u v : V} (star : IndependentCoreStar G S u 4)
    (core : ∀ x∈S,3≤G.indepNeighborsCard x) (far : 3≤G.dist u v)
    (tip : 2≤G.indepNeighborsCard v ∨ 3≤G.degree v) : G.dist u v+4≤G.path := by
  classical
  obtain ⟨q,_,hq⟩ := hc.exists_path_of_dist v u
  have base : q.length=G.dist u v := hq.trans (G.dist_comm (u:=v) (v:=u))
  let P := chainOfChordless q ⟨q.isPath_of_length_eq_dist hq,
    fun i j hi hj => (adj_getVert_iff_consecutive_of_length_eq_dist q hq hi hj).1⟩
  have root : P.vertex 0=v := q.getVert_zero
  have atRoot : 2≤G.indepNeighborsCard (P.vertex 0) ∨ 3≤G.degree (P.vertex 0) := by rw [root]; exact tip
  obtain ⟨B⟩ := exists_contact_options P (by omega) h4 atRoot
  have sz := B.size
  obtain ⟨z,hz⟩ := Finset.card_pos.mp (by omega : 0<B.points.card)
  have good : Good P z := by
    refine ⟨B.adj _ hz,B.fresh _ hz,?_⟩
    intro i hi pos edge
    have := B.lower z hz i hi pos edge
    have geo : G.dist (P.vertex 0) (P.vertex i)=i := by
      change G.dist (q.getVert 0) (q.getVert i)=i
      simpa using dist_getVert_eq_sub_of_le_of_length_eq_dist q hq (Nat.zero_le i) hi
    have dist := hc.dist_triangle (u:=P.vertex 0) (v:=z) (w:=P.vertex i)
    rw [geo,dist_eq_one_iff_adj.mpr (B.adj _ hz),dist_eq_one_iff_adj.mpr edge] at dist
    omega
  let R := (grow P z good).reverse
  have pref (i) (hi : i≤q.length) : R.vertex i=q.getVert (q.length-i) := by
    change (grow P z good).vertex (q.length+1-i)=_
    rw [show q.length+1-i=q.length-i+1 by omega]
    rfl
  have start : R.vertex 0=u := by rw [pref 0 (Nat.zero_le _),Nat.sub_zero,q.getVert_length]
  have sr : IndependentCoreStar G S (R.vertex 0) 4 := by rw [start]; exact star
  have geor (i) (hi : i<q.length+1) : G.dist (R.vertex 0) (R.vertex i)=i := by
    rw [pref 0 (Nat.zero_le _),pref i (by omega),Nat.sub_zero,G.dist_comm]
    rw [dist_getVert_eq_sub_of_le_of_length_eq_dist q hq (Nat.sub_le ..) le_rfl]
    omega
  have := path_of_core_at_extended_geodesic R (by omega) h4 hc sr core geor
  omega

/-- In a fifth-band counterexample the dense core lies within one of the
radius in eccentricity. Every vertex with four independent core neighbors
is within the radius of each endpoint of degree three or with two
independent neighbors. Two core vertices have ambient distance at most
four when the radius is four or five. -/
theorem core_eccentricity_of_five_shortfall [Nonempty V] (h4 : NoFourCycle G)
    (hc : G.Connected) (avg : (5:ℝ)≤l G) (hr : 2≤G.radius.toNat) (short : G.path<G.radius.toNat+5) :
    ∃ S : Finset V, S.Nonempty ∧
      5*S.card ≤ ∑ u:S,(G.induce (S:Set V)).indepNeighborsCard u ∧
      (∀ u:S,3≤(G.induce (S:Set V)).indepNeighborsCard u) ∧
      (∀ u:S,G.eccent u.val≤(G.radius.toNat+1:ℕ)) ∧
      (∀ u v:S,G.dist u.val v.val≤max 4 (G.radius.toNat-1)) ∧
      ∀ u:S,4≤(G.induce (S:Set V)).indepNeighborsCard u →
        ∀ v,2≤G.indepNeighborsCard v ∨ 3≤G.degree v → G.dist u.val v≤G.radius.toNat := by
  classical
  obtain ⟨S,hs,avgS,hmin,_⟩ := exists_odd_independence_core h4 (d:=3) (by decide) avg
  have ambient (x) (hx : x∈(S:Set V)) : 3≤G.indepNeighborsCard x :=
    (Classical.choice (exists_core_star_of_induced (⟨x,hx⟩:S) (hmin _))).ambient
  refine ⟨S,hs,avgS,hmin,?_,?_,?_⟩
  · intro u
    apply (G.eccent_le_iff _ _).2
    intro v
    rw [←(hc u.val v).coe_dist_eq_edist]
    apply Nat.cast_le.mpr
    by_contra! farther
    obtain ⟨s⟩ := exists_core_star_of_induced u (hmin u)
    have bound := distance_add_three_of_independence_core (v:=v) h4 hc s ambient (by omega)
    omega
  · intro u v
    by_cases far : 5≤G.dist u.val v.val
    · obtain ⟨su⟩ := exists_core_star_of_induced u (hmin u)
      obtain ⟨sv⟩ := exists_core_star_of_induced v (hmin v)
      have bound := distance_add_five_of_two_core_vertices h4 hc su sv ambient far
      omega
    · omega
  · intro u high v tip
    by_contra! farther
    obtain ⟨s⟩ := exists_core_star_of_induced u high
    have bound := distance_add_four_of_high_core h4 hc s ambient (by omega) tip
    omega

end Wall133
