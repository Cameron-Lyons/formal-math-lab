import Wall133.CoreExterior
import Wall133.BipartiteRadiusSix

/-! # Reaching the dense subgraph from the opposite end of a geodesic

Grow a short path at the far end of the geodesic in isolation. As long as
it has no chord into the tail already grown at the other end, the two
extensions combine. The first chord gives a short induced route back into
the dense subgraph. The same geodesic can then grow from both ends.
-/

namespace Wall133
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

private theorem first_contact {n m : ℕ} (R : Chain G n) (U : Chain G m)
    (S : Finset V) (hn : n ≤ m) (hmatch : ∀ i ≤ n, U.vertex i = R.vertex i)
    (hrest : ∀ i, n < i → i ≤ m → U.vertex i ∈ S) {z : V} (hz : Good R z)
    (hfail : ¬Good U z) (hfar : 2 < G.dist z (R.vertex n)) (hc : G.Connected) :
    z ∈ S ∨ ∃ w ∈ S, Good (grow R z hz) w := by
  by_cases rep : ∃ i ≤ m, z=U.vertex i
  · obtain ⟨i,hi,he⟩ := rep
    by_cases his : i ≤ n
    · exact (hz.2.1 i his (he.trans (hmatch i his))).elim
    · exact Or.inl (he ▸ hrest i (by omega) hi)
  have hit : ∃ i ≤ m, i ≠ 0 ∧ G.Adj z (U.vertex i) := by
    by_contra! clean
    exact hfail ⟨(hmatch 0 (Nat.zero_le _)) ▸ hz.1,
      fun i hi e => rep ⟨i,hi,e⟩,clean⟩
  obtain ⟨i,hi,hip,hadj⟩ := hit
  have hlarge : n < i := by
    by_contra! h
    exact hz.2.2 i h hip ((hmatch i h) ▸ hadj)
  have skip : n+1 < i := by
    by_contra! h
    have e : G.Adj (U.vertex i) (U.vertex n) :=
      (U.edges hi hn).2 (Or.inr (by omega))
    rw [hmatch n le_rfl] at e
    have ht := hc.dist_triangle (u := z) (v := U.vertex i) (w := R.vertex n)
    rw [dist_eq_one_iff_adj.mpr hadj,dist_eq_one_iff_adj.mpr e] at ht
    omega
  refine Or.inr ⟨U.vertex i,hrest i hlarge hi,hadj,?_,?_⟩
  · intro j hj e
    cases j with
    | zero => exact hadj.ne e.symm
    | succ j =>
      change U.vertex i=R.vertex j at e
      rw [← hmatch j (by omega)] at e
      have := U.inj hi (by omega) e
      omega
  · intro j hj hjp ha
    cases j with
    | zero => exact hjp rfl
    | succ j =>
      change G.Adj (U.vertex i) (R.vertex j) at ha
      rw [← hmatch j (by omega)] at ha
      have := (U.edges hi (by omega)).1 ha
      omega

private theorem clean_step {w a : V} (p : G.Walk w a) (hp : p.length=G.dist w a)
    (hD : 2 ≤ p.length) (hc : G.Connected) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    {b j : ℕ} (E : ExteriorChoices G w b) (hj : j<b) (R : Chain G (p.length+j))
    (hm : R.vertex 0 ∈ E.allowed j) (hg : ∀ i ≤ p.length, R.vertex (j+i)=p.getVert i) :
    ∃ z ∈ E.allowed (j+1), Good R z := by
  have hbase : R.vertex j = w := by simpa using hg 0 (Nat.zero_le _)
  have hdist := R.dist_le_sub hc (i := 0) (j := j) (Nat.zero_le _) (by omega)
  rw [hbase,Nat.sub_zero,G.dist_comm] at hdist
  obtain ⟨N,hN,hmem⟩ := E.choices j hj _ hm hdist
  have bound (i : ℕ) (hi : R.Blocks i) : i/2-1 < j+1 := by
    obtain ⟨hi,_,_,hs⟩ := hi
    by_cases hh : j ≤ i
    · have he := hg (i-j) (by omega)
      rw [Nat.add_sub_of_le hh] at he
      have h := dist_getVert_eq_sub_of_le_of_length_eq_dist p hp (Nat.zero_le (i-j)) (by omega)
      rw [Walk.getVert_zero,Nat.sub_zero,← he] at h
      have := hc.dist_triangle (u := w) (v := R.vertex 0) (w := R.vertex i)
      omega
    · omega
  have inj (i k : ℕ) (hi : R.Blocks i) (hk : R.Blocks k) (h : i/2-1=k/2-1) : i=k := by
    obtain ⟨_,hi,ih,_⟩ := hi
    obtain ⟨_,hk,kh,_⟩ := hk
    omega
  obtain ⟨Q,hQ,eq⟩ := R.extendByCode hc c h4 (by omega) _ N hN hmem _ bound inj
  refine ⟨Q.vertex 0,hQ,?_,?_,?_⟩
  · rw [← eq 0]
    exact (Q.edges (by omega) (Nat.zero_le _)).2 (Or.inr rfl)
  · intro i hi h
    rw [← eq i] at h
    have := Q.inj (Nat.zero_le _) (by omega) h
    omega
  · intro i hi hn h
    rw [← eq i] at h
    have := (Q.edges (Nat.zero_le _) (by omega)).1 h
    omega

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private theorem combine_or_return {w a : V} (p : G.Walk w a) (hp : p.length=G.dist w a)
    (hD : 5 ≤ p.length) (hc : G.Connected) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    (S : Finset V) (ha : a ∈ S) {d : ℕ} (hd : 4 ≤ d)
    (hmin : ∀ u : S, d ≤ (G.induce (S : Set V)).degree u)
    {b j' : ℕ} (hb : b ≤ 2) (E : ExteriorChoices G w b)
    (hj' : j' ≤ d-1) (hfar : 3*j' ≤ p.length+1)
    {L : ℕ} (T : Chain G L) (hL : p.length ≤ L) (hT : ∀ i ≤ p.length, T.vertex i=p.getVert i)
    (hrest : ∀ i, p.length < i → i ≤ L → T.vertex i ∈ S) :
    p.length + 2*d+j' ≤ G.path+4 ∨ L+b+1 ≤ G.path := by
  let target := p.length + 2*d+j' ≤ G.path+4
  have build (j : ℕ) (hj : j ≤ b) : target ∨
      ∃ (R : Chain G (p.length+j)) (U : Chain G (L+j)), R.vertex 0 ∈ E.allowed j ∧
        (∀ i ≤ p.length, R.vertex (j+i)=p.getVert i) ∧
        (∀ i ≤ p.length+j, U.vertex i=R.vertex i) ∧
        (∀ i, p.length+j < i → i ≤ L+j → U.vertex i ∈ S) := by
    induction j with
    | zero =>
      refine Or.inr ⟨Chain.ofGeodesic p hp,T,?_,fun _ _ => by simp [Chain.ofGeodesic],hT,hrest⟩
      simpa [Chain.ofGeodesic] using E.start
    | succ j ih =>
      rcases ih (by omega) with done | ⟨R,U,hm,hg,hu,hr⟩
      · exact Or.inl done
      obtain ⟨z,hzE,hz⟩ := clean_step p hp (by omega) hc c h4 E (by omega) R hm hg
      let R' := grow R z hz
      have hg' (i : ℕ) (hi : i ≤ p.length) : R'.vertex (j+1+i)=p.getVert i := by
        rw [Nat.succ_add]; exact hg i hi
      by_cases hgood : Good U z
      · refine Or.inr ⟨R',grow U z hgood,hzE,hg',?_,?_⟩
        · intro i hi; cases i with
          | zero => rfl
          | succ i => exact hu i (by omega)
        · intro i hi hi'; cases i with
          | zero => omega
          | succ i => exact hr i (by omega) (by omega)
      · have hbase := hg' 0 (Nat.zero_le _)
        simp only [Nat.add_zero, Walk.getVert_zero] at hbase
        have hend := hg p.length le_rfl
        rw [Walk.getVert_length] at hend
        have hend' : R.vertex (p.length+j) = a := (congrArg R.vertex (Nat.add_comm p.length j)).trans hend
        have hdist := R'.dist_le_sub hc (i := 0) (j := j+1) (Nat.zero_le _) (by omega)
        change G.dist z (R'.vertex (j+1)) ≤ _ at hdist
        rw [hbase,Nat.sub_zero,G.dist_comm] at hdist
        have ht := hc.dist_triangle (u := w) (v := z) (w := a)
        have hfar' : 2 < G.dist z (R.vertex (p.length+j)) := by rw [hend']; omega
        rcases first_contact R U S (by omega) hu hr hz hgood hfar' hc with hzS | ⟨y,hyS,hy⟩
        · exact Or.inl (path_bound_of_core_return p hp hc c h4 S ha (d := d) (s := j+1) (by omega) hmin hD
            R' hzS hg' (by omega) hj' hfar)
        · let R'' := grow R' y hy
          have hg'' (i : ℕ) (hi : i ≤ p.length) : R''.vertex (j+1+1+i)=p.getVert i := by
            calc
              _ = R''.vertex ((j+1+i)+1) := congrArg R''.vertex (by omega)
              _ = _ := hg' i hi
          exact Or.inl (path_bound_of_core_return p hp hc c h4 S ha (d := d) (s := j+1+1) (by omega) hmin hD
            R'' hyS hg'' (by omega) hj' hfar)
  rcases build b le_rfl with h | ⟨_,U,_⟩
  · exact Or.inl h
  · exact Or.inr U.length_le

/-- Two available exterior steps suffice at an eccentric endpoint of a dense
core anchor. No separation of that endpoint from the core is required. -/
theorem radius_add_threshold_le_path_of_exterior_anchor (hc : G.Connected) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) {k : ℕ} (hk : 7 ≤ k) (S : Finset V) (a : S)
    (hmin : ∀ u : S, k/2+1 ≤ (G.induce (S : Set V)).degree u)
    (cost : ∀ (u : S) (t : ℕ), (c a.val).val = ((c u.val).val+t)%2 →
      (G.induce (S : Set V)).degree u ≤ (t-1)/2+3 → k ≤ t+3)
    {v : V} (hrv : G.radius.toNat ≤ G.dist a.val v) (E : ExteriorChoices G v 2)
    (hr : 5+3*(k%2) ≤ G.dist a.val v) : G.radius.toNat+k ≤ G.path := by
  obtain ⟨q,_,hq⟩ := hc.exists_path_of_dist a.val v
  obtain ⟨u,t,⟨p,hp,hlen,hsuf,hpre⟩,_,hcol,hbound,_,_⟩ :=
    geodesic_core_endpoint_with_walk hc c h4 S a.property q hq (by omega)
  have hcost := cost u t hcol hbound
  let T := (chainOfChordless p hp).reverse
  let g := q.reverse
  have hg : g.length=q.length := q.length_reverse
  have hdg : g.length=G.dist v a.val := by rw [hg,hq,G.dist_comm]
  have hT (i : ℕ) (hi : i ≤ g.length) : T.vertex i = g.getVert i := by
    change p.getVert (p.length-i) = q.reverse.getVert i
    rw [Walk.getVert_reverse,show p.length-i = t+(q.length-i) by omega,hsuf]
  have hrest (i : ℕ) (hi : g.length < i) (hin : i ≤ p.length) : T.vertex i ∈ S :=
    hpre (p.length-i) (by omega)
  rcases combine_or_return g hdg (by omega) hc c h4 S a.property (d := k/2+1)
    (by omega) hmin (by decide) E (j' := 2+k%2) (by omega) (by omega)
    T (by omega) hT hrest with h | h
  · omega
  · omega

/-- At any radius from eight onward, one exceptional vertex can have
arbitrarily small degree. For even floors the distance argument starts
already at radius five. -/
theorem radius_add_floor_le_path_of_one_exception_eight [Nonempty V] (hc : G.Connected)
    (hb : G.IsBipartite) (h4 : NoFourCycle G) (e : V)
    (hdegree : ∀ x, x ≠ e → 3 ≤ G.degree x)
    (hr : 5+3*(⌊l G⌋₊%2) ≤ G.radius.toNat) : G.radius.toNat+⌊l G⌋₊ ≤ G.path := by
  by_contra! hbad
  let k := ⌊l G⌋₊
  change G.path < G.radius.toNat+k at hbad
  change 5+3*(k%2) ≤ G.radius.toNat at hr
  have hk : 7 ≤ k := by
    by_contra! h
    have hrk := chung_bound_nat G hc
    have hs := radius_add_floor_le_path_of_bipartite_radius_le_six hc hb h4 (by omega)
    omega
  have hav : (k : ℝ) ≤ l G := Nat.floor_le (div_nonneg
    (Finset.sum_nonneg (fun v _ => Nat.cast_nonneg (G.indepNeighborsCard v))) (Nat.cast_nonneg _))
  obtain ⟨c⟩ := hb
  obtain ⟨S,a,hmin,cost⟩ := exists_growth_anchor c hk (sum_degree_ge_of_le_l hav)
  obtain ⟨a',he,ha⟩ := exists_nearby_anchor hc c h4 S a e (by omega) hbad hmin
  obtain ⟨v,q,hq,hrv⟩ := exists_geodesic_ge_radius G hc a'.val
  have hv : v ≠ e := by intro eq; subst v; omega
  have hx := radius_add_threshold_le_path_of_exterior_anchor hc c h4 hk S a' hmin
    (by simpa only [he] using cost) (v := v) (by omega) (ExteriorChoices.withException hv hdegree) (by omega)
  omega

/-- One extra neighbor at the far endpoint either extends the path, or
provides a path of at most two edges from that endpoint back into the core.
A rotated path may differ from the geodesic at its original anchor. -/
theorem one_step_or_core_return {a v : V} (q : G.Walk a v) (hq : q.length=G.dist a v)
    (hD : 5 ≤ q.length) (hc : G.Connected) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    (S : Finset V) (hv : 2 ≤ G.degree v) {L : ℕ} (T : Chain G L) (hL : q.length-1 ≤ L)
    (hsuf : ∀ i ≤ q.length-1, T.reverse.vertex i = q.getVert (q.length-i))
    (hrest : ∀ i ≤ L, q.length-1 < i → T.reverse.vertex i ∈ S) :
    L+2 ≤ G.path ∨ ∃ (s : ℕ) (P : Chain G (q.reverse.length+s)), s ≤ 2 ∧ P.vertex 0 ∈ S ∧
      ∀ i ≤ q.reverse.length, P.vertex (s+i) = q.reverse.getVert i := by
  classical
  let g := q.reverse
  have hg : g.length=q.length := q.length_reverse
  have hgeo : g.length=G.dist v a := by rw [hg,hq,G.dist_comm]
  let P := Chain.ofGeodesic g hgeo
  let R : Chain G (q.length-1) := ⟨P.vertex,fun hi hj => P.inj (by omega) (by omega),
    fun hi hj => P.edges (by omega) (by omega)⟩
  let E : ExteriorChoices G v 1 := ExteriorChoices.ofDegree (by
    intro x hx
    have h := hc.dist_eq_zero_iff.mp (show G.dist v x=0 by omega)
    subst x; exact hv)
  obtain ⟨z,_,hz⟩ := clean_step g hgeo (by omega) hc c h4 E (j := 0) (by decide) P
    (by simpa [P, Chain.ofGeodesic] using E.start) (by simp [P,Chain.ofGeodesic])
  have hzR : Good R z := ⟨hz.1,fun i hi => hz.2.1 i (by omega),fun i hi => hz.2.2 i (by omega)⟩
  have hvz : G.Adj v z := by simpa [P,Chain.ofGeodesic] using hz.1
  by_cases h : Good T.reverse z
  · exact Or.inl (grow T.reverse z h).length_le
  have hmatch (i : ℕ) (hi : i ≤ q.length-1) : T.reverse.vertex i = R.vertex i := by
    simpa only [R,P,Chain.ofGeodesic,g,Walk.getVert_reverse] using hsuf i hi
  have farSite (i : ℕ) (hi : i ≤ g.length) (hnear : q.length-1 ≤ i) : 2 < G.dist z (P.vertex i) := by
    have he := dist_getVert_eq_sub_of_le_of_length_eq_dist g hgeo (Nat.zero_le i) hi
    rw [Walk.getVert_zero,Nat.sub_zero] at he
    change G.dist v (P.vertex i) = i at he
    have ht := hc.dist_triangle (u := v) (v := z) (w := P.vertex i)
    rw [dist_eq_one_iff_adj.mpr hvz,he] at ht
    omega
  obtain h | ⟨y,hy,hyG⟩ := first_contact R T.reverse S hL hmatch (fun i hi hin => hrest i hin hi)
    hzR h (farSite _ (by omega) le_rfl) hc
  · exact Or.inr ⟨1,grow P z hz,by decide,h,fun i _ => by rw [Nat.one_add]; rfl⟩
  · have hzy : G.Adj z y := hyG.1
    have far : 2 < G.dist z (P.vertex g.length) := farSite _ le_rfl (by omega)
    have fresh : y ≠ P.vertex g.length := by
      intro he; rw [←he,dist_eq_one_iff_adj.mpr hzy] at far; omega
    have clean : ¬G.Adj y (P.vertex g.length) := by
      intro h'
      have ht := hc.dist_triangle (u := z) (v := y) (w := P.vertex g.length)
      rw [dist_eq_one_iff_adj.mpr hzy,dist_eq_one_iff_adj.mpr h'] at ht
      omega
    have hyP : Good (grow P z hz) y := by
      refine ⟨hzy,?_,?_⟩
      · intro i hi
        cases i with
        | zero => exact hzy.ne.symm
        | succ i =>
          by_cases hlast : i=g.length
          · exact hlast ▸ fresh
          · exact hyG.2.1 (i+1) (by omega)
      · intro i hi hpos
        cases i with
        | zero => exact (hpos rfl).elim
        | succ i =>
          by_cases hlast : i=g.length
          · exact hlast ▸ clean
          · exact hyG.2.2 (i+1) (by omega) (by omega)
    exact Or.inr ⟨2,grow (grow P z hz) y hyP,by decide,hy,fun i _ => by
      change (grow (grow P z hz) y hyP).vertex (2+i) = g.getVert i
      have e : 2+i = (i+1)+1 := by omega
      exact (congrArg (grow (grow P z hz) y hyP).vertex e).trans rfl⟩

end Wall133
