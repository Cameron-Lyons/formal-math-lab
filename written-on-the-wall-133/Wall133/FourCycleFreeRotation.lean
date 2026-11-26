module

public import Wall133.FourCycleFreeGeodesic
public import Wall133.GeodesicRotation

@[expose] public section

namespace Wall133
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

/-- Every stalled neighbor has a positive contact. The neighbor already
on the chain at index one can be assigned to index two. -/
private lemma contact (P : Chain G n) (hn : 2 ≤ n) {z : V} (ha : G.Adj (P.vertex 0) z)
    (h : ¬Good P z) : ∃ i ≤ n,i ≠ 0 ∧ G.Adj (P.vertex i) z := by
  by_contra! no
  apply h
  refine ⟨ha,?_,fun i hi hp e => no i hi hp e.symm⟩
  intro i hi he
  have hpos := (P.edges (Nat.zero_le _) hi).1 (he ▸ ha)
  have eq : i=1 := by omega
  subst i
  exact no 2 hn (by decide) (he ▸ (P.edges (i := 2) (j := 1) hn hi).2 (by decide))

private def Site (P : Chain G n) (i : ℕ) := i ≤ n ∧ i ≠ 0 ∧ G.dist (P.vertex 0) (P.vertex i) ≤ 2

/-- At equality, each slot has a neighbor blocked only at its unique
corresponding chain position. -/
private theorem saturated_sites (P : Chain G n) (hc : G.Connected) (h4 : NoFourCycle G)
    (N : Finset V) (ha : ∀ w∈N,G.Adj (P.vertex 0) w) (hn : 2 ≤ n)
    (sat : ∀ w∈N,¬Good P w) {m : ℕ} (f : ℕ → ℕ)
    (bound : ∀ i, Site P i → f i < m)
    (unique : ∀ i j,Site P i → Site P j → f i=f j → i=j) :
    N.card ≤ m ∧ (m ≤ N.card → ∀ k : Fin m, ∃ i, Site P i ∧ f i=k.val ∧
      ∃ w∈N,G.Adj (P.vertex i) w ∧ ∀ j ≤ n,j ≠ 0 → G.Adj (P.vertex j) w → j=i) := by
  classical
  have site (w : N) (i : ℕ) (hi : i≤n) (hp : i≠0) (h : G.Adj (P.vertex i) w.val) : Site P i := by
    have := hc.dist_triangle (u := P.vertex 0) (v := w.val) (w := P.vertex i)
    exact ⟨hi,hp,by simpa [dist_eq_one_iff_adj.mpr (ha _ w.property),dist_eq_one_iff_adj.mpr h.symm] using this⟩
  choose idx hi hpos hadj using fun w:N => contact P hn (ha _ w.property) (sat _ w.property)
  have hs (w:N) := site w _ (hi w) (hpos w) (hadj w)
  let F (w:N) : Fin m := ⟨f (idx w),bound _ (hs w)⟩
  have single (x y : N) {i : ℕ} (h : Site P i) (hx : G.Adj (P.vertex i) x.val)
      (hy : G.Adj (P.vertex i) y.val) : x=y := by
    exact Subtype.ext (h4 (fun eq => h.2.1 ((P.inj (Nat.zero_le _) h.1 eq).symm))
      (ha _ x.property) hx (ha _ y.property) hy)
  have inj : Function.Injective F := by
    intro x y eq
    have e := unique _ _ (hs x) (hs y) (congrArg Fin.val eq)
    exact single x y (hs x) (hadj x) (e ▸ hadj y)
  have count := Fintype.card_le_of_injective F inj
  refine ⟨by simpa using count,?_⟩
  intro eq k
  have onto := ((Fintype.bijective_iff_injective_and_card F).2
    ⟨inj,count.antisymm (by simpa using eq)⟩).2
  obtain ⟨x,hx⟩ := onto k
  refine ⟨idx x,hs x,congrArg Fin.val hx,x.val,x.property,hadj x,?_⟩
  intro j hj hp hjx
  have sj := site x j hj hp hjx
  obtain ⟨y,hy⟩ := onto ⟨f j,bound _ sj⟩
  have e := unique _ _ (hs y) sj (congrArg Fin.val hy)
  have he := single y x sj (e ▸ hadj y) hjx
  exact he ▸ e.symm

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- When the endpoint of a stalled chain has degree at least the number of
edges of the chain, every positive position has a neighbor of the endpoint
whose only positive contact is that position. -/
theorem full_degree_private_sites (P : Chain G n) (hc : G.Connected) (h4 : NoFourCycle G)
    (hn : 2≤n) (sat : ∀ w,G.Adj (P.vertex 0) w → ¬Good P w)
    (degree : n ≤ G.degree (P.vertex 0)) :
    G.degree (P.vertex 0) = n ∧ ∀ j, 0<j → j≤n →
      ∃ w,G.Adj (P.vertex 0) w ∧ G.Adj (P.vertex j) w ∧
        ∀ i≤n,i≠0 → G.Adj (P.vertex i) w → i=j := by
  let N := G.neighborFinset (P.vertex 0)
  have mem (w) (hw : w∈N) := (G.mem_neighborFinset _ _).mp hw
  have count := G.card_neighborFinset_eq_degree (P.vertex 0)
  change N.card=G.degree (P.vertex 0) at count
  obtain ⟨upper,full⟩ := saturated_sites P hc h4 N mem hn (fun w hw => sat w (mem w hw))
    (m:=n) (fun i => i-1) (fun i hi => by have := hi.1; have := hi.2.1; omega)
    (fun i j hi hj eq => by have := hi.2.1; have := hj.2.1; omega)
  refine ⟨by omega,?_⟩
  intro j jp jn
  obtain ⟨i,hi,slot,w,hw,adj,only⟩ := full (by omega) ⟨j-1,by omega⟩
  change i-1=j-1 at slot
  have pos := hi.2.1
  have eq : i=j := by omega
  subst i
  exact ⟨w,mem w hw,adj,only⟩

/-- A minimum-degree core adds d−2 vertices to any sufficiently long
geodesic starting in it. This uses no coloring and allows triangles. -/
theorem four_cycle_free_pointed_core (hc : G.Connected) (h4 : NoFourCycle G) (S : Finset V)
    {d : ℕ} (hd : 6 ≤ d) (hmin : ∀ x:S,d ≤ (G.induce (S:Set V)).degree x)
    (a:S) {v:V} (q:G.Walk a.val v) (hq:q.length=G.dist a.val v) (hD:2≤q.length) :
    q.length+d ≤ G.path+2 := by
  classical
  have hq' : Chordless q := ⟨q.isPath_of_length_eq_dist hq,
    fun i j hi hj => (adj_getVert_iff_consecutive_of_length_eq_dist q hq hi hj).1⟩
  obtain ⟨u,p,t,hu,hp,hlen,hgeo,hpre,sat⟩ :=
    exists_saturated_inside (S:Set V) q hq' a.property
  let P := chainOfChordless p hp
  let U : S := ⟨u,hu⟩
  let N := coreNeighbors (G := G) S U
  have head : P.vertex 0=u := p.getVert_zero
  have atAnchor : P.vertex t=a.val := by simpa [P,chainOfChordless] using hgeo 0
  have suf (j : ℕ) : P.vertex (t+j)=q.getVert j := hgeo j
  have adj (w) (hw:w∈N) : G.Adj (P.vertex 0) w := by rw [head]; exact (mem_coreNeighbors hw).1
  have dn : d ≤ N.card := (hmin U).trans_eq (coreNeighbors_card S U).symm
  have stalled (w) (hw:w∈N) : ¬Good P w := by
    intro good
    have off : w ∉ p.support := by
      intro hem
      obtain ⟨i,he,hi⟩ := Walk.mem_support_iff_exists_getVert.mp hem
      exact good.2.1 i hi he.symm
    obtain ⟨i,hi,hn,hab⟩ := sat w (mem_coreNeighbors hw).2 (mem_coreNeighbors hw).1 off
    exact good.2.2 i hi hn hab
  let lo := p.length-(G.dist u v+2)
  have window (i : ℕ) (hi : Site P i) (ht : t ≤ i) : lo ≤ i ∧ i≤lo+4 := by
    have si := hi.1
    have he : P.vertex i=q.getVert (i-t) := by simpa only [Nat.add_sub_of_le ht] using suf (i-t)
    have hdist := dist_getVert_eq_sub_of_le_of_length_eq_dist q hq (i := i-t) (j := q.length)
      (by omega) le_rfl
    rw [Walk.getVert_length,←he] at hdist
    have h₁ := hc.dist_triangle (u := u) (v := P.vertex i) (w := v)
    have h₂ := hc.dist_triangle (u := P.vertex i) (v := u) (w := v)
    rw [G.dist_comm (u := P.vertex i) (v := u)] at h₂
    have hh := hi.2.2
    rw [head] at hh
    dsimp [lo]; omega
  let f i := if i<t then i-1 else (t-1)+(i-lo)
  have capacity (i) (hi : Site P i) : f i < (t-1)+5 := by
    dsimp [f]
    by_cases h : i<t
    · rw [ite_eq_left h]; omega
    · rw [ite_eq_right h]; have := window i hi (by omega); omega
  have fi (i j) (hi : Site P i) (hj : Site P j) (he : f i=f j) : i=j := by
    have w₁ := window i hi; have w₂ := window j hj
    have := hi.2.1; have := hj.2.1
    dsimp [f] at he
    split_ifs at he <;> omega
  obtain ⟨count,full⟩ := saturated_sites P hc h4 N adj (by omega) stalled f capacity fi
  by_contra! short
  have size := P.length_le
  have ht : t=d-4 := by omega
  have fill := full (by omega)
  obtain ⟨i,hi,hfi,w,hw,hwadj,_⟩ := fill ⟨t-2,by omega⟩
  change (if i<t then i-1 else (t-1)+(i-lo))=t-2 at hfi
  have hip : i=t-1 := by have := hi.2.1; split_ifs at hfi <;> omega
  have close : G.dist a.val u ≤ 3 := by
    have h₁ := hc.dist_triangle (u := P.vertex i) (v := w) (w := u)
    rw [dist_eq_one_iff_adj.mpr hwadj,dist_eq_one_iff_adj.mpr (mem_coreNeighbors hw).1.symm] at h₁
    have h₂ := P.dist_le_sub hc (i:=i) (j:=t) (by omega) (by omega)
    rw [atAnchor,G.dist_comm] at h₂
    have h₃ := hc.dist_triangle (u := a.val) (v := P.vertex i) (w := u)
    omega
  have limit (i) (hi : Site P i) (hti : t≤ i) : i≤t+5 := by
    have hlen' := hi.1
    have ge := dist_getVert_eq_sub_of_le_of_length_eq_dist q hq (i := 0) (j := i-t)
      (Nat.zero_le _) (by omega)
    have he : P.vertex i=q.getVert (i-t) := by simpa only [Nat.add_sub_of_le hti] using suf (i-t)
    rw [Walk.getVert_zero,Nat.sub_zero,←he] at ge
    have tri := hc.dist_triangle (u := a.val) (v := u) (w := P.vertex i)
    have hh := hi.2.2
    rw [head] at hh
    omega
  have slot (s:Fin 5) : ∃ i, t≤ i ∧ i=lo+s.val ∧ Site P i ∧
      ∃ w∈N,G.Adj (P.vertex i) w ∧ ∀ j ≤ p.length,j≠0 → G.Adj (P.vertex j) w → j=i := by
    obtain ⟨i,hi,he,w,hw,hadj,only⟩ := fill ⟨t-1+s.val,by have := s.isLt; omega⟩
    change (if i<t then i-1 else (t-1)+(i-lo))=t-1+s.val at he
    by_cases h : i<t
    · rw [ite_eq_left h] at he
      have := hi.2.1; omega
    · rw [ite_eq_right h] at he
      have win := window _ hi (by omega)
      exact ⟨i,by omega,by omega,hi,w,hw,hadj,only⟩
  obtain ⟨i₀,ht₀,he₀,_,_⟩ := slot 0
  obtain ⟨i₄,ht₄,he₄,hi₄,_⟩ := slot 4
  have lastBound := limit _ hi₄ ht₄
  change i₀=lo+0 at he₀
  change i₄=lo+4 at he₄
  obtain ⟨j,_,he,hj,z,hz,hzj,priv⟩ := slot ⟨t+2-lo,by omega⟩
  change j=lo+(t+2-lo) at he
  have hj' : j=t+2 := by omega
  rw [hj'] at hzj priv
  let R := P.rotateAt (t+2) (by omega) (by omega) (adj z hz) hzj priv
  have root : R.vertex 0=a.val := by
    simpa [R,Chain.rotateAt,show ¬t+2≤0 by omega,show 1≠t+2 by omega] using atAnchor
  have remain (j) (hj : 2≤j) : R.vertex (t+j)=q.getVert j := by
    simpa [R,Chain.rotateAt,show t+2≤t+j by omega] using suf j
  let A := coreNeighbors (G := G) S a
  have choices (w) (hw:w∈A) : G.Adj (R.vertex 0) w := by rw [root]; exact (mem_coreNeighbors hw).1
  have shortR (w) (hw:w∈A) : ¬Good R w := by
    intro ok
    have h := (grow R w ok).length_le
    omega
  have bounded (i) (hi:Site R i) : i≤t+2 := by
    by_contra! h
    have hl := hi.1
    have he := remain (i-t) (by omega)
    rw [Nat.add_sub_of_le (by omega : t≤ i)] at he
    have ge := dist_getVert_eq_sub_of_le_of_length_eq_dist q hq (i := 0) (j := i-t)
      (Nat.zero_le _) (by omega)
    rw [Walk.getVert_zero,Nat.sub_zero,←he] at ge
    have hh := hi.2.2
    rw [root] at hh
    omega
  have Rcount := (saturated_sites R hc h4 A choices (by omega) shortR (fun i => i-1)
    (m := t+2) (fun i hi => by have := bounded i hi; have := hi.2.1; omega)
    (fun i j hi hj h => by have := hi.2.1; have := hj.2.1; omega)).1
  have amin : d ≤ A.card := (hmin a).trans_eq (coreNeighbors_card S a).symm
  omega

/-- The bound also holds for small core degrees by counting the positions
within two steps of the endpoint before any rotation is needed. -/
theorem radius_add_core_degree_le_path_add_two (hc : G.Connected) (h4 : NoFourCycle G)
    (S : Finset V) (hs : S.Nonempty) {d : ℕ} (hr : 2 ≤ G.radius.toNat)
    (hmin : ∀ x:S,d ≤ (G.induce (S:Set V)).degree x) : G.radius.toNat+d ≤ G.path+2 := by
  obtain ⟨a,ha⟩ := hs
  let A : S := ⟨a,ha⟩
  obtain ⟨v,q,hq,hrq⟩ := exists_geodesic_ge_radius G hc A.val
  by_cases hd : 6≤d
  · have := four_cycle_free_pointed_core hc h4 S hd hmin A q hq (by omega)
    omega
  have hq' : Chordless q := ⟨q.isPath_of_length_eq_dist hq,
    fun i j hi hj => (adj_getVert_iff_consecutive_of_length_eq_dist q hq hi hj).1⟩
  obtain ⟨u,p,t,hu,hp,hlen,hgeo,_,sat⟩ := exists_saturated_inside (S:Set V) q hq' A.property
  let U : S := ⟨u,hu⟩
  let N := coreNeighbors (G := G) S U
  have dcnt : d ≤ N.card := (hmin U).trans_eq (coreNeighbors_card S U).symm
  have bound := stalled_geodesic_middle_bound hp h4 hc q hq (by omega)
    (s := 0) (by omega : p.length=t+q.length+0) (fun j _ => hgeo j) N
    (fun w hw => (mem_coreNeighbors hw).1)
    (fun w hw => sat w (mem_coreNeighbors hw).2 (mem_coreNeighbors hw).1)
  have path := (chainOfChordless p hp).length_le
  omega

theorem radius_add_half_density_le_path_add_one [Nonempty V] (hc : G.Connected)
    (h4 : NoFourCycle G) {k : ℕ} (hr : 2 ≤ G.radius.toNat)
    (hav : (2*k)*Fintype.card V ≤ ∑ v,G.degree v) : G.radius.toNat+k ≤ G.path+1 := by
  by_cases hk : k=0
  · have := radius_add_one_le_path G hc; omega
  obtain ⟨S,hs,hd⟩ := exists_degree_core G (by omega : 0 < 2*k) hav
  have := radius_add_core_degree_le_path_add_two hc h4 S hs hr hd
  omega

end Wall133
