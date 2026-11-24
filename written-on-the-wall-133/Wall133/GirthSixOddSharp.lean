import Wall133.GirthSixSharp
import Wall133.OddNeighborhoodCore
import Wall133.HereditaryDensity
import Wall133.LeafPruning

namespace Wall133
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

private theorem core_parity {S : Finset V} (P : Chain G n) {t : ℕ} (ht : t ≤ n)
    (inside : ∀ i ≤ t,P.vertex i∈S) (c : (G.induce (S : Set V)).Coloring (Fin 2)) :
    (c ⟨P.vertex 0,inside 0 (Nat.zero_le _)⟩=c ⟨P.vertex t,inside t le_rfl⟩) ↔ t%2=0 := by
  let T : Chain (G.induce (S : Set V)) t := {
    vertex := fun i => ⟨P.vertex (min i t),inside _ (min_le_right _ _)⟩
    inj := by
      intro i j hi hj e
      have he := congrArg Subtype.val e
      simp only [min_eq_left hi,min_eq_left hj] at he
      exact P.inj (by omega) (by omega) he
    edges := by
      intro i j hi hj
      change G.Adj (P.vertex (min i t)) (P.vertex (min j t)) ↔ _
      rw [min_eq_left hi,min_eq_left hj]
      exact P.edges (by omega) (by omega) }
  have h := T.color_val c t le_rfl
  let u : S := ⟨P.vertex 0,inside 0 (Nat.zero_le _)⟩
  let a : S := ⟨P.vertex t,inside t le_rfl⟩
  have hu : T.vertex 0=u := by apply Subtype.ext; simp [u,T]
  have ha : T.vertex t=a := by apply Subtype.ext; simp [a,T]
  rw [hu,ha] at h
  change c u=c a ↔ _
  constructor
  · intro e; rw [e] at h; have := (c a).isLt; omega
  · intro e; apply Fin.ext; have := (c u).isLt; omega

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private theorem two_steps (hg : 6 ≤ G.egirth) (hc : G.Connected) (R : Chain G n)
    (S : Finset V) (u : S) (hu : R.vertex 0=u.val) {a v : V} (q : G.Walk a v) {e t j r : ℕ}
    (hq : q.length ≤ G.dist a v+e) (hn : n=t+q.length) (hL : 5 ≤ q.length) (hj : j ≤ r+2+e)
    (suf : ∀ k,j ≤ k → k ≤ q.length → R.vertex (t+k)=q.getVert k) (near : G.dist a u.val ≤ r)
    (size : (t+r+2+e)/2 < (G.induce (S : Set V)).degree u)
    (next : ∀ z : S,(G.induce (S : Set V)).Adj u z → (t+1+(r+1)+2+e)/2 <
      (G.induce (S : Set V)).degree z) : n+3 ≤ G.path := by
  obtain ⟨w,hw,g⟩ := girth_six_grow_among hg hc R q hq hn (by omega) hj suf (hu ▸ near)
    (coreNeighbors (G:=G) S u) (fun z hz => hu ▸ (mem_coreNeighbors hz).1) (by rwa [coreNeighbors_card])
  let z : S := ⟨w,(mem_coreNeighbors hw).2⟩
  have adj : (G.induce (S : Set V)).Adj u z := (mem_coreNeighbors hw).1
  have zn : G.dist a z.val ≤ r+1 := by
    have tri := hc.dist_triangle (u:=a) (v:=u.val) (w:=z.val)
    rw [dist_eq_one_iff_adj.mpr (show G.Adj u.val z.val from adj)] at tri
    omega
  apply girth_six_core_growth hg hc (grow R w g) S z rfl q hq (t:=t+1) (by omega) (by omega)
    (j:=j) (by omega) _ zn (next z adj)
  intro k hk hlen
  rw [show t+1+k=(t+k)+1 by omega]
  exact suf k hk hlen

omit [Fintype V] in
private theorem pick_neighbor (S : Finset V) (a : S) (z : V)
    (hdeg : 2 ≤ (G.induce (S : Set V)).degree a) :
    ∃ x : S,G.Adj a.val x.val ∧ x.val ≠ z := by
  let H := G.induce (S : Set V)
  by_contra! h
  have sc : (H.neighborFinset a).card ≤ 1 := Finset.card_le_one.mpr (fun x hx y hy =>
    Subtype.ext ((h x ((H.mem_neighborFinset _ _).mp hx)).trans (h y ((H.mem_neighborFinset _ _).mp hy)).symm))
  rw [H.card_neighborFinset_eq_degree] at sc
  exact (Nat.not_succ_le_self 1) (hdeg.trans sc)

/-- A geodesic starting at the high-degree side of a two-colored core
gains at least 2d−2 vertices, even in a nonbipartite ambient graph. -/
theorem girth_six_high_side_pointed (hg : 6 ≤ G.egirth) (hc : G.Connected)
    (S : Finset V) (c : (G.induce (S : Set V)).Coloring (Fin 2)) (a : S) {d : ℕ} (hd : 4 ≤ d)
    (hmin : ∀ z : S,d ≤ (G.induce (S : Set V)).degree z)
    (boost : ∀ z : S,c z=c a → d < (G.induce (S : Set V)).degree z)
    {v : V} (q : G.Walk a.val v) (hq : q.length=G.dist a.val v) (hl : 5 ≤ q.length) :
    q.length+2*d-2 ≤ G.path := by
  obtain ⟨x,hax,hx⟩ := pick_neighbor (G:=G) S a (q.getVert 1) (by have := hmin a; omega)
  have hp : Chordless q := ⟨q.isPath_of_length_eq_dist hq,
    fun _ _ hi hj => (adj_getVert_iff_consecutive_of_length_eq_dist q hq hi hj).1⟩
  have metric : q.length ≤ G.dist a.val v+0 := hq.le
  obtain ⟨t,n,P,hn,px,suf,inside,all⟩ :=
    girth_six_core_rotations hc hg S hd hmin a x q (e:=0) (by decide) metric hp hl hax hx
  let u : S := ⟨P.vertex 0,inside 0 (Nat.zero_le _)⟩
  have anchor : P.vertex t=a.val := by simpa using suf 0 (Nat.zero_le _)
  have eq := core_parity P (by omega : t ≤ n) inside c
  have aeq : (⟨P.vertex t,inside t le_rfl⟩ : S)=a := Subtype.ext anchor
  rw [aeq] at eq
  have plen := P.length_le
  by_contra! short
  have odd : t%2 ≠ 0 := by
    intro ev
    have := (all (d+1) (by omega) (boost u (eq.2 ev))).1
    omega
  obtain ⟨lower,rot⟩ := all d le_rfl (hmin u)
  have ht : t=2*d-5 := by clear * - odd hd lower hn plen short; omega
  obtain ⟨j,R,lo,up,root,rs,-⟩ := rot (Or.inl ht)
  clear all rot
  rcases (show j=1 ∨ j=2 by omega) with rfl|rfl
  · have rX : R.vertex 0=x.val := by rwa [show t+1-2=t-1 by omega,px] at root
    have := two_steps hg hc R S x rX q metric hn hl (by omega) rs
      ((dist_eq_one_iff_adj.mpr hax).le) (by have := hmin x; omega) (fun z hz => by
        have col := color_common c hz.symm (show (G.induce (S : Set V)).Adj a x from hax)
        have := boost z col
        omega)
    omega
  · have rA : R.vertex 0=a.val := by rwa [show t+2-2=t by omega,anchor] at root
    have := two_steps hg hc R S a rA q metric hn hl (r:=0) (by omega) rs (by simp)
      (by have := hmin a; omega) (fun z hz => by have := hmin z; omega)
    omega


/-- At a low-side anchor the full odd threshold holds whenever the first
edge of the starting path lies inside the two-colored core. One extra edge
beyond the distance is allowed, with a corresponding loss of one vertex. -/
theorem girth_six_low_side_pointed (hg : 6 ≤ G.egirth) (hc : G.Connected)
    (S : Finset V) (c : (G.induce (S : Set V)).Coloring (Fin 2)) (a : S) {d : ℕ} (hd : 4 ≤ d)
    (hmin : ∀ z : S,d ≤ (G.induce (S : Set V)).degree z)
    (boost : ∀ z : S,c z ≠ c a → d < (G.induce (S : Set V)).degree z)
    {v : V} (q : G.Walk a.val v) {e : ℕ} (he : e ≤ 1) (metric : q.length ≤ G.dist a.val v+e)
    (hp : Chordless q) (hl : 5 ≤ q.length) (hq1 : q.getVert 1∈S) :
    q.length+2*d-1 ≤ G.path+e := by
  obtain ⟨x,hax,hx⟩ := pick_neighbor (G:=G) S a (q.getVert 1) (by have := hmin a; omega)
  obtain ⟨t,n,P,hn,px,suf,inside,all⟩ :=
    girth_six_core_rotations hc hg S hd hmin a x q he metric hp hl hax hx
  let u : S := ⟨P.vertex 0,inside 0 (Nat.zero_le _)⟩
  let y : S := ⟨q.getVert 1,hq1⟩
  let H := G.induce (S : Set V)
  have hay : H.Adj a y := by simpa [H,y] using q.adj_getVert_succ (i:=0) (by omega)
  have hac : c x ≠ c a := (c.valid (show H.Adj a x from hax)).symm
  have anchor : P.vertex t=a.val := by simpa using suf 0 (Nat.zero_le _)
  have eq := core_parity P (by omega : t ≤ n) inside c
  have aeq : (⟨P.vertex t,inside t le_rfl⟩ : S)=a := Subtype.ext anchor
  rw [aeq] at eq
  change c u=c a ↔ _ at eq
  have plen := P.length_le
  by_contra! short
  have axnear := (dist_eq_one_iff_adj.mpr hax).le
  by_cases even : t%2=0
  · obtain ⟨lower,rot⟩ := all d le_rfl (hmin u)
    have ht : t=2*d-4 := by clear * - even hd lower hn plen short; omega
    obtain ⟨j,R,lo,up,root,rs,w,hw,huw,hwi,-⟩ := rot (Or.inr ht)
    clear all rot
    have notOne : j ≠ 1 := by
      intro h
      have wy : H.Adj y ⟨w,hw⟩ := by rw [h,suf 1 (by omega)] at hwi; exact hwi
      have col := color_common c (show H.Adj u ⟨w,hw⟩ from huw) wy
      exact c.valid hay ((eq.2 even).symm.trans col)
    by_cases ez : e=0
    · subst e
      have atTwo : j=2 := by omega
      have rA : R.vertex 0=a.val := by rwa [atTwo,show t+2-2=t by omega,anchor] at root
      have := two_steps hg hc R S a rA q metric hn hl (r:=0) (by omega) rs (by simp)
        (by have := hmin a; omega) (fun z hz => by have := boost z (c.valid hz).symm; omega)
      omega
    · rcases (show j=2 ∨ j=3 by omega) with h|h
      · have rA : R.vertex 0=a.val := by rwa [h,show t+2-2=t by omega,anchor] at root
        have := girth_six_core_growth hg hc R S a rA q metric hn (by omega) (r:=0) (by omega) rs
          (by simp) (by have := hmin a; omega)
        omega
      · have rY : R.vertex 0=y.val := by rwa [h,show t+3-2=t+1 by omega,suf 1 (by omega)] at root
        have ay : G.Adj a.val y.val := hay
        have := girth_six_core_growth hg hc R S y rY q metric hn (by omega) (by omega) rs
          ((dist_eq_one_iff_adj.mpr ay).le) (by have := boost y (c.valid hay).symm; omega)
        omega
  · have high := boost u (fun h => even (eq.1 h))
    obtain ⟨lower,rot⟩ := all (d+1) (by omega) high
    have ht : t=2*(d+1)-5 := by clear * - even hd lower hn plen short; omega
    obtain ⟨j,R,lo,up,root,rs,-⟩ := rot (Or.inl ht)
    clear all rot
    have ez : e=0 := by omega
    rcases (show j=1 ∨ j=2 by omega) with h|h
    · have rX : R.vertex 0=x.val := by rwa [h,show t+1-2=t-1 by omega,px] at root
      have := girth_six_core_growth hg hc R S x rX q metric hn (by omega) (by omega) rs axnear
        (by have := boost x hac; omega)
      omega
    · have rA : R.vertex 0=a.val := by rwa [h,show t+2-2=t by omega,anchor] at root
      have := girth_six_core_growth hg hc R S a rA q metric hn (by omega) (r:=0) (by omega) rs
        (by simp) (by have := hmin a; omega)
      omega


/-- A two-colored induced core with minimum degree d, and degree at least
d+1 on one side, gives the full odd threshold 2d−1 at radius at least five. -/
theorem girth_six_odd_colored_core (hg : 6 ≤ G.egirth) (hc : G.Connected)
    (S : Finset V) (hS : S.Nonempty) (c : (G.induce (S : Set V)).Coloring (Fin 2))
    (col : Fin 2) {d : ℕ} (hd : 4 ≤ d)
    (hmin : ∀ z : S,d+(if c z=col then 1 else 0) ≤ (G.induce (S : Set V)).degree z)
    (hr : 5 ≤ G.radius.toNat) : G.radius.toNat+2*d-1 ≤ G.path := by
  let H := G.induce (S : Set V)
  have base (z : S) : d ≤ H.degree z := (Nat.le_add_right _ _).trans (hmin z)
  obtain ⟨s,hs⟩ := hS
  let u : S := ⟨s,hs⟩
  have low : ∃ a : S,c a ≠ col := by
    by_cases h : c u=col
    · obtain ⟨y,hy⟩ := (H.degree_pos_iff_exists_adj u).mp (by have := base u; omega)
      exact ⟨y,fun e => c.valid hy (h.trans e.symm)⟩
    · exact ⟨u,h⟩
  obtain ⟨a,ha⟩ := low
  have high (z : S) (hz : c z ≠ c a) : d < H.degree z := by
    have eq : c z=col := by
      apply Fin.ext
      have := Fin.val_ne_of_ne hz; have := Fin.val_ne_of_ne ha
      have := (c z).isLt; have := (c a).isLt; have := col.isLt
      omega
    simpa [eq] using hmin z
  obtain ⟨v,q,hq,hv⟩ := exists_geodesic_ge_radius G hc a.val
  obtain ⟨y,hy⟩ := (H.degree_pos_iff_exists_adj a).mp (by have := base a; omega)
  have hay : G.Adj a.val y.val := hy
  obtain ⟨w,_,hw⟩ := hc.exists_path_of_dist y.val v
  have hW : Chordless w := ⟨w.isPath_of_length_eq_dist hw,
    fun _ _ hi hj => (adj_getVert_iff_consecutive_of_length_eq_dist w hw hi hj).1⟩
  by_cases farther : G.dist a.val v < G.dist y.val v
  · have bound := girth_six_high_side_pointed hg hc S c y hd base
      (fun z hz => high z (hz ▸ (c.valid hy).symm)) w hw (by omega)
    omega
  have tri := hc.dist_triangle (u:=a.val) (v:=y.val) (w:=v)
  rw [dist_eq_one_iff_adj.mpr hay] at tri
  let p := w.cons hay
  have plen : p.length=w.length+1 := rfl
  have near : p.length ≤ G.dist a.val v+1 := by omega
  have suffix (i) (hi : i ≤ w.length) : G.dist (w.getVert i) v=w.length-i := by
    simpa using dist_getVert_eq_sub_of_le_of_length_eq_dist w hw hi le_rfl
  have ne : a.val ≠ w.getVert 1 := by
    intro eq
    have := suffix 1 (by omega)
    rw [←eq] at this
    omega
  have off := hW.pending_off_path hay.symm ne
  have hp : Chordless p := hW.extend hay.symm off (by
    intro i hi pos h
    have := first_blocker (g:=6) hg hW hay.symm off hi pos h
    have tr := hc.dist_triangle (u:=a.val) (v:=w.getVert i) (w:=v)
    rw [dist_eq_one_iff_adj.mpr h,suffix i hi] at tr
    omega)
  have q1 : p.getVert 1∈S := by change w.getVert 0∈S; simp
  by_cases equal : G.dist a.val v=G.dist y.val v
  · have := girth_six_low_side_pointed hg hc S c a hd base high p (e:=1) le_rfl near hp (by omega) q1
    omega
  · have := girth_six_low_side_pointed hg hc S c a hd base high p (e:=0) (by decide) (by omega)
      hp (by omega) q1
    omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem noFour_of_six (hg : 6 ≤ G.egirth) : NoFourCycle G := by
  intro a b w z hab haw hbw haz hbz
  by_contra ne
  let p : G.Walk a b := .cons haw (.cons hbw.symm .nil)
  let q : G.Walk a b := .cons haz (.cons hbz.symm .nil)
  have hp : p.IsPath := by simp [p,Walk.isPath_def,haw.ne,hbw.ne.symm,hab]
  have hq : q.IsPath := by simp [q,Walk.isPath_def,haz.ne,hbz.ne.symm,hab]
  have different : p ≠ q := fun e => ne (congrArg (fun r : G.Walk a b => r.getVert 1) e)
  obtain ⟨_,_,_,r,hr,le⟩ := hp.exists_isCycle_length_le_add_of_ne hq different
  have hlen : 6 ≤ r.length := ENat.natCast_le_natCast.mp (hg.trans (egirth_le_length hr))
  change r.length ≤ 2+2 at le
  omega

/-- An odd average-degree threshold attained on a bipartite induced
subgraph gives the exact radius bound for the whole graph, at every radius. -/
theorem girth_six_odd_bipartite_induce (hg : 6 ≤ G.egirth) (hc : G.Connected)
    (U : Finset V) (hU : U.Nonempty) (hb : (G.induce (U : Set V)).IsBipartite)
    {m : ℕ} (hav : (2*m+1)*U.card ≤ ∑ z : U,(G.induce (U : Set V)).degree z) :
    G.radius.toNat+(2*m+1) ≤ G.path := by
  classical
  have : Nonempty V := hc.nonempty
  have : Nonempty U := hU.to_subtype
  by_cases zero : m=0
  · simpa [zero] using radius_add_one_le_path G hc
  obtain ⟨S,hS,c,col,hmin⟩ := exists_odd_colored_core_of_induce U hU hb (by omega : 0<m) hav
  have chung := chung_bound_nat G hc
  by_cases large : 3 ≤ m ∧ 5 ≤ G.radius.toNat
  · have := girth_six_odd_colored_core hg hc S hS c col (Nat.succ_le_succ large.1) hmin large.2
    omega
  let H := G.induce (U : Set V)
  have hg' : 6 ≤ H.egirth := hg.trans (IsContained.egirth_le ⟨Copy.induce G (U : Set V)⟩)
  have mono : H.path ≤ G.path := G.path_induce_le (U : Set V)
  by_cases medium : 2 ≤ m
  · obtain ⟨C⟩ := hb
    have hsum : (2*m+1)*Fintype.card U ≤ ∑ z : U,H.degree z := by simpa using hav
    have bound := add_five_le_path_of_bipartite_density (G:=H) ⟨C⟩ (noFour_of_six hg')
      (by omega : 5 ≤ 2*m+1) (le_l_of_sum_degree C hsum)
    omega
  let K := G.induce (S : Set V)
  obtain ⟨a,ha⟩ := hS
  let x : S := ⟨a,ha⟩
  have base (z : S) : 2 ≤ K.degree z := by
    have h : m+1 ≤ K.degree z := (Nat.le_add_right _ _).trans (hmin z)
    omega
  have high : ∃ y : S,c y=col := by
    by_cases h : c x=col
    · exact ⟨x,h⟩
    · obtain ⟨y,hy⟩ := (K.degree_pos_iff_exists_adj x).mp (by have := base x; omega)
      refine ⟨y,Fin.ext ?_⟩
      have := Fin.val_ne_of_ne (c.valid hy); have := Fin.val_ne_of_ne h
      have := (c x).isLt; have := (c y).isLt; have := col.isLt
      omega
  obtain ⟨y,hy⟩ := high
  have deg : 2 < K.degree y := by
    have h : m+1+1 ≤ K.degree y := by simpa [hy] using hmin y
    omega
  have gK : 6 ≤ K.egirth := hg.trans (IsContained.egirth_le ⟨Copy.induce G (S : Set V)⟩)
  have h := girth_six_min_degree_bound gK (d:=2) le_rfl base y
  rw [if_pos deg] at h
  have mK : K.path ≤ G.path := G.path_induce_le (S : Set V)
  omega


/-- Under a one-vertex shortfall at the odd threshold, a vertex witnessing
many high-degree neighbors at an adjacent vertex must be central. -/
theorem girth_six_center_of_high_neighbors (hg : 6 ≤ G.egirth) (hc : G.Connected)
    (S : Finset V) {d : ℕ} (hd : 4 ≤ d) (hmin : ∀ z : S,d ≤ (G.induce (S : Set V)).degree z)
    (hr : 5 ≤ G.radius.toNat) (short : G.path ≤ G.radius.toNat+2*d-2)
    (a x : S) (hax : (G.induce (S : Set V)).Adj a x) (A : Finset S) (hcard : d ≤ A.card)
    (hA : ∀ z∈A,(G.induce (S : Set V)).Adj x z ∧ (z=a ∨ d<(G.induce (S : Set V)).degree z))
    (v : V) : G.dist a.val v ≤ G.radius.toNat := by
  by_contra! far
  have cap (y : S) : G.dist y.val v ≤ G.radius.toNat+1 := by
    by_cases large : 5 ≤ G.dist y.val v
    · obtain ⟨p,_,hp⟩ := hc.exists_path_of_dist y.val v
      have chord : Chordless p := ⟨p.isPath_of_length_eq_dist hp,
        fun _ _ hi hj => (adj_getVert_iff_consecutive_of_length_eq_dist p hp hi hj).1⟩
      have := girth_six_pointed_core hc hg S hd hmin y p (e:=0) (by decide) hp.le chord
        (by omega) (by simp)
      omega
    · omega
  obtain ⟨y,hay,hyx⟩ := pick_neighbor (G:=G) S a x.val (by have := hmin a; omega)
  have hcy := cap y
  have diff : G.dist a.val v ≠ G.dist y.val v := by
    intro eq
    have := girth_six_equal_layer_gain hc hg S hd hmin a y hay eq (by omega)
    omega
  have tri := hc.dist_triangle (u:=a.val) (v:=y.val) (w:=v)
  rw [dist_eq_one_iff_adj.mpr hay] at tri
  obtain ⟨q,_,hq⟩ := hc.exists_path_of_dist y.val v
  let p := q.cons hay
  have hp : p.length=G.dist a.val v := by change q.length+1=_; omega
  have avoid : x.val ≠ p.getVert 1 := by
    have e : p.getVert 1=y.val := by simp [p]
    exact fun h => hyx (h.trans e).symm
  have := girth_six_geodesic_high_neighbors hc hg S hd hmin a x p hp (by omega) hax avoid
    (by omega) A hA
  omega

/-- In a minimum-degree core whose degree-d vertices form an independent
set, every neighbor of every degree-d vertex is central under an odd
one-vertex shortfall. -/
theorem girth_six_low_neighbors_central (hg : 6 ≤ G.egirth) (hc : G.Connected)
    (S : Finset V) {d : ℕ} (hd : 4 ≤ d) (hmin : ∀ z : S,d ≤ (G.induce (S : Set V)).degree z)
    (independent : ∀ x y : S,(G.induce (S : Set V)).degree x=d →
      (G.induce (S : Set V)).degree y=d → ¬(G.induce (S : Set V)).Adj x y)
    (hr : 5 ≤ G.radius.toNat) (short : G.path ≤ G.radius.toNat+2*d-2)
    (a x : S) (hax : (G.induce (S : Set V)).Adj a x) (hx : (G.induce (S : Set V)).degree x=d)
    (v : V) : G.dist a.val v ≤ G.radius.toNat := by
  let H := G.induce (S : Set V)
  apply girth_six_center_of_high_neighbors hg hc S hd hmin hr short a x hax (H.neighborFinset x)
    (by rw [H.card_neighborFinset_eq_degree]; exact hx.ge) _ v
  intro z hz
  have adj := (H.mem_neighborFinset _ _).mp hz
  have ne : H.degree z ≠ d := fun eq => independent x z hx eq adj
  have deg : d ≤ H.degree z := hmin z
  exact ⟨adj,Or.inr (by change d < H.degree z; omega)⟩


/-- A core with independent degree-d vertices also gains 2d−2 vertices
when the initial path is one edge longer than the distance, provided it
starts at a degree-d vertex and uses a first edge inside the core. -/
theorem girth_six_independent_low_almost_geodesic (hg : 6 ≤ G.egirth) (hc : G.Connected)
    (S : Finset V) {d : ℕ} (hd : 4 ≤ d) (hmin : ∀ z : S,d ≤ (G.induce (S : Set V)).degree z)
    (independent : ∀ x y : S,(G.induce (S : Set V)).degree x=d →
      (G.induce (S : Set V)).degree y=d → ¬(G.induce (S : Set V)).Adj x y)
    (a : S) {v : V} (q : G.Walk a.val v) {e : ℕ} (he : e ≤ 1)
    (metric : q.length ≤ G.dist a.val v+e) (hp : Chordless q) (hl : 5 ≤ q.length)
    (extra : e=1 → (G.induce (S : Set V)).degree a=d ∧ q.getVert 1∈S) :
    q.length+2*d-2 ≤ G.path := by
  let H := G.induce (S : Set V)
  obtain ⟨x,hax,hx⟩ := pick_neighbor (G:=G) S a (q.getVert 1) (by have := hmin a; omega)
  have more {z : S} (haz : H.Adj a z) (ez : e=1) : d < H.degree z := by
    have deg : d ≤ H.degree z := hmin z
    have ne : H.degree z ≠ d := fun eq => independent a z (extra ez).1 eq haz
    omega
  have first : G.Adj a.val (q.getVert 1) := by simpa using q.adj_getVert_succ (i:=0) (by omega)
  obtain ⟨t,n,P,hn,px,suf,inside,all⟩ :=
    girth_six_core_rotations hc hg S hd hmin a x q he metric hp hl hax hx
  let u : S := ⟨P.vertex 0,inside 0 (Nat.zero_le _)⟩
  have anchor : P.vertex t=a.val := by simpa using suf 0 (Nat.zero_le _)
  have plen := P.length_le
  by_contra! short
  obtain ⟨lower,rotate⟩ := all d le_rfl (hmin u)
  have ht : t=2*d-5 ∨ t=2*d-4 := by clear * - hd hn plen short lower; omega
  obtain ⟨j,R,lo,up,root,rs,w,hw,huw,hwi,wr,tight⟩ := rotate ht
  clear rotate
  have rX (h : j=1) : R.vertex 0=x.val := by rwa [h,show t+1-2=t-1 by omega,px] at root
  have rA (h : j=2) : R.vertex 0=a.val := by rwa [h,show t+2-2=t by omega,anchor] at root
  have nearX := (dist_eq_one_iff_adj.mpr hax).le
  rcases ht with ht|ht
  · have jb := tight ht
    rcases (show j=1 ∨ j=2 by omega) with h|h
    · have hu : H.degree u=d := by
        by_contra! ne
        have deg : d ≤ H.degree u := hmin u
        have := (all (d+1) (by omega) (by change d+1 ≤ H.degree u; omega)).1
        omega
      let b : S := ⟨w,hw⟩
      have bdeg : d < H.degree b := by
        have deg : d ≤ H.degree b := hmin b
        have ne : H.degree b ≠ d := fun e => independent u b hu e huw
        omega
      have wb : G.Adj (q.getVert 1) b.val := by rwa [h,suf 1 (by omega)] at hwi
      have nearB : G.dist a.val b.val ≤ 2 := by
        have edge : G.Adj a.val (q.getVert 1) := by simpa using q.adj_getVert_succ (i:=0) (by omega)
        have tr := hc.dist_triangle (u:=a.val) (v:=q.getVert 1) (w:=b.val)
        rwa [dist_eq_one_iff_adj.mpr edge,dist_eq_one_iff_adj.mpr wb] at tr
      obtain ⟨z,hz,g⟩ := girth_six_grow_among hg hc R q metric hn (by omega) (by omega) rs
        (rX h ▸ nearX) (coreNeighbors (G:=G) S x) (fun z hz => rX h ▸ (mem_coreNeighbors hz).1)
        (by rw [coreNeighbors_card]; have := hmin x; omega)
      let y : S := ⟨z,(mem_coreNeighbors hz).2⟩
      let Q := grow R z g
      have ynear : G.dist a.val y.val ≤ 2 := by
        have edge : G.Adj x.val y.val := (mem_coreNeighbors hz).1
        have tr := hc.dist_triangle (u:=a.val) (v:=x.val) (w:=y.val)
        rw [dist_eq_one_iff_adj.mpr edge] at tr
        omega
      have ysuf (k) (hk : j ≤ k) (hL : k ≤ q.length) : Q.vertex (t+1+k)=q.getVert k := by
        rw [show t+1+k=(t+k)+1 by omega]; exact rs k hk hL
      have sat (z) (_ : z∈S) (hz : Good Q z) : False := by
        have := (grow Q z hz).length_le
        clear * - ht hn short this hd; omega
      obtain ⟨i,Z,ki,ik,rootZ,fs⟩ := girth_six_interval_rotation hg hc Q S y rfl q metric
        (t:=t+1) (by omega) (by omega) (by omega) ysuf ynear (hmin y) sat (s:=e) (by omega)
        he (k:=t+3) (by omega) (by omega) (by omega)
      have zsuf (k) (hk : 3 ≤ k) (hL : k ≤ q.length) : Z.vertex (t+1+k)=q.getVert k :=
        (fs _ (by omega)).trans (ysuf _ (by omega) hL)
      by_cases lowSlot : i=t+3
      · have rB : Z.vertex 0=b.val := by
          rw [rootZ,show i-2=t+1 by omega]
          change R.vertex t=w
          rwa [h,show t+1-1=t by omega] at wr
        have := girth_six_core_growth hg hc Z S b rB q metric (t:=t+1) (by omega) (by omega)
          (by omega) zsuf nearB (by change _ < H.degree b; omega)
        clear * - ht hn short hd this; omega
      · have ez : e=1 := by omega
        let y' : S := ⟨q.getVert 1,(extra ez).2⟩
        have rY : Z.vertex 0=y'.val := by
          rw [rootZ,show i-2=t+1+1 by omega]
          exact ysuf 1 (by omega) (by omega)
        have := girth_six_core_growth hg hc Z S y' rY q metric (t:=t+1) (by omega) (by omega)
          (by omega) zsuf ((dist_eq_one_iff_adj.mpr first).le) (by
            have deg := more (z:=y') first ez; change _ < H.degree y'; omega)
        clear * - ht hn short hd this; omega
    · have := two_steps hg hc R S a (rA h) q metric hn hl (r:=0) (by omega) rs (by simp)
        (by have := hmin a; omega) (fun z hz => by
          by_cases ez : e=1
          · have deg := more hz ez; change _ < H.degree z; omega
          · have := hmin z; omega)
      clear * - ht hn short hd this; omega
  · rcases (show j=1 ∨ j=2 ∨ j=3 ∧ e=1 by omega) with h|h|⟨h,ez⟩
    · have := girth_six_core_growth hg hc R S x (rX h) q metric hn (by omega) (by omega) rs nearX (by
        by_cases ez : e=1
        · have deg := more (z:=x) hax ez; change _ < H.degree x; omega
        · have := hmin x; omega)
      clear * - ht hn short hd this; omega
    · have := girth_six_core_growth hg hc R S a (rA h) q metric hn (by omega) (r:=0) (by omega)
        rs (by simp) (by have := hmin a; omega)
      clear * - ht hn short hd this; omega
    · let y : S := ⟨q.getVert 1,(extra ez).2⟩
      have rY : R.vertex 0=y.val := by rwa [h,show t+3-2=t+1 by omega,suf 1 (by omega)] at root
      have := girth_six_core_growth hg hc R S y rY q metric hn (by omega) (by omega) rs
        ((dist_eq_one_iff_adj.mpr first).le) (by have := more (z:=y) first ez; change _ < H.degree y; omega)
      clear * - ht hn short hd this; omega

/-- When the degree-d core vertices are independent, every geodesic
starting in the core gains 2d−2 vertices. -/
theorem girth_six_independent_low_pointed (hg : 6 ≤ G.egirth) (hc : G.Connected)
    (S : Finset V) {d : ℕ} (hd : 4 ≤ d) (hmin : ∀ z : S,d ≤ (G.induce (S : Set V)).degree z)
    (independent : ∀ x y : S,(G.induce (S : Set V)).degree x=d →
      (G.induce (S : Set V)).degree y=d → ¬(G.induce (S : Set V)).Adj x y)
    (a : S) {v : V} (q : G.Walk a.val v) (hq : q.length=G.dist a.val v) (hl : 5 ≤ q.length) :
    q.length+2*d-2 ≤ G.path := by
  have hp : Chordless q := ⟨q.isPath_of_length_eq_dist hq,
    fun _ _ hi hj => (adj_getVert_iff_consecutive_of_length_eq_dist q hq hi hj).1⟩
  exact girth_six_independent_low_almost_geodesic hg hc S hd hmin independent a q
    (e:=0) (by decide) hq.le hp hl (by simp)


/-- An odd counterexample at girth six contains a dense core consisting
entirely of centers. An edge incident with a minimum-degree core vertex
cannot lie inside the most distant layer from either endpoint's antipode. -/
theorem girth_six_central_core_of_odd_shortfall [Nonempty V] (hg : 6 ≤ G.egirth)
    (hc : G.Connected) {d : ℕ} (hd : 4 ≤ d)
    (hav : (2*d-1)*Fintype.card V ≤ ∑ v,G.degree v)
    (hr : 5 ≤ G.radius.toNat) (short : G.path ≤ G.radius.toNat+2*d-2) :
    ∃ S : Finset V, S.Nonempty ∧
      (2*d-1)*S.card ≤ ∑ z : S,(G.induce (S : Set V)).degree z ∧
      (∀ z : S,d ≤ (G.induce (S : Set V)).degree z) ∧
      (∀ x y : S,(G.induce (S : Set V)).degree x=d → (G.induce (S : Set V)).degree y=d →
        ¬(G.induce (S : Set V)).Adj x y) ∧
      (∀ a : S,∀ v,G.dist a.val v ≤ G.radius.toNat) ∧
      ∀ a y : S,(G.induce (S : Set V)).degree a=d → (G.induce (S : Set V)).Adj a y →
        ∀ v,(G.dist a.val v=G.radius.toNat → G.dist y.val v+1=G.radius.toNat) ∧
          (G.dist y.val v=G.radius.toNat → G.dist a.val v+1=G.radius.toNat) := by
  classical
  obtain ⟨S,hS,dense,min,limits⟩ := exists_odd_neighborhood_core G (by omega : 2 ≤ d) hav
  let H := G.induce (S : Set V)
  have ind (a y : S) (ha : H.degree a=d) (hy : H.degree y=d) (adj : H.Adj a y) : False := by
    have h := limits a {y} (by intro z hz; simp only [Finset.mem_singleton] at hz; subst z; exact ⟨adj,hy⟩)
    change ({y} : Finset S).card ≤ 2*(H.degree a-d) at h
    simp [ha] at h
  have center (a : S) (v : V) : G.dist a.val v ≤ G.radius.toNat := by
    by_cases large : 5 ≤ G.dist a.val v
    · obtain ⟨q,_,hq⟩ := hc.exists_path_of_dist a.val v
      have := girth_six_independent_low_pointed hg hc S hd min ind a q hq (by omega)
      omega
    · omega
  refine ⟨S,hS,dense,min,ind,center,?_⟩
  intro a y low adj v
  have ca := center a v
  have cy := center y v
  have hay : G.Adj a.val y.val := adj
  have tri := hc.dist_triangle (u:=a.val) (v:=y.val) (w:=v)
  rw [dist_eq_one_iff_adj.mpr hay] at tri
  have tri' := hc.dist_triangle (u:=y.val) (v:=a.val) (w:=v)
  rw [dist_eq_one_iff_adj.mpr hay.symm] at tri'
  suffices diff : ¬(G.dist a.val v=G.radius.toNat ∧ G.dist y.val v=G.radius.toNat) by omega
  rintro ⟨far,far'⟩
  have tie : G.dist a.val v=G.dist y.val v := far.trans far'.symm
  obtain ⟨q,_,hq⟩ := hc.exists_path_of_dist y.val v
  have hp : Chordless q := ⟨q.isPath_of_length_eq_dist hq,
    fun _ _ hi hj => (adj_getVert_iff_consecutive_of_length_eq_dist q hq hi hj).1⟩
  have suffix (i) (hi : i ≤ q.length) : G.dist (q.getVert i) v=q.length-i := by
    simpa using dist_getVert_eq_sub_of_le_of_length_eq_dist q hq hi le_rfl
  have ne : a.val ≠ q.getVert 1 := by
    intro eq
    have := suffix 1 (by omega)
    rw [←eq] at this
    omega
  have off := hp.pending_off_path hay.symm ne
  have hQ : Chordless (q.cons hay) := hp.extend hay.symm off (by
    intro i hi pos hiw
    have := first_blocker (g:=6) hg hp hay.symm off hi pos hiw
    have tr := hc.dist_triangle (u:=a.val) (v:=q.getVert i) (w:=v)
    rw [dist_eq_one_iff_adj.mpr hiw,suffix i hi] at tr
    omega)
  have len : (q.cons hay).length=q.length+1 := rfl
  have := girth_six_independent_low_almost_geodesic hg hc S hd min ind a (q.cons hay)
    (e:=1) le_rfl (by omega) hQ (by omega) (fun _ => ⟨low,by simp⟩)
  omega

end Wall133
