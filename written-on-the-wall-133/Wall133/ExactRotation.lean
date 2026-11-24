import Wall133.EvenTailRotation

namespace Wall133
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Grow into a specified subset of the core when few early even indices
are available to block its neighbors. -/
private theorem grow_in_subset {n : ℕ} (P : Chain G n) (hc : G.Connected)
    (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G) (hn : 2 ≤ n)
    (S : Finset V) (u : S) (hu : P.vertex 0=u.val) (A : Finset S)
    {b : ℕ} (hcard : b < A.card) (hA : ∀z∈A,(G.induce (S : Set V)).Adj u z)
    (bound : ∀ i, P.Blocks i → i ≤ 2*b+1) :
    ∃ Q : Chain G (n+1), ∃ y∈A, Q.vertex 0=y.val ∧ ∀ i,Q.vertex (i+1)=P.vertex i := by
  let N := A.map (Function.Embedding.subtype (· ∈ S))
  have hncard : N.card=A.card := Finset.card_map _
  have neighbors (w) (hw : w∈N) : G.Adj (P.vertex 0) w ∧ w∈(N : Set V) := by
    refine ⟨?_,hw⟩
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hw
    exact hu ▸ hA _ hy
  obtain ⟨Q,hQ,hshift⟩ := P.extendByCode hc c h4 hn (N : Set V) N
    (show b<N.card by omega) neighbors (fun i=> i/2-1)
    (fun i hi => by have := bound i hi; have := hi.2.2.1; have := hi.2.1; omega)
    (fun i j hi hj he => by have := hi.2.2.1; have := hj.2.2.1; have := hi.2.1; have := hj.2.1; omega)
  obtain ⟨y,hy,he⟩ := Finset.mem_map.mp hQ
  exact ⟨Q,y,hy,he.symm,hshift⟩

private theorem two_growths {n t : ℕ} (R : Chain G n) (hc : G.Connected)
    (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G) (S : Finset V) (a x : S) {v : V}
    (q : G.Walk a.val v) (hq : q.length=G.dist a.val v) (hl : 5 ≤ q.length)
    (hlen : n=t+q.length) (hx : R.vertex 0=x.val) (skip r : ℕ) (hskip : skip ≤ r+2)
    (hnear : G.dist a.val x.val ≤ r)
    (hsuf : ∀ j, skip ≤ j → j ≤ q.length → R.vertex (t+j)=q.getVert j)
    (A : Finset S) {b₀ b₁ : ℕ} (hA : b₀ < A.card)
    (hadj : ∀z∈A,(G.induce (S : Set V)).Adj x z)
    (hhigh : ∀z∈A, b₁ < (G.induce (S : Set V)).degree z ∨ (z=a ∧ skip ≤ 1))
    (h₀ : t+r+2 ≤ 2*b₀+1) (h₁ : t+r+4 ≤ 2*b₁+1) : n+3 ≤ G.path := by
  have rb (i) (hi : R.Blocks i) := R.block_limit hc q hq t skip r hlen hsuf hskip (hx ▸ hnear) hi
  obtain ⟨Q,y,hy,hQ,hshift⟩ := grow_in_subset R hc c h4 (by omega) S x hx A hA hadj
    (fun i hi => (rb i hi).trans h₀)
  have ysuf (j) (hj : skip ≤ j) (hj' : j ≤ q.length) : Q.vertex (t+1+j)=q.getVert j := by
    rw [show t+1+j=(t+j)+1 by omega,hshift]
    exact hsuf j hj hj'
  have hxy : G.Adj x.val y.val := hadj y hy
  have yn : G.dist a.val (Q.vertex 0) ≤ r+1 := by
    have tri := hc.dist_triangle (u := a.val) (v := x.val) (w := y.val)
    rw [dist_eq_one_iff_adj.mpr hxy] at tri
    rw [hQ]; omega
  have yhigh : b₁ < (G.induce (S : Set V)).degree y := by
    rcases hhigh y hy with h|⟨he,hj⟩
    · exact h
    have ha : G.Adj (Q.vertex 0) (Q.vertex (t+1+1)) := by
      rw [ysuf 1 hj (by omega),hQ,he]
      simpa using q.adj_getVert_succ (i := 0) (by omega)
    have := (Q.edges (Nat.zero_le _) (by omega)).1 ha
    omega
  let H := G.induce (S : Set V)
  have qb (i) (hi : Q.Blocks i) := Q.block_limit hc q hq (t+1) skip (r+1) (by omega)
    ysuf (by omega) yn hi
  obtain ⟨Z,_,_,_,_⟩ := grow_in_subset Q hc c h4 (by omega) S y hQ (H.neighborFinset y)
    (show b₁ < (H.neighborFinset y).card by rw [H.card_neighborFinset_eq_degree]; exact yhigh)
    (fun w hw => (H.mem_neighborFinset _ _).mp hw) (fun i hi => by have := qb i hi; omega)
  exact Z.length_le

/-- Under a one-vertex shortfall, among the neighbors of the prescribed
first step at most d−1 can be high-degree vertices or the anchor itself. -/
theorem geodesic_high_neighbors_bound (hc : G.Connected) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) (S : Finset V) {d : ℕ} (hd : 4 ≤ d)
    (hmin : ∀ u : S, d ≤ (G.induce (S : Set V)).degree u) (a x : S) {v : V}
    (q : G.Walk a.val v) (hq : q.length=G.dist a.val v) (hl : 5 ≤ q.length)
    (hax : G.Adj a.val x.val) (hx : x.val ≠ q.getVert 1)
    (hshort : G.path ≤ q.length+2*d-3) (A : Finset S)
    (hA : ∀z∈A,(G.induce (S : Set V)).Adj x z ∧ (z=a ∨ d<(G.induce (S : Set V)).degree z)) :
    A.card ≤ d-1 := by
  classical
  by_contra! hcard
  obtain ⟨t,n,P,hn,hX,hsuf,hpre,sat,hmetric⟩ := exists_seeded_geodesic_tail hc c h4 S a x q hq hl hax hx
  let u : S := ⟨P.vertex 0,hpre 0 (by omega)⟩
  let N := coreNeighbors (G := G) S u
  have hN (w) (hw : w∈N) : G.Adj (P.vertex 0) w := (mem_coreNeighbors hw).1
  have hin (w) (hw : w∈N) : w∈S := (mem_coreNeighbors hw).2
  have hs (w) (hw : w∈N) := sat w (hin _ hw)
  have nc : N.card = (G.induce (S : Set V)).degree u := coreNeighbors_card S u
  have hdn : d ≤ N.card := nc ▸ hmin u
  have hu := P.card_le_of_metricSuffix hc c h4 (by omega) N hN hs hmetric
  have len := P.length_le
  rcases (show t=2*d-5 ∨ t=2*d-4 by omega) with ht|ht
  · obtain ⟨R,hR,_,hRs,_⟩ := rotate_odd_geodesic_tail P hc c h4 S a x q hq hl hax
      hd ht hn hX hsuf hpre hmetric N hN hin hs hdn
    have near : G.dist a.val x.val ≤ 1 := (dist_eq_one_iff_adj.mpr hax).le
    have := two_growths R hc c h4 S a x q hq hl hn hR 1 1 (by decide) near hRs
      A (b₀ := d-1) (b₁ := d) hcard (fun z hz => (hA z hz).1)
      (fun z hz => ((hA z hz).2).elim (fun e => Or.inr ⟨e,le_rfl⟩) Or.inl) (by omega) (by omega)
    omega
  · obtain ⟨R,hR,_,_,hbound⟩ := rotate_even_geodesic_tail P hc c h4 S a q hq hl hd ht hn
      hsuf hpre hmetric N hN hin hs hdn
    let H := G.induce (S : Set V)
    obtain ⟨Z,_,_,_,_⟩ := grow_in_subset R hc c h4 (by omega) S a hR (H.neighborFinset a)
      (show d-1 < (H.neighborFinset a).card by rw [H.card_neighborFinset_eq_degree]; have hab : d ≤ H.degree a := hmin a; omega)
      (fun w hw => (H.mem_neighborFinset _ _).mp hw)
      (fun i hi => by have := hbound i hi; omega)
    have := Z.length_le
    omega

/-- In an asymmetric minimum-degree core, rotating from a low-side anchor
and using the higher degree on its neighbors gives the full odd threshold. -/
theorem geodesic_exact_odd_core (hc : G.Connected) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) (S : Finset V) {d : ℕ} (hd : 4 ≤ d)
    (hmin : ∀ u : S, d ≤ (G.induce (S : Set V)).degree u) (a x : S) {v : V}
    (q : G.Walk a.val v) (hq : q.length=G.dist a.val v) (hl : 5 ≤ q.length)
    (hax : G.Adj a.val x.val) (hx : x.val ≠ q.getVert 1)
    (boost : ∀y : S, c y.val ≠ c a.val → d+1 ≤ (G.induce (S : Set V)).degree y) :
    q.length+(2*d-1) ≤ G.path := by
  classical
  by_contra! hshort
  obtain ⟨t,n,P,hn,hX,hsuf,hpre,sat,hmetric⟩ := exists_seeded_geodesic_tail hc c h4 S a x q hq hl hax hx
  let u : S := ⟨P.vertex 0,hpre 0 (by omega)⟩
  let N := coreNeighbors (G := G) S u
  have hN (w) (hw : w∈N) : G.Adj (P.vertex 0) w := (mem_coreNeighbors hw).1
  have hin (w) (hw : w∈N) : w∈S := (mem_coreNeighbors hw).2
  have hs (w) (hw : w∈N) := sat w (hin _ hw)
  have nc : N.card = (G.induce (S : Set V)).degree u := coreNeighbors_card S u
  have hdn : d ≤ N.card := nc ▸ hmin u
  have hu := P.card_le_of_metricSuffix hc c h4 (by omega) N hN hs hmetric
  have len := P.length_le
  let H := G.induce (S : Set V)
  by_cases he : t%2=0
  · have ht : t=2*d-4 := by omega
    obtain ⟨R,hR,hRs,_,_⟩ := rotate_even_geodesic_tail P hc c h4 S a q hq hl hd ht hn
      hsuf hpre hmetric N hN hin hs hdn
    have := two_growths R hc c h4 S a a q hq hl hn hR 2 0 (by decide) (by simp) hRs
      (H.neighborFinset a) (b₀ := d-1) (b₁ := d)
      (by rw [H.card_neighborFinset_eq_degree]; have hab : d ≤ H.degree a := hmin a; omega)
      (fun w hw => (H.mem_neighborFinset _ _).mp hw)
      (fun w hw => Or.inl (boost w (c.valid (show G.Adj a.val w.val from (H.mem_neighborFinset _ _).mp hw)).symm))
      (by omega) (by omega)
    omega
  · have col : c u.val ≠ c a.val := by
      intro eq
      have h := P.color_val c t (by omega)
      have an : P.vertex t=a.val := by simpa using hsuf 0 (Nat.zero_le _)
      rw [an] at h
      change (c a.val).val = ((c u.val).val+t)%2 at h
      rw [eq] at h
      have := (c a.val).isLt
      omega
    have highU : d+1 ≤ N.card := nc ▸ boost u col
    have ht : t=2*(d+1)-5 := by omega
    obtain ⟨R,hR,_,_,hbound⟩ := rotate_odd_geodesic_tail P hc c h4 S a x q hq hl hax
      (by omega : 4 ≤ d+1) ht hn hX hsuf hpre hmetric N hN hin hs highU
    obtain ⟨Z,_,_,_,_⟩ := grow_in_subset R hc c h4 (by omega) S x hR (H.neighborFinset x)
      (show d < (H.neighborFinset x).card by rw [H.card_neighborFinset_eq_degree]; exact boost x (c.valid hax).symm)
      (fun w hw => (H.mem_neighborFinset _ _).mp hw)
      (fun i hi => by have := hbound i hi; omega)
    have := Z.length_le
    omega

/-- The exact WOWII bound at every odd density threshold and arbitrary radius. -/
theorem radius_add_odd_density_le_path_exact [Nonempty V] (hc : G.Connected)
    (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G) {m : ℕ} (hm : 3 ≤ m)
    (hdeg : (2*m+1)*Fintype.card V ≤ ∑ v,G.degree v) (hr : 5 ≤ G.radius.toNat) :
    G.radius.toNat+(2*m+1) ≤ G.path := by
  classical
  obtain ⟨col,S,hS,hmin⟩ := exists_odd_degree_core c (by omega : 0<m) hdeg
  let H := G.induce (S : Set V)
  have base (w : S) : m+1 ≤ H.degree w := (Nat.le_add_right _ _).trans (hmin w)
  have low : ∃ a : S, c a.val ≠ col := by
    obtain ⟨w,hw⟩ := hS
    let u : S := ⟨w,hw⟩
    by_cases hu : c u.val=col
    · obtain ⟨z,hz⟩ := (H.degree_pos_iff_exists_adj u).mp (by have := base u; omega)
      exact ⟨z,fun eq => c.valid (show G.Adj u.val z.val from hz) (hu.trans eq.symm)⟩
    · exact ⟨u,hu⟩
  obtain ⟨a,ha⟩ := low
  obtain ⟨v,q,hq,hrq⟩ := exists_geodesic_ge_radius G hc a.val
  have pick : ∃x∈H.neighborFinset a,(x:S).val ≠ q.getVert 1 := by
    by_contra! hex
    have card : (H.neighborFinset a).card ≤ 1 := Finset.card_le_one.mpr
      (fun z hz y hy => Subtype.ext ((hex z hz).trans (hex y hy).symm))
    rw [H.card_neighborFinset_eq_degree] at card
    have := base a
    omega
  obtain ⟨x,hx,hx'⟩ := pick
  have high (y : S) (hy : c y.val ≠ c a.val) : m+1+1 ≤ H.degree y := by
    have hcol : c y.val=col := by
      apply Fin.ext
      have := Fin.val_ne_of_ne hy; have := Fin.val_ne_of_ne ha
      have := (c y.val).isLt; have := (c a.val).isLt; have := col.isLt
      omega
    simpa [hcol] using hmin y
  have := geodesic_exact_odd_core hc c h4 S (by omega : 4≤m+1) base a x q hq (by omega)
    (show G.Adj a.val x.val from (H.mem_neighborFinset _ _).mp hx) hx' high
  omega



theorem radius_add_floor_le_path_of_bipartite_odd [Nonempty V] (hc : G.Connected)
    (hb : G.IsBipartite) (h4 : NoFourCycle G) (ho : ⌊l G⌋₊ % 2 = 1) :
    G.radius.toNat+⌊l G⌋₊ ≤ G.path := by
  by_cases hr : G.radius.toNat ≤ 6
  · exact radius_add_floor_le_path_of_bipartite_radius_le_six hc hb h4 hr
  by_cases hm : 3 ≤ ⌊l G⌋₊/2
  · have eq : 2*(⌊l G⌋₊/2)+1=⌊l G⌋₊ := by omega
    have hdeg := sum_degree_ge_of_le_l (G := G) (k := ⌊l G⌋₊)
      (Nat.floor_le (div_nonneg (Finset.sum_nonneg (fun v _ => Nat.cast_nonneg (G.indepNeighborsCard v))) (Nat.cast_nonneg _)))
    obtain ⟨c⟩ := hb
    have := radius_add_odd_density_le_path_exact hc c h4 hm (by rwa [eq]) (by omega)
    omega
  · have := chung_bound_nat G hc
    omega

end Wall133
