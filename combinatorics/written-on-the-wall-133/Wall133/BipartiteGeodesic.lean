module

public import Wall133.Biregular
public import Wall133.Girth

@[expose] public section

/-!
# Geodesics and dense induced subgraphs in the bipartite case

Maximally extend a geodesic at an endpoint in a dense induced subgraph.
Every obstructed neighbor in that subgraph has a distinct even attachment
index. At most three indices occur on the geodesic. If the geodesic is a
shortest path to the subgraph, at most one occurs there.
-/

namespace Wall133
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

private theorem walk_color (c : G.Coloring (Fin 2)) {u v : V} (p : G.Walk u v)
    (i : ℕ) (hi : i ≤ p.length) : (c (p.getVert i)).val = ((c u).val + i) % 2 := by
  induction i with
  | zero => simp [Nat.mod_eq_of_lt (c u).isLt]
  | succ i ih =>
    have hprev := ih (by omega)
    have hdiff := Fin.val_ne_of_ne (c.valid (p.adj_getVert_succ (i := i) (by omega)))
    have := (c (p.getVert (i+1))).isLt
    have := (c u).isLt
    omega

/-- Count distinct positive even indices. Those outside the first `t`
positions are contained in a single interval of width `width`. -/
private theorem count_even_sites {W : Finset V} (idx : W → ℕ) (hinj : Function.Injective idx)
    (hpos : ∀ w, 0 < idx w) (heven : ∀ w, idx w % 2 = 0)
    (t b width : ℕ) (hwin : ∀ w, t ≤ idx w → b ≤ idx w ∧ idx w ≤ b+width) :
    W.card ≤ (t-1)/2 + width/2+1 := by
  let code (w : W) := if idx w < t then (idx w)/2-1
    else (t-1)/2 + (idx w-b)/2
  let f (w : W) : Fin ((t-1)/2 + width/2+1) := ⟨code w, by
    dsimp [code]
    split_ifs with h
    · have := hpos w; have := heven w; omega
    · have := hwin w (by omega); omega⟩
  have inj : Function.Injective f := by
    intro x y h
    have e := congrArg Fin.val h
    change code x = code y at e
    apply hinj
    have := heven x
    have := heven y
    have := hpos x
    have := hpos y
    dsimp [code] at e
    split_ifs at e with hx hy hy <;> first | omega | (have := hwin x (by omega); have := hwin y (by omega); omega)
  simpa using Fintype.card_le_of_injective f inj

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The extension retains its endpoint color and counts the possible obstructions
on the old geodesic both in general and when it first meets the core. -/
theorem geodesic_core_endpoint_with_walk (hc : G.Connected) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) (S : Finset V) {a v : V} (ha : a ∈ S) (q : G.Walk a v)
    (hgeo : q.length = G.dist a v) (h₂ : 2 ≤ q.length) :
    ∃ (u : S) (t : ℕ), (∃ p : G.Walk u.val v, Chordless p ∧ p.length = t+q.length ∧
      (∀ j, p.getVert (t+j) = q.getVert j) ∧ (∀ i < t, p.getVert i ∈ S)) ∧
      q.length + t + 1 ≤ G.path ∧
      (c a).val = ((c u.val).val+t)%2 ∧
      (G.induce (S : Set V)).degree u ≤ (t-1)/2 + 3 ∧
      (G.induce (S : Set V)).degree u ≤ t+1 ∧
      ((∀ w : S, q.length ≤ G.dist w.val v) →
        (G.induce (S : Set V)).degree u ≤ (t-1)/2 + 1) := by
  classical
  have hq : Chordless q := ⟨q.isPath_of_length_eq_dist hgeo,
    fun i j hi hj => (adj_getVert_iff_consecutive_of_length_eq_dist q hgeo hi hj).1⟩
  obtain ⟨u,p,t,hu,hp,hlen,hsuf,hpre,hsat⟩ := exists_saturated_inside (S : Set V) q hq ha
  let H := G.induce (S : Set V)
  let uS : S := ⟨u,hu⟩
  let W := (H.neighborFinset uS).map (Function.Embedding.subtype (· ∈ S))
  have hW (w : W) : G.Adj u w.val ∧ w.val ∈ S := by
    obtain ⟨w',hw',he⟩ := Finset.mem_map.mp w.property
    exact he ▸ ⟨(H.mem_neighborFinset _ _).mp hw', w'.property⟩
  have hcard : W.card = H.degree uS := by simp [W]
  have blocks (w : W) : ∃ i ≤ p.length, i ≠ 0 ∧ G.Adj w.val (p.getVert i) := by
    by_cases h : w.val = p.getVert 1
    · exact ⟨2, by omega, by decide, h ▸ (p.adj_getVert_succ (i := 1) (by omega))⟩
    · exact hsat _ (hW w).2 (hW w).1 (hp.pending_off_path (hW w).1 h)
  choose idx hi using blocks
  have heven (w : W) : idx w % 2 = 0 := by
    have h1 := Fin.val_ne_of_ne (c.valid (hW w).1)
    have h2 := Fin.val_ne_of_ne (c.valid (hi w).2.2)
    have h3 := walk_color c p (idx w) (hi w).1
    have := (c u).isLt
    have := (c w.val).isLt
    have := (c (p.getVert (idx w))).isLt
    omega
  have hinj : Function.Injective idx := by
    intro w z he
    have hne : u ≠ p.getVert (idx w) := by
      intro e
      have eq := hp.simple.getVert_injOn (x₁ := 0) (x₂ := idx w) (Nat.zero_le _) (hi w).1 (by simpa using e)
      exact (hi w).2.1 eq.symm
    exact Subtype.ext (h4 hne (hW w).1 (hi w).2.2.symm (hW z).1 (he ▸ (hi z).2.2.symm))
  have hpos (w : W) : 0 < idx w := Nat.pos_of_ne_zero (hi w).2.1
  have anchor : p.getVert t = a := by simpa using hsuf 0
  have hra : G.dist u a ≤ t := by
    have h := dist_le (p.take t)
    simpa only [Walk.take_length, Nat.min_eq_left (show t ≤ p.length by omega), anchor] using h
  have twoSteps (w : W) : G.dist u (p.getVert (idx w)) ≤ 2 :=
    (hc.dist_triangle (u := u) (v := w.val) (w := p.getVert (idx w))).trans_eq (by
      rw [dist_eq_one_iff_adj.mpr (hW w).1, dist_eq_one_iff_adj.mpr (hi w).2.2])
  have before_after (w : W) (hw : t ≤ idx w) :
      G.dist a (p.getVert (idx w)) = idx w-t ∧
      G.dist (p.getVert (idx w)) v = p.length-idx w := by
    let j := idx w-t
    have hj : j ≤ q.length := by have := (hi w).1; dsimp [j]; omega
    have eq : p.getVert (idx w) = q.getVert j := Nat.add_sub_of_le hw ▸ hsuf j
    rw [eq]
    constructor
    · simpa [j] using dist_getVert_eq_sub_of_le_of_length_eq_dist q hgeo (Nat.zero_le j) hj
    · have e := dist_getVert_eq_sub_of_le_of_length_eq_dist q hgeo hj le_rfl
      simpa only [Walk.getVert_length, j, hlen, Nat.sub_sub_self (Nat.zero_le _),
        show q.length - (idx w - t) = t + q.length - idx w by omega] using e
  let b := p.length - (G.dist u v + 2)
  have win (w : W) (hw : t ≤ idx w) : b ≤ idx w ∧ idx w ≤ b+4 := by
    have h1 := hc.dist_triangle (u := u) (v := p.getVert (idx w)) (w := v)
    have h2 := hc.dist_triangle (u := p.getVert (idx w)) (v := u) (w := v)
    rw [G.dist_comm (u := p.getVert (idx w)) (v := u)] at h2
    have h := (before_after w hw).2
    have := twoSteps w
    have := (hi w).1
    dsimp [b]
    omega
  have global (w : W) : idx w ≤ 2*t+2 := by
    by_cases hw : t ≤ idx w
    · have h := hc.dist_triangle (u := a) (v := u) (w := p.getVert (idx w))
      rw [G.dist_comm (u := a) (v := u)] at h
      have := (before_after w hw).1
      have := twoSteps w
      omega
    · omega
  -- Use all even positions up to 2t+2; the last slot of a suffix is unnecessary here.
  let f (w : W) : Fin (t+1) := ⟨idx w/2-1, by have := global w; have := hpos w; have := heven w; omega⟩
  have hinj' : Function.Injective f := by
    intro w z he
    apply hinj
    have h := congrArg Fin.val he
    change idx w/2-1 = idx z/2-1 at h
    have := hpos w; have := hpos z; have := heven w; have := heven z
    omega
  have short : W.card ≤ t+1 := by simpa using Fintype.card_le_of_injective f hinj'
  have hl := G.length_le_path_of_isInducedPath _ (isInducedPath_support_of_isPath_of_adj_getVert p
    hp.simple hp.consecutive)
  rw [Walk.length_support, hlen, Nat.add_comm t q.length] at hl
  refine ⟨uS,t,⟨p,hp,hlen,hsuf,hpre⟩,hl,?_,?_,hcard ▸ short,?_⟩
  · simpa only [anchor] using walk_color c p t (by omega)
  · exact hcard ▸ count_even_sites idx hinj hpos heven t b 4 win
  · intro hclosest
    have narrow (w : W) (hw : t ≤ idx w) : t ≤ idx w ∧ idx w ≤ t+1 := by
      have e := hclosest ⟨w.val,(hW w).2⟩
      change q.length ≤ G.dist w.val v at e
      have ht := hc.dist_triangle (u := w.val) (v := p.getVert (idx w)) (w := v)
      rw [dist_eq_one_iff_adj.mpr (hi w).2.2, (before_after w hw).2] at ht
      have := (hi w).1
      omega
    exact hcard ▸ count_even_sites idx hinj hpos heven t t 1 narrow

private theorem geodesic_core_endpoint (hc : G.Connected) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) (S : Finset V) {a v : V} (ha : a ∈ S) (q : G.Walk a v)
    (hgeo : q.length = G.dist a v) (h₂ : 2 ≤ q.length) :
    ∃ (u : S) (t : ℕ), q.length + t + 1 ≤ G.path ∧
      (c a).val = ((c u.val).val+t)%2 ∧
      (G.induce (S : Set V)).degree u ≤ (t-1)/2 + 3 ∧
      (G.induce (S : Set V)).degree u ≤ t+1 ∧
      ((∀ w : S, q.length ≤ G.dist w.val v) →
        (G.induce (S : Set V)).degree u ≤ (t-1)/2 + 1) := by
  obtain ⟨u,t,_,h⟩ := geodesic_core_endpoint_with_walk hc c h4 S ha q hgeo h₂
  exact ⟨u,t,h⟩

/-- A vertex at distance at least two from a dense induced subgraph forces an
induced path with two additional vertices per unit of minimum internal degree. -/
theorem distance_add_twice_degree_le_path_of_nearest (hc : G.Connected)
    (hb : G.IsBipartite) (h4 : NoFourCycle G) (S : Finset V) {a v : V}
    (ha : a ∈ S) (hnearest : ∀ w : S, G.dist a v ≤ G.dist w.val v)
    (hfar : 2 ≤ G.dist a v) {d : ℕ} (hd : 2 ≤ d)
    (hmin : ∀ u : S, d ≤ (G.induce (S : Set V)).degree u) :
    G.dist a v + 2*d ≤ G.path := by
  obtain ⟨c⟩ := hb
  obtain ⟨q,_,hq⟩ := hc.exists_path_of_dist a v
  obtain ⟨u,t,hp,_,_,hsmall,hn⟩ := geodesic_core_endpoint hc c h4 S ha q hq (hq ▸ hfar)
  have := hn (hq ▸ hnearest)
  have := hmin u
  omega

/-- Starting from any vertex of a minimum-degree subgraph incurs at most
two more unavailable attachment sites than starting at the nearest vertex. -/
theorem distance_add_twice_degree_le_path_add_four (hc : G.Connected)
    (hb : G.IsBipartite) (h4 : NoFourCycle G) (S : Finset V) {a v : V}
    (ha : a ∈ S) (hfar : 2 ≤ G.dist a v) {d : ℕ}
    (hmin : ∀ u : S, d ≤ (G.induce (S : Set V)).degree u) :
    G.dist a v + 2*d ≤ G.path+4 := by
  obtain ⟨c⟩ := hb
  obtain ⟨q,_,hq⟩ := hc.exists_path_of_dist a v
  obtain ⟨u,t,hp,_,hdeg,hsmall,_⟩ := geodesic_core_endpoint hc c h4 S ha q hq (hq ▸ hfar)
  have := hmin u
  omega

omit [Fintype V] [DecidableEq V] in
/-- The lower-degree color class contains an anchor from which saturation
forces at least `2*m-2` additional vertices. -/
theorem exists_odd_growth_anchor (c : G.Coloring (Fin 2)) (S : Finset V)
    (hS : S.Nonempty) (col : Fin 2) {m : ℕ}
    (hmin : ∀ u : S, m+1+(if c u.val = col then 1 else 0) ≤ (G.induce (S : Set V)).degree u) :
    ∃ a : S, ∀ (u : S) (t : ℕ), (c a.val).val = ((c u.val).val+t)%2 →
      (G.induce (S : Set V)).degree u ≤ (t-1)/2+3 →
      (2 ≤ t ∨ (G.induce (S : Set V)).degree u ≤ t+1) → 2*m+1 ≤ t+3 := by
  classical
  let H := G.induce (S : Set V)
  obtain ⟨b,hb'⟩ := hS
  let b' : S := ⟨b,hb'⟩
  have hlow : ∃ a : S, c a.val ≠ col := by
    by_cases hbcol : c b'.val = col
    · have hpos : 0 < H.degree b' := by
        have h := hmin b'
        change _ ≤ H.degree b' at h
        omega
      obtain ⟨a,ha⟩ := (H.degree_pos_iff_exists_adj b').mp hpos
      exact ⟨a,fun heq => c.valid (show G.Adj b'.val a.val from ha) (hbcol.trans heq.symm)⟩
    · exact ⟨b',hbcol⟩
  obtain ⟨a,ha⟩ := hlow
  refine ⟨a, ?_⟩
  intro u t hcolor hbound hsmall
  have hh := hmin u
  by_cases hu : c u.val = col
  · simp only [ite_eq_left hu] at hh
    omega
  · simp only [ite_eq_right hu] at hh
    have hsame : c a.val = c u.val := by
      apply Fin.ext
      have e₁ := Fin.val_ne_of_ne ha
      have e₂ := Fin.val_ne_of_ne hu
      have := (c a.val).isLt
      have := (c u.val).isLt
      have := col.isLt
      omega
    rw [hsame] at hcolor
    have := (c u.val).isLt
    omega


/-- With one extra neighbor on a color class, starting the geodesic in the
opposite class gains one vertex at an odd density threshold. -/
theorem radius_add_odd_threshold_le_path_add_two_of_core (hc : G.Connected)
    (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G) (S : Finset V) (hS : S.Nonempty)
    (col : Fin 2) {m : ℕ}
    (hmin : ∀ u : S, m+1+(if c u.val = col then 1 else 0) ≤ (G.induce (S : Set V)).degree u)
    (hr : 2 ≤ G.radius.toNat) : G.radius.toNat+(2*m+1) ≤ G.path+2 := by
  obtain ⟨a,hcost⟩ := exists_odd_growth_anchor c S hS col hmin
  obtain ⟨v,q,hq,hrq⟩ := exists_geodesic_ge_radius G hc a.val
  obtain ⟨u,t,hp,hcolor,hbound,hsmall,_⟩ :=
    geodesic_core_endpoint hc c h4 S a.property q hq (by omega)
  have := hcost u t hcolor hbound (Or.inr hsmall)
  omega

variable [Nonempty V]

/-- Without regularity or a bound on radius, the conjectured bipartite
inequality holds with an additive error of at most two vertices. -/
theorem radius_add_floor_le_path_add_two_of_bipartite [Nontrivial V]
    (hc : G.Connected) (hb : G.IsBipartite) (h4 : NoFourCycle G) :
    G.radius.toNat + ⌊l G⌋₊ ≤ G.path+2 := by
  classical
  let k := ⌊l G⌋₊
  change G.radius.toNat+k ≤ _
  by_cases hr : G.radius.toNat ≤ 4
  · have := radius_add_floor_le_path_of_bipartite_radius_le_four hc hb h4 hr
    omega
  by_cases hk : k ≤ 4
  · have := chung_bound_nat G hc
    omega
  have hav : (k : ℝ) ≤ l G := Nat.floor_le (div_nonneg
    (Finset.sum_nonneg (fun v _ => Nat.cast_nonneg (G.indepNeighborsCard v))) (Nat.cast_nonneg _))
  have hdeg := sum_degree_ge_of_le_l hav
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · obtain ⟨S,hS,hmin⟩ := exists_degree_core G (by omega : 0 < k) hdeg
    obtain ⟨a,ha⟩ := hS
    obtain ⟨v,q,hq,hrq⟩ := exists_geodesic_ge_radius G hc a
    have := distance_add_twice_degree_le_path_add_four hc hb h4 S ha
      (by omega : 2 ≤ G.dist a v) hmin
    omega
  · obtain ⟨c⟩ := hb
    let m := k/2
    have he : 2*m+1 = k := by dsimp [m]; omega
    obtain ⟨col,S,hS,hmin⟩ := exists_odd_degree_core c (show 0 < m by omega) (he ▸ hdeg)
    have hodd := radius_add_odd_threshold_le_path_add_two_of_core hc c h4 S hS col hmin (by omega)
    omega

/-- The exact conjecture holds when a dense induced subgraph lies within
distance `s` of every vertex and the radius is at least
`4*s + 5 + 3*(⌊l G⌋₊ % 2)`. The subgraph may be disconnected. -/
theorem radius_add_floor_le_path_of_core_cover (hc : G.Connected) (hb : G.IsBipartite)
    (h4 : NoFourCycle G) (S : Finset V) (hS : S.Nonempty)
    (hmin : ∀ u : S, ⌊l G⌋₊/2+1 ≤ (G.induce (S : Set V)).degree u) {s : ℕ}
    (hcover : ∀ v : V, ∃ u ∈ S, G.dist v u ≤ s)
    (hr : 4*s+5+3*(⌊l G⌋₊%2) ≤ G.radius.toNat) : G.radius.toNat+⌊l G⌋₊ ≤ G.path := by
  let k := ⌊l G⌋₊
  change G.radius.toNat+k ≤ _
  change 4*s+5+3*(k%2) ≤ G.radius.toNat at hr
  by_cases hk : k < G.radius.toNat
  · have := chung_bound_nat G hc
    omega
  obtain ⟨a,ha⟩ := hS
  obtain ⟨v,q,hq,hrq⟩ := exists_geodesic_ge_radius G hc a
  obtain ⟨b,hb',hnear⟩ := hcover v
  have ht := hc.dist_triangle (u := a) (v := b) (w := v)
  rw [G.dist_comm (u := b) (v := v)] at ht
  have hp := distance_add_twice_core_degree_add_tail_le_path_add_four hc hb h4 S ha hb'
    (d := k/2+1) (by omega) hmin (by omega) (b := s+2+k%2) (by omega) (by omega)
  omega

/-- In a counterexample every dense induced subgraph must be close to every
vertex, and each of its vertices has bounded eccentricity. Both distances
here are measured in the original graph. -/
theorem distances_to_core_of_bipartite_counterexample (hc : G.Connected)
    (hb : G.IsBipartite) (h4 : NoFourCycle G) (hr : 5 ≤ G.radius.toNat)
    (hbad : G.path < G.radius.toNat + ⌊l G⌋₊) (S : Finset V) (hS : S.Nonempty)
    (hmin : ∀ u : S, ⌊l G⌋₊/2+1 ≤ (G.induce (S : Set V)).degree u) (v : V) :
    (∃ a ∈ S, G.dist a v+3 ≤ G.radius.toNat + ⌊l G⌋₊%2) ∧
    (∀ a ∈ S, G.dist a v ≤ G.radius.toNat+1+⌊l G⌋₊%2) := by
  have hk := chung_bound_nat G hc
  obtain ⟨a,ha,hm⟩ := S.exists_min_image (fun w => G.dist w v) hS
  constructor
  · refine ⟨a,ha,?_⟩
    by_cases hf : 2 ≤ G.dist a v
    · have := distance_add_twice_degree_le_path_of_nearest hc hb h4 S ha
        (fun w => hm w.val w.property) hf (by omega) hmin
      omega
    · omega
  · intro a ha
    by_cases hf : 2 ≤ G.dist a v
    · have := distance_add_twice_degree_le_path_add_four hc hb h4 S ha hf hmin
      omega
    · omega

end Wall133
