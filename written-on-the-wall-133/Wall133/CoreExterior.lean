import Wall133.BipartiteGeodesic

/-!
# Growing the end away from a dense subgraph

A far endpoint of a geodesic can be extended after its other end has already
grown an induced tail inside a dense subgraph. The new vertices only need to
avoid the first few vertices of the geodesic while the subgraph is far away.
-/
namespace Wall133
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

def chainOfChordless {u v : V} (p : G.Walk u v) (h : Chordless p) : Chain G p.length where
  vertex := p.getVert
  inj hi hj e := h.simple.getVert_injOn hi hj e
  edges := by
    intro i j hi hj
    refine ⟨h.consecutive i j hi hj, ?_⟩
    rintro (eq | eq)
    · rw [← eq]
      exact p.adj_getVert_succ (by omega)
    · rw [← eq]
      exact (p.adj_getVert_succ (by omega)).symm

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertices allowed at successive stages of an extension. There need to
be more choices for the next vertex than the number of blocking sites. -/
structure ExteriorChoices (G : SimpleGraph V) (v : V) (b : ℕ) where
  allowed : ℕ → Set V
  start : v ∈ allowed 0
  choices : ∀ j < b, ∀ x ∈ allowed j, G.dist v x ≤ j →
    ∃ N : Finset V, j+1 < N.card ∧ ∀ z ∈ N, G.Adj x z ∧ z ∈ allowed (j+1)

def ExteriorChoices.ofDegree {v : V} {b : ℕ}
    (hdegree : ∀ x, G.dist v x < b → b+1 ≤ G.degree x) : ExteriorChoices G v b where
  allowed _ := Set.univ
  start := Set.mem_univ _
  choices j hj x _ hd := by
    refine ⟨G.neighborFinset x, ?_, fun z hz => ⟨(G.mem_neighborFinset _ _).mp hz, Set.mem_univ _⟩⟩
    rw [G.card_neighborFinset_eq_degree]
    have := hdegree x (by omega)
    omega

omit [DecidableRel G.Adj] in
private theorem exterior_growth (hc : G.Connected) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) (S : Finset V) {a v u : V} (q : G.Walk a v)
    (hq : q.length = G.dist a v) (h₂ : 2 ≤ q.length)
    (p : G.Walk u v) (hp : Chordless p) {t : ℕ} (hlen : p.length = t+q.length)
    (hsuf : ∀ j, p.getVert (t+j) = q.getVert j) (hpre : ∀ i < t, p.getVert i ∈ S)
    {b : ℕ} (hfar : ∀ z ∈ S, b+2 ≤ G.dist v z)
    (E : ExteriorChoices G v b) : p.length+b+1 ≤ G.path := by
  let R := (chainOfChordless p hp).reverse
  have hvertex (i : ℕ) : R.vertex i = p.getVert (p.length-i) := rfl
  have hfirst : R.vertex 0 = v := by simp [hvertex]
  have hgeo (i : ℕ) (hi : i ≤ q.length) : G.dist v (R.vertex i) = i := by
    rw [hvertex, show p.length-i = t+(q.length-i) by omega, hsuf, G.dist_comm]
    have he := dist_getVert_eq_sub_of_le_of_length_eq_dist q hq
      (i := q.length-i) (j := q.length) (Nat.sub_le _ _) le_rfl
    rw [Walk.getVert_length] at he
    omega
  have htail (i : ℕ) (hi : q.length < i) (hn : i ≤ p.length) : R.vertex i ∈ S := by
    rw [hvertex]
    exact hpre _ (by omega)
  have build (j : ℕ) (hj : j ≤ b) :
      ∃ P : Chain G (p.length+j), P.vertex 0 ∈ E.allowed j ∧
        ∀ i ≤ p.length, P.vertex (j+i) = R.vertex i := by
    induction j with
    | zero => exact ⟨R, by simpa only [hfirst] using E.start, fun i _ => by rw [Nat.zero_add]⟩
    | succ j ih =>
      obtain ⟨P, hPS, hP⟩ := ih (by omega)
      have hbase : P.vertex j = v := by simpa [hfirst] using hP 0 (Nat.zero_le _)
      have hd := P.dist_le_sub hc (i := 0) (j := j) (Nat.zero_le _) (by omega)
      rw [Nat.sub_zero, hbase, G.dist_comm] at hd
      have key (i : ℕ) (h : P.Blocks i) : i ≤ 2*j+2 := by
        obtain ⟨hn, -, -, hdist⟩ := h
        by_cases hij : j ≤ i
        · have hei : P.vertex i = R.vertex (i-j) := by
            simpa only [Nat.add_sub_of_le hij] using hP (i-j) (by omega)
          have ht := hc.dist_triangle (u := v) (v := P.vertex 0) (w := P.vertex i)
          by_cases hi : i-j ≤ q.length
          · have he := hgeo _ hi
            rw [← hei] at he
            omega
          · have hz := hfar _ (htail (i-j) (by omega) (by omega))
            rw [← hei] at hz
            omega
        · omega
      let code (i : ℕ) := i/2-1
      have bound (i : ℕ) (h : P.Blocks i) : code i < j+1 := by
        have := key i h
        dsimp [code]
        omega
      have inj (i k : ℕ) (hi : P.Blocks i) (hk : P.Blocks k) (he : code i = code k) :
          i = k := by
        have hp₁ := hi.2.1
        have hp₂ := hk.2.1
        have he₁ := hi.2.2.1
        have he₂ := hk.2.2.1
        dsimp [code] at he
        omega
      obtain ⟨N,hcard,hN⟩ := E.choices j (by omega) (P.vertex 0) hPS hd
      obtain ⟨Q, hQS, hQ⟩ := P.extendByCode hc c h4 (by omega) (E.allowed (j+1))
        N hcard hN code bound inj
      exact ⟨Q, hQS, fun i hi => by
        simpa only [Nat.succ_add] using (hQ (j+i)).trans (hP i hi)⟩
  obtain ⟨P, _⟩ := build b le_rfl
  exact P.length_le

/-- A density core has an anchor whose saturated extensions always use at
least `k-3` vertices. The color of the anchor matters in the odd case. -/
theorem exists_growth_anchor [Nonempty V] (c : G.Coloring (Fin 2)) {k : ℕ}
    (hk : 7 ≤ k) (hdeg : k * Fintype.card V ≤ ∑ v, G.degree v) :
    ∃ (S : Finset V) (a : S), (∀ u : S, k/2+1 ≤ (G.induce (S : Set V)).degree u) ∧
      ∀ (u : S) (t : ℕ), (c a.val).val = ((c u.val).val+t)%2 →
        (G.induce (S : Set V)).degree u ≤ (t-1)/2+3 → k ≤ t+3 := by
  rcases Nat.mod_two_eq_zero_or_one k with he | ho
  · obtain ⟨S, ⟨a, ha⟩, hm⟩ := exists_degree_core G (by omega : 0 < k) hdeg
    refine ⟨S, ⟨a, ha⟩, hm, ?_⟩
    intro u t _ ht
    have := hm u
    omega
  · let m := k/2
    have he : 2*m+1 = k := by dsimp [m]; omega
    obtain ⟨col, S, hS, hm⟩ := exists_odd_degree_core c (by dsimp [m]; omega : 0 < m)
      (he ▸ hdeg)
    obtain ⟨a, hanchor⟩ := exists_odd_growth_anchor c S hS col hm
    refine ⟨S, a, fun v => (Nat.le_add_right _ _).trans (hm v), ?_⟩
    intro u t hcol hb
    rw [← he]
    apply hanchor u t hcol hb
    left
    have := hm u
    omega

theorem exterior_estimate_of_anchor (hc : G.Connected) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) (S : Finset V) (a : S) {k b : ℕ}
    (hd : ∀ u : S, k/2+1 ≤ (G.induce (S : Set V)).degree u)
    (hcost : ∀ (u : S) (t : ℕ), (c a.val).val = ((c u.val).val+t)%2 →
      (G.induce (S : Set V)).degree u ≤ (t-1)/2+3 → k ≤ t+3)
    (v : V) (hrad : G.radius.toNat ≤ G.dist a.val v) (E : ExteriorChoices G v b)
    (hk : G.radius.toNat ≤ k) (hbpos : 1 ≤ b) (hbsmall : b ≤ 2)
    (hr : 7*b+3+3*(k%2) ≤ G.radius.toNat) :
    G.radius.toNat + k + b ≤ G.path+2 := by
  obtain ⟨q, _, hq⟩ := hc.exists_path_of_dist a.val v
  by_cases hf : ∀ z ∈ S, b+2 ≤ G.dist v z
  · obtain ⟨u,t,⟨p,hp,hlen,hsuf,hpre⟩,_,hcol,hbound,_,_⟩ :=
      geodesic_core_endpoint_with_walk hc c h4 S a.property q hq (by omega)
    have hl := exterior_growth hc c h4 S q hq (by omega) p hp hlen hsuf hpre hf E
    have := hcost u t hcol hbound
    omega
  · push Not at hf
    obtain ⟨w,hw,hwv⟩ := hf
    have ht := hc.dist_triangle (u := a.val) (v := w) (w := v)
    rw [G.dist_comm (u := w) (v := v)] at ht
    have hl := distance_add_twice_core_degree_add_tail_le_path_add_four hc ⟨c⟩ h4 S a.property hw
      (d := k/2+1) (by omega) hd (by omega) (b := 2*b+1+k%2) (by omega) (by omega)
    omega

/-- At sufficiently large radius, a lower bound on the degrees near a far
endpoint allows extra vertices beyond the unrestricted two-vertex estimate. -/
theorem radius_add_floor_add_exterior_le_path_add_two_of_far_vertices [Nonempty V]
    (hc : G.Connected) (hb : G.IsBipartite) (h4 : NoFourCycle G)
    {b : ℕ} (hbpos : 1 ≤ b) (hbsmall : b ≤ 2)
    (hfar : ∀ a, ∃ v, G.radius.toNat ≤ G.dist a v ∧
      ∀ x, G.dist v x < b → b+1 ≤ G.degree x)
    (hr : 7*b+3+3*(⌊l G⌋₊%2) ≤ G.radius.toNat) :
    G.radius.toNat + ⌊l G⌋₊ + b ≤ G.path+2 := by
  let k := ⌊l G⌋₊
  change G.radius.toNat + k + b ≤ _
  change 7*b+3+3*(k%2) ≤ G.radius.toNat at hr
  by_cases hlarge : k < G.radius.toNat
  · have := chung_bound_nat G hc
    omega
  have hav : (k : ℝ) ≤ l G := Nat.floor_le (div_nonneg
    (Finset.sum_nonneg (fun v _ => Nat.cast_nonneg (G.indepNeighborsCard v))) (Nat.cast_nonneg _))
  obtain ⟨c⟩ := hb
  obtain ⟨S, a, hd, hcost⟩ := exists_growth_anchor c (by omega : 7 ≤ k) (sum_degree_ge_of_le_l hav)
  obtain ⟨v, hrad, hdegree⟩ := hfar a.val
  exact exterior_estimate_of_anchor hc c h4 S a hd hcost v hrad
    (ExteriorChoices.ofDegree hdegree) (by omega) hbpos hbsmall hr

/-- A global minimum degree provides a suitable far endpoint for every anchor. -/
theorem radius_add_floor_add_exterior_le_path_add_two [Nonempty V]
    (hc : G.Connected) (hb : G.IsBipartite) (h4 : NoFourCycle G)
    {b : ℕ} (hbpos : 1 ≤ b) (hbsmall : b ≤ 2)
    (hdegree : ∀ v, b+1 ≤ G.degree v)
    (hr : 7*b+3+3*(⌊l G⌋₊%2) ≤ G.radius.toNat) :
    G.radius.toNat + ⌊l G⌋₊ + b ≤ G.path+2 := by
  apply radius_add_floor_add_exterior_le_path_add_two_of_far_vertices hc hb h4 hbpos hbsmall _ hr
  intro a
  obtain ⟨v,q,hq,hrq⟩ := exists_geodesic_ge_radius G hc a
  exact ⟨v, by omega, fun x _ => hdegree x⟩

def ExteriorChoices.withException {v e : V} (hv : v ≠ e)
    (hdegree : ∀ x, x ≠ e → 3 ≤ G.degree x) : ExteriorChoices G v 2 where
  allowed j := {x | x ≠ e ∨ j = 2}
  start := Or.inl hv
  choices j hj x hx _ := by
    change x ≠ e ∨ j = 2 at hx
    have hd := hdegree x (hx.resolve_right (by omega))
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · refine ⟨(G.neighborFinset x).erase e, ?_, ?_⟩
      · have he := Finset.pred_card_le_card_erase (s := G.neighborFinset x) (a := e)
        rw [G.card_neighborFinset_eq_degree] at he
        omega
      · intro z hz
        obtain ⟨hne,hz'⟩ := Finset.mem_erase.mp hz
        exact ⟨(G.mem_neighborFinset _ _).mp hz', Or.inl hne⟩
    · exact ⟨G.neighborFinset x, hd, fun z hz => ⟨(G.mem_neighborFinset _ _).mp hz, Or.inr rfl⟩⟩

/-- In a hypothetical counterexample, one can prescribe a vertex near which
to select a core anchor, preserving the anchor's required color. -/
theorem exists_nearby_anchor [Nonempty V] (hc : G.Connected) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) (S : Finset V) (a : S) (e : V) (hr : 5 ≤ G.radius.toNat)
    (hbad : G.path < G.radius.toNat + ⌊l G⌋₊)
    (hmin : ∀ u : S, ⌊l G⌋₊/2+1 ≤ (G.induce (S : Set V)).degree u) :
    ∃ a' : S, c a'.val = c a.val ∧ G.dist a'.val e < G.radius.toNat := by
  obtain ⟨x, hx, he⟩ := (distances_to_core_of_bipartite_counterexample hc ⟨c⟩ h4 hr hbad S
    ⟨a.val,a.property⟩ hmin e).1
  let x' : S := ⟨x,hx⟩
  by_cases hcol : c x = c a.val
  · exact ⟨x',hcol,by dsimp [x']; omega⟩
  · let H := G.induce (S : Set V)
    have hn : 0 < H.degree x' := lt_of_lt_of_le (Nat.zero_lt_succ _) (hmin x')
    obtain ⟨y, hy⟩ := (H.degree_pos_iff_exists_adj x').mp hn
    have hadj : G.Adj x y.val := hy
    refine ⟨y, ?_, ?_⟩
    · apply Fin.ext
      have := Fin.val_ne_of_ne (c.valid hadj)
      have := Fin.val_ne_of_ne hcol
      have := (c x).isLt
      have := (c y.val).isLt
      have := (c a.val).isLt
      omega
    · have htri := hc.dist_triangle (u := y.val) (v := x) (w := e)
      rw [dist_eq_one_iff_adj.mpr hadj.symm] at htri
      omega

/-- One arbitrary vertex can have degree below three. Every other vertex
supplies enough neighbors for the exterior extension. -/
theorem radius_add_floor_le_path_of_one_degree_exception [Nonempty V]
    (hc : G.Connected) (hb : G.IsBipartite) (h4 : NoFourCycle G) (e : V)
    (hdegree : ∀ v, v ≠ e → 3 ≤ G.degree v)
    (hr : 17+3*(⌊l G⌋₊%2) ≤ G.radius.toNat) :
    G.radius.toNat + ⌊l G⌋₊ ≤ G.path := by
  classical
  by_contra! hbad
  let k := ⌊l G⌋₊
  change G.path < G.radius.toNat+k at hbad
  change 17+3*(k%2) ≤ G.radius.toNat at hr
  have hk : G.radius.toNat ≤ k := by have := chung_bound_nat G hc; omega
  have hav : (k : ℝ) ≤ l G := Nat.floor_le (div_nonneg
    (Finset.sum_nonneg (fun v _ => Nat.cast_nonneg (G.indepNeighborsCard v))) (Nat.cast_nonneg _))
  obtain ⟨c⟩ := hb
  obtain ⟨S,a,hd,hcost⟩ := exists_growth_anchor c (by omega : 7 ≤ k) (sum_degree_ge_of_le_l hav)
  obtain ⟨a',hcol,hclose⟩ := exists_nearby_anchor hc c h4 S a e (by omega) hbad hd
  obtain ⟨v,p,hp,hrad⟩ := exists_geodesic_ge_radius G hc a'.val
  have hfar : G.radius.toNat ≤ G.dist a'.val v := by omega
  have hv : v ≠ e := fun he => by rw [he] at hfar; omega
  have hext := exterior_estimate_of_anchor hc c h4 S a' hd (by simpa only [hcol] using hcost)
    v (by omega) (ExteriorChoices.withException hv hdegree) hk (by decide) (by decide) (by omega)
  omega

/-- For minimum degree at least two and radius at least thirteen, at most
one vertex separates the longest induced path from the conjectured bound. -/
theorem radius_add_floor_le_path_add_one_of_no_leaves [Nonempty V]
    (hc : G.Connected) (hb : G.IsBipartite) (h4 : NoFourCycle G)
    (hdegree : ∀ v, 2 ≤ G.degree v) (hr : 13 ≤ G.radius.toNat) :
    G.radius.toNat + ⌊l G⌋₊ ≤ G.path+1 := by
  have := radius_add_floor_add_exterior_le_path_add_two hc hb h4 (b := 1)
    (by decide) (by decide) hdegree (by omega)
  omega

/-- WOWII 133 for every four-cycle-free bipartite graph of radius at least
twenty and minimum degree at least three, with arbitrary upper degrees. -/
theorem radius_add_floor_le_path_of_min_degree_three_large_radius [Nonempty V]
    (hc : G.Connected) (hb : G.IsBipartite) (h4 : NoFourCycle G)
    (hdegree : ∀ v, 3 ≤ G.degree v) (hr : 20 ≤ G.radius.toNat) :
    G.radius.toNat + ⌊l G⌋₊ ≤ G.path := by
  have := radius_add_floor_add_exterior_le_path_add_two hc hb h4 (b := 2)
    (by decide) (by decide) hdegree (by omega)
  omega

end Wall133
