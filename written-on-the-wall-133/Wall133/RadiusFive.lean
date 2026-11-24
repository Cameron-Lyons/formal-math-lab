import Wall133.BipartiteDensity

namespace Wall133
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

def Good (P : Chain G n) (z : V) : Prop :=
  G.Adj (P.vertex 0) z ∧
  (∀ i ≤ n, z ≠ P.vertex i) ∧ (∀ i ≤ n, i ≠ 0 → ¬G.Adj z (P.vertex i))

def grow (P : Chain G n) (z : V) (h : Good P z) : Chain G (n+1) :=
  P.prepend z h.1.symm h.2.1 h.2.2

private theorem site_of_contact (P : Chain G n) (c : G.Coloring (Fin 2))
    {i : ℕ} (hi : i ≤ n) (hp : i ≠ 0) {z : V} (hz : G.Adj (P.vertex 0) z)
    (ha : G.Adj (P.vertex i) z) : ∃ j : Fin (n/2), i = 2*j.val+2 := by
  have := P.even_of_common c hi hz ha
  exact ⟨⟨i/2-1, by omega⟩, by simp; omega⟩

theorem blocker (P : Chain G n) (c : G.Coloring (Fin 2)) (hn : 2 ≤ n)
    {z : V} (hz : G.Adj (P.vertex 0) z) (h : ¬ Good P z) :
    ∃ j : Fin (n/2), G.Adj (P.vertex (2*j.val+2)) z := by
  by_cases hc : ∃ i ≤ n, i ≠ 0 ∧ G.Adj (P.vertex i) z
  · obtain ⟨i, hi, hp, ha⟩ := hc
    obtain ⟨j, hj⟩ := site_of_contact P c hi hp hz ha
    exact ⟨j, hj ▸ ha⟩
  have clean : ∀ i ≤ n, i ≠ 0 → ¬G.Adj z (P.vertex i) :=
    fun i hi hpos ha => hc ⟨i, hi, hpos, ha.symm⟩
  have rep : ∃ i ≤ n, z = P.vertex i := by
    by_contra! hfresh
    exact h ⟨hz, hfresh, clean⟩
  obtain ⟨i, hi, rfl⟩ := rep
  have := (P.edges (Nat.zero_le _) hi).1 hz
  have : i = 1 := by omega
  subst i
  exact ⟨⟨0, by omega⟩, (P.edges (i := 2) (j := 1) hn hi).2 (by decide)⟩

theorem unique_at_site (P : Chain G n) (h4 : NoFourCycle G)
    (j : Fin (n/2)) {x y : V}
    (hx : G.Adj (P.vertex 0) x) (hx' : G.Adj (P.vertex (2*j.val+2)) x)
    (hy : G.Adj (P.vertex 0) y) (hy' : G.Adj (P.vertex (2*j.val+2)) y) : x = y := by
  have hj := j.isLt
  apply h4 _ hx hx' hy hy'
  intro he
  have := P.inj (Nat.zero_le _) (show 2*j.val+2 ≤ n by omega) he
  omega

variable [Fintype V] [DecidableRel G.Adj]

open scoped Classical in
theorem good_card (P : Chain G n) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    (hn : 2 ≤ n) :
    G.degree (P.vertex 0) ≤ ((G.neighborFinset (P.vertex 0)).filter (Good P)).card + n/2 := by
  classical
  let N := G.neighborFinset (P.vertex 0)
  let B := N.filter fun z => ¬Good P z
  have ha (z : B) : G.Adj (P.vertex 0) z :=
    (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp z.property).1
  choose f hf using fun z : B => blocker P c hn (ha z) (Finset.mem_filter.mp z.property).2
  have inj : Function.Injective f := by
    intro x y he
    exact Subtype.ext (unique_at_site P h4 (f x) (ha x) (hf x) (ha y) (he ▸ hf y))
  have card := Fintype.card_le_of_injective f inj
  simp only [Fintype.card_coe, Fintype.card_fin] at card
  have hsum := Finset.card_filter_add_card_filter_not (s := N) (Good P)
  change (N.filter (Good P)).card + B.card = G.degree (P.vertex 0) at hsum
  change G.degree (P.vertex 0) ≤ (N.filter (Good P)).card+n/2
  omega

private theorem one_good (P : Chain G n) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    (hn : 2 ≤ n) (hd : n/2 < G.degree (P.vertex 0)) : ∃ x, Good P x := by
  classical
  have h := good_card P c h4 hn
  let N := (G.neighborFinset (P.vertex 0)).filter (Good P)
  change G.degree (P.vertex 0) ≤ N.card+n/2 at h
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < N.card by omega)
  exact ⟨x, (Finset.mem_filter.mp hx).2⟩

theorem two_good (P : Chain G n) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    (hn : 2 ≤ n) (hd : n/2+2 ≤ G.degree (P.vertex 0)) :
    ∃ x y, Good P x ∧ Good P y ∧ x ≠ y := by
  classical
  let N := G.neighborFinset (P.vertex 0)
  have h := good_card P c h4 hn
  change G.degree (P.vertex 0) ≤ (N.filter (Good P)).card+n/2 at h
  obtain ⟨x, y, hx, hy, hxy⟩ := Finset.one_lt_card_iff.mp
    (show 1 < (N.filter (Good P)).card by omega)
  exact ⟨x, y, (Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2, hxy⟩

/-- When an endpoint of degree at least half the path length cannot be extended,
each positive even path index has its own neighbor, touching no other such index. -/
theorem saturated_witness (P : Chain G n) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    (hn : 2 ≤ n) (hd : n/2 ≤ G.degree (P.vertex 0)) (sat : ∀ z, ¬Good P z)
    (j : Fin (n/2)) :
    ∃ z, G.Adj (P.vertex 0) z ∧ G.Adj (P.vertex (2*j.val+2)) z ∧
      ∀ i ≤ n, i ≠ 0 → G.Adj (P.vertex i) z → i = 2*j.val+2 := by
  classical
  let N := G.neighborFinset (P.vertex 0)
  have ha (z : N) : G.Adj (P.vertex 0) z := (G.mem_neighborFinset _ _).mp z.property
  choose f hf using fun z : N => blocker P c hn (ha z) (sat z)
  have inj : Function.Injective f := by
    intro x y he
    exact Subtype.ext (unique_at_site P h4 (f x) (ha x) (hf x) (ha y) (he ▸ hf y))
  have surj : Function.Surjective f := by
    apply ((Fintype.bijective_iff_injective_and_card f).2 ⟨inj, ?_⟩).2
    apply (Fintype.card_le_of_injective f inj).antisymm
    simp only [Fintype.card_coe, Fintype.card_fin]
    exact hd
  obtain ⟨z, hz⟩ := surj j
  refine ⟨z, ha z, hz ▸ hf z, ?_⟩
  intro i hi hp hcontact
  obtain ⟨k, hk⟩ := site_of_contact P c hi hp (ha z) hcontact
  obtain ⟨y, hy⟩ := surj k
  have he : z = y := Subtype.ext (unique_at_site P h4 k (ha z) (hk ▸ hcontact)
    (ha y) (hy ▸ hf y))
  simpa [← hz, he, hy] using hk


/-- Replacing the first two internal vertices by a different induced three-edge
route preserves the induced path whenever the two replacement vertices have the
indicated contacts with the old path. -/
private def reroute (P : Chain G n) (x w : V) (hxw : G.Adj x w)
    (hx : ∀ i ≤ n, x ≠ P.vertex i) (hw : ∀ i ≤ n, w ≠ P.vertex i)
    (hxa : ∀ i ≤ n, G.Adj x (P.vertex i) ↔ i = 0)
    (hwa : ∀ i ≤ n, G.Adj w (P.vertex i) ↔ i = 3) : Chain G n where
  vertex i := if i = 1 then x else if i = 2 then w else P.vertex i
  inj := by
    intro i j hi hj
    split_ifs <;> intro he
    all_goals first
      | omega
      | exact (hxw.ne he).elim
      | exact (hxw.ne he.symm).elim
      | exact (hx _ hj he).elim
      | exact (hx _ hi he.symm).elim
      | exact (hw _ hj he).elim
      | exact (hw _ hi he.symm).elim
      | exact P.inj hi hj he
  edges := by
    intro i j hi hj
    split_ifs
    all_goals first
      | rw [hxa _ hj]; omega
      | rw [hwa _ hj]; omega
      | rw [G.adj_comm, hxa _ hi]; omega
      | rw [G.adj_comm, hwa _ hi]; omega
      | rw [P.edges hi hj]
      | simp only [SimpleGraph.irrefl, hxw, hxw.symm, true_iff, false_iff]; omega

theorem other_route [DecidableEq V]
    (P : Chain G n) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    (hn : 4 ≤ n) {x : V} (hx : Good P x)
    (hd : (n+1)/2 ≤ G.degree x) (sat : ∀ z, ¬Good (grow P x hx) z) :
    ∃ w, G.Adj x w ∧ (∀ i ≤ n, w ≠ P.vertex i) ∧
      (∀ i ≤ n, G.Adj w (P.vertex i) ↔ i = 3) := by
  let R := grow P x hx
  let j : Fin ((n+1)/2) := ⟨1, by omega⟩
  obtain ⟨w, hxw, h3, honly⟩ :=
    saturated_witness R c h4 (by omega) hd sat j
  change G.Adj x w at hxw
  change G.Adj (P.vertex 3) w at h3
  have only (i : ℕ) (hi : i ≤ n) (ha : G.Adj w (P.vertex i)) : i = 3 := by
    have := honly (i+1) (by omega) (by omega) ha.symm
    change i+1 = 2*1+2 at this
    omega
  refine ⟨w, hxw, ?_, fun i hi => ⟨only i hi, fun he => he ▸ h3.symm⟩⟩
  intro i hi he
  have hi0 : i = 0 := by
    by_contra h
    exact hx.2.2 i hi h (he ▸ hxw)
  have he0 : w = P.vertex 0 := hi0 ▸ he
  have ha : G.Adj (P.vertex 0) (P.vertex 1) :=
    (P.edges (Nat.zero_le _) (by omega)).2 (Or.inl rfl)
  have := only 1 (by omega) (he0 ▸ ha)
  omega



/-- A vertex of degree at least two above the minimum permits two alternative
three-edge routes from it. If neither endpoint can extend, the two routes force
a four-cycle. -/
theorem two_mul_minDegree_add_three_le_path_of_high_degree [DecidableEq V]
    (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G) {d : ℕ}
    (hd : 3 ≤ d) (hmin : ∀ x, d ≤ G.degree x) (v : V) (hv : d+2 ≤ G.degree v) :
    2*d+3 ≤ path G := by
  classical
  by_contra! hshort
  obtain ⟨T, hT⟩ := exists_chain_ending_at v c h4 (by omega : 2 ≤ d) hmin (2*d) le_rfl
  let P := T.reverse
  have hP : P.vertex 0 = v := by simpa [P, Chain.reverse] using hT
  have far_sat (Q : Chain G (2*d)) (hQ : Q.vertex 0 = v) (u : V) :
      ¬Good Q.reverse u := by
    intro hu
    let R := grow Q.reverse u hu
    have he : R.reverse.vertex 0 = v := by simpa [R, grow, Chain.reverse, Chain.prepend] using hQ
    have hdeg : d+2 ≤ G.degree (R.reverse.vertex 0) := he ▸ hv
    obtain ⟨S, _⟩ := R.reverse.extend c h4 (by omega) (by omega)
    have := S.length_le
    omega
  let j : Fin ((2*d)/2) := ⟨d-2, by omega⟩
  obtain ⟨z, hend, htwo, huniq⟩ := saturated_witness P.reverse c h4 (by omega)
    (by have := hmin (P.reverse.vertex 0); omega) (far_sat P hP) j
  have hidx : 2*d-(2*j.val+2) = 2 := by dsimp [j]; omega
  change G.Adj (P.vertex (2*d-(2*j.val+2))) z at htwo
  rw [hidx] at htwo
  have only2 (i : ℕ) (hi : i < 2*d) (ha : G.Adj (P.vertex i) z) : i = 2 := by
    have hrev : P.reverse.vertex (2*d-i) = P.vertex i := by
      change P.vertex _ = P.vertex _; congr 1; omega
    have := huniq (2*d-i) (by omega) (by omega) (hrev ▸ ha)
    omega
  have hdeg : (2*d)/2+2 ≤ G.degree (P.vertex 0) := by rw [hP]; omega
  obtain ⟨x, y, hx, hy, hxy⟩ := two_good P c h4 (by omega) hdeg
  have forced (a : V) (ha : Good P a) :
      ∃ w, G.Adj a w ∧ w ≠ P.vertex 0 ∧ G.Adj (P.vertex 3) w ∧ G.Adj z w := by
    have sat (u : V) : ¬Good (grow P a ha) u := by
      intro hu
      have := (grow (grow P a ha) u hu).length_le
      omega
    obtain ⟨w, haw, hw, hwAdj⟩ := other_route P c h4 (by omega) ha
      (by have := hmin a; omega) sat
    have haAdj (i : ℕ) (hi : i ≤ 2*d) : G.Adj a (P.vertex i) ↔ i = 0 := by
      exact ⟨fun h => by by_contra h'; exact ha.2.2 i hi h' h, fun h => h ▸ ha.1.symm⟩
    let Q := reroute P a w haw ha.2.1 hw haAdj hwAdj
    have hQ : Q.vertex 0 = v := hP
    have he : G.Adj (Q.reverse.vertex 0) z := by
      simpa [Q, reroute, Chain.reverse, show 2*d ≠ 1 by omega, show 2*d ≠ 2 by omega]
        using hend
    obtain ⟨k, hk⟩ := blocker Q.reverse c (by omega) he (far_sat Q hQ z)
    let t := 2*d-(2*k.val+2)
    have hkt := k.isLt
    have ht : t < 2*d := by dsimp [t]; omega
    have ht1 : t ≠ 1 := by dsimp [t]; omega
    change G.Adj (if t=1 then a else if t=2 then w else P.vertex t) z at hk
    by_cases ht2 : t = 2
    · have hwz : G.Adj w z := by simpa only [if_neg ht1, if_pos ht2] using hk
      exact ⟨w, haw, hw 0 (by omega), ((hwAdj 3 (by omega)).2 rfl).symm, hwz.symm⟩
    · have ht' : G.Adj (P.vertex t) z := by simpa [ht1, ht2] using hk
      exact (ht2 (only2 t ht ht')).elim
  obtain ⟨w, hxw, hw, hw3, hzw⟩ := forced x hx
  obtain ⟨u, hyu, hu, hu3, hzu⟩ := forced y hy
  have hwu : w ≠ u := by
    intro he
    exact hxy (h4 hw.symm hx.1 hxw.symm hy.1 (he ▸ hyu.symm))
  have h3z : P.vertex 3 ≠ z := by
    intro he
    change G.Adj (P.vertex (2*d-0)) z at hend
    rw [← he] at hend
    have := (P.edges (by omega) (by omega)).1 hend
    omega
  exact hwu (h4 h3z hw3 hzw hu3 hzu)



/-- At every even density threshold at least six, a four-cycle-free bipartite
graph contains an induced path exceeding the threshold by at least five. -/
theorem add_five_le_path_of_even_bipartite_density [DecidableEq V] [Nonempty V]
    (hb : G.IsBipartite) (h4 : NoFourCycle G)
    {m : ℕ} (hm : 3 ≤ m) (hav : (2*m : ℕ) ≤ l G) : 2*m+5 ≤ path G := by
  classical
  have hdeg := sum_degree_ge_of_le_l hav
  have hh : 2 * (∑ _v : V, m) ≤ ∑ v, G.degree v := by
    simpa [Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_comm] using hdeg
  obtain ⟨S, hS, hmin, hsum⟩ := exists_weighted_degree_core G (fun _ => m) (by omega) hh
  have : Nonempty S := hS.to_subtype
  let H := G.induce (S : Set V)
  obtain ⟨c⟩ := hb
  let C : H.Coloring (Fin 2) := ⟨fun x => c x.val, fun h => c.map_rel h⟩
  have h4' : NoFourCycle H := by
    intro x y a b hxy hxa hya hxb hyb
    exact Subtype.ext (h4 (x := x.val) (y := y.val) (fun h => hxy (Subtype.ext h))
      hxa hya hxb hyb)
  have hhigh : ∃ v : S, 2*m ≤ H.degree v := by
    by_contra! h
    have hlt := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun v _ => h v)
    have hh : ∑ v : S, H.degree v < 2 * ∑ _v ∈ S, m := by
      simpa [Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_comm] using hlt
    exact hh.not_ge hsum
  obtain ⟨v, hv⟩ := hhigh
  have hp := two_mul_minDegree_add_three_le_path_of_high_degree C h4' (d := m+1)
    (by omega) hmin v (by omega)
  have htransfer := G.path_induce_le (S : Set V)
  change path H ≤ _ at htransfer
  omega

/-- The conjectured inequality holds at radius five whenever the floor of the
average neighborhood independence number is even. -/
theorem radius_add_floor_le_path_of_bipartite_radius_five_even [DecidableEq V] [Nonempty V]
    (hc : G.Connected) (hb : G.IsBipartite) (h4 : NoFourCycle G)
    (hr : G.radius.toNat = 5) (he : ⌊l G⌋₊ % 2 = 0) :
    G.radius.toNat + ⌊l G⌋₊ ≤ path G := by
  by_cases hm : 3 ≤ ⌊l G⌋₊/2
  · have hav : (⌊l G⌋₊ : ℝ) ≤ l G :=
      Nat.floor_le (div_nonneg (Finset.sum_nonneg (fun v _ => Nat.cast_nonneg (G.indepNeighborsCard v)))
        (Nat.cast_nonneg _))
    have heq : 2*(⌊l G⌋₊/2) = ⌊l G⌋₊ := by omega
    have hp := add_five_le_path_of_even_bipartite_density hb h4 hm (by rwa [heq])
    omega
  · have := chung_bound_nat G hc
    omega



private def triple {w a v : V} (hwa : G.Adj w a) (hav : G.Adj a v) (hne : w ≠ v)
    (hna : ¬ G.Adj w v) : Chain G 2 where
  vertex i := if i = 0 then w else if i = 1 then a else v
  inj := by
    intro i j hi hj h
    interval_cases i <;> interval_cases j <;>
      simp_all [hwa.ne, hav.ne, Ne.symm hwa.ne, Ne.symm hav.ne, Ne.symm hne]
  edges := by
    intro i j hi hj
    interval_cases i <;> interval_cases j <;>
      simp_all [hwa.symm, hav.symm, G.adj_comm (u := v) (v := w)]

private theorem grow_triple (P : Chain G 2) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    {d : ℕ} (hmin : ∀ x, d ≤ G.degree x) (j : ℕ) (hj : j+2 ≤ 2*d) :
    ∃ Q : Chain G (j+2), Q.vertex (j+2) = P.vertex 2 ∧ Q.vertex j = P.vertex 0 := by
  induction j with
  | zero => exact ⟨P,rfl,rfl⟩
  | succ j ih =>
    obtain ⟨Q,hv,hw⟩ := ih (by omega)
    obtain ⟨x,hx⟩ := one_good Q c h4 (by omega) (by have := hmin (Q.vertex 0); omega)
    exact ⟨grow Q x hx,hv,hw⟩

private def turn (P : Chain G n) (hn : 4 ≤ n) {x : V}
    (hx : G.Adj (P.vertex 0) x) (hx' : G.Adj (P.vertex n) x)
    (honly : ∀ i ≤ n, i ≠ 0 → G.Adj (P.vertex i) x → i = n) : Chain G n where
  vertex i := if i = n then P.vertex n else if i+1 = n then x else P.vertex (n-2-i)
  inj := by
    have fresh (i) (hi : i ≤ n) : x ≠ P.vertex i := by
      intro he
      have h1 := (P.edges (Nat.zero_le _) hi).1 (he ▸ hx)
      have h2 := (P.edges le_rfl hi).1 (he ▸ hx')
      omega
    intro i j hi hj
    split_ifs <;> intro he
    all_goals first
      | omega
      | exact (fresh _ (by omega) he).elim
      | exact (fresh _ (by omega) he.symm).elim
      | have := P.inj (by omega) (by omega) he; omega
  edges := by
    have adj (i) (hi : i ≤ n) : G.Adj (P.vertex i) x ↔ i=0 ∨ i=n := by
      constructor
      · intro h; by_cases hz : i=0
        · exact Or.inl hz
        · exact Or.inr (honly i hi hz h)
      · rintro (rfl | rfl)
        · exact hx
        · exact hx'
    intro i j hi hj
    split_ifs
    all_goals first
      | rw [P.edges (by omega) (by omega)]; omega
      | rw [adj _ (by omega)]; omega
      | rw [G.adj_comm, adj _ (by omega)]; omega
      | simp only [SimpleGraph.irrefl, false_iff]; omega

omit [Fintype V] [DecidableRel G.Adj] in
private theorem cast_chain_vertex {i j : ℕ} (h : i = j) (P : Chain G i) (a : ℕ) :
    (h ▸ P : Chain G j).vertex a = P.vertex a := by subst j; rfl

/-- Starting at v and growing through w, a saturated final endpoint closes an
induced cycle. Removing the vertex between v and w exposes w for the last step. -/
theorem exists_odd_chain_of_common_neighbor (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ x, d ≤ G.degree x)
    {v a w : V} (hav : G.Adj a v) (hwa : G.Adj w a) (hne : w ≠ v)
    (hw : d+1 ≤ G.degree w) : ∃ P : Chain G (2*d+1), P.vertex (2*d+1) = v := by
  classical
  have cvw : c w = c v := by
    apply Fin.ext
    have := Fin.val_ne_of_ne (c.valid hav)
    have := Fin.val_ne_of_ne (c.valid hwa)
    have := (c a).isLt
    have := (c w).isLt
    have := (c v).isLt
    omega
  let T := triple hwa hav hne (fun h => c.valid h cvw)
  obtain ⟨Q, hv', hw'⟩ := grow_triple T c h4 hmin (2*d-2) (by omega)
  have hlen : 2*d-2+2 = 2*d := by omega
  let P : Chain G (2*d) := hlen ▸ Q
  have hP : P.vertex (2*d) = v := by simpa [P, cast_chain_vertex, hlen, T, triple] using hv'
  have hW : P.vertex (2*d-2) = w := by simpa [P, cast_chain_vertex, hlen, T, triple] using hw'
  by_cases hx : ∃ z, Good P z
  · obtain ⟨z,hz⟩ := hx
    exact ⟨grow P z hz,hP⟩
  let j : Fin ((2*d)/2) := ⟨d-1, by omega⟩
  have hj : 2*j.val+2 = 2*d := by dsimp [j]; omega
  obtain ⟨z,hz,hz',honly⟩ := saturated_witness P c h4 (by omega)
    (by have := hmin (P.vertex 0); omega) (fun z hz => hx ⟨z,hz⟩) j
  rw [hj] at hz' honly
  let U := turn P (by omega) hz hz' honly
  have hu : U.vertex (2*d) = v := by simpa [U, turn] using hP
  have hu0 : U.vertex 0 = w := by
    simpa [U,turn,show 0 ≠ 2*d by omega,show 1 ≠ 2*d by omega] using hW
  obtain ⟨z,hz⟩ := one_good U c h4 (by omega) (by rw [hu0]; omega)
  exact ⟨grow U z hz,hu⟩


/-- Two vertices on the lower-minimum-degree side that share a neighbor give
the odd-density path bound when they have degrees at least d+2 and d+1. -/
theorem odd_path_of_common_neighbor [DecidableEq V]
    (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G) {d : ℕ} (hd : 3 ≤ d)
    (hmin : ∀ x, d ≤ G.degree x) {v a w : V} (hav : G.Adj a v) (hwa : G.Adj w a)
    (hne : w ≠ v) (hv : d+2 ≤ G.degree v) (hw : d+1 ≤ G.degree w)
    (hpart : ∀ u, c u ≠ c v → d+1 ≤ G.degree u) : 2*d+4 ≤ path G := by
  obtain ⟨P,hP⟩ := exists_odd_chain_of_common_neighbor c h4 (by omega) hmin hav hwa hne hw
  have hpcolor := P.color_val c (2*d+1) le_rfl
  rw [hP] at hpcolor
  have hh := hpart (P.vertex 0) (fun he => by
    rw [he] at hpcolor
    have := (c v).isLt
    omega)
  obtain ⟨Q,hQ⟩ := P.extend c h4 (by omega) (by omega)
  have hlast : Q.reverse.vertex 0 = v := by simpa [Chain.reverse,hP] using hQ
  obtain ⟨X,_⟩ := Q.reverse.extend c h4 (by rw [hlast]; omega) (by rw [hlast]; omega)
  exact X.length_le



private theorem other_color {i j a : Fin 2} (hi : i ≠ a) (hj : i ≠ j) : j = a := by
  apply Fin.ext
  have := Fin.val_ne_of_ne hi
  have := Fin.val_ne_of_ne hj
  have := i.isLt
  have := j.isLt
  have := a.isLt
  omega

/-- A weighted odd-density core either already contains the desired path or
contains a vertex of degree at least d+2 on its higher-minimum-degree side. -/
theorem odd_core_path_or_high [DecidableEq V] [Nonempty V]
    (c : G.Coloring (Fin 2)) (a : Fin 2) (h4 : NoFourCycle G)
    {m : ℕ} (hm : 2 ≤ m)
    (hmin : ∀ v, m+1+(if c v = a then 1 else 0) ≤ G.degree v)
    (hsum : 2*(∑ v : V, (m + if c v = a then 1 else 0)) ≤ ∑ v : V, G.degree v) :
    2*(m+1)+4 ≤ path G ∨ ∃ v, c v = a ∧ (m+1)+2 ≤ G.degree v := by
  classical
  by_contra! hbad
  obtain ⟨hshort,hcap⟩ := hbad
  let A := (Finset.univ : Finset V).filter fun v => c v = a
  let B := (Finset.univ : Finset V).filter fun v => c v ≠ a
  let T := B.filter fun v => m+3 ≤ G.degree v
  have memA (v : V) : v ∈ A ↔ c v = a := by simp [A]
  have memB (v : V) : v ∈ B ↔ c v ≠ a := by simp [B]
  have hb : G.IsBipartiteWith (A : Set V) (B : Set V) := by
    constructor
    · exact Set.disjoint_left.mpr fun x hx hy => (memB x).mp hy ((memA x).mp hx)
    · intro v w hadj
      by_cases ha : c v = a
      · exact Or.inl ⟨(memA _).mpr ha, (memB _).mpr fun h => c.valid hadj (ha.trans h.symm)⟩
      · exact Or.inr ⟨(memB _).mpr ha,(memA _).mpr (other_color ha (c.valid hadj))⟩
  have balance := isBipartiteWith_sum_degrees_eq hb
  let E := ∑ v ∈ A, G.degree v
  change E = ∑ v ∈ B, G.degree v at balance
  have total : ∑ v, G.degree v = 2*E := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v : V => c v = a)]
    change E + (∑ v ∈ B, G.degree v) = _
    omega
  have part : A.card+B.card = Fintype.card V :=
    Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun v => c v=a)
  have costs : (∑ v : V, (m + if c v = a then 1 else 0)) = Fintype.card V*m + A.card := by
    simp [A,Finset.sum_add_distrib,Finset.sum_boole]
  rw [total, costs, ← part] at hsum
  have lowE : (m+1)*A.card+m*B.card ≤ E := by
    rw [Nat.add_mul] at hsum
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm m A.card,Nat.mul_comm m B.card]
    omega
  have upperA : E ≤ A.card * (m+2) := by
    simpa [E] using (Finset.sum_le_sum (s := A) (f := fun v => G.degree v)
      (g := fun _ => m+2) (fun v hv => by have := hcap v ((memA _).mp hv); omega))
  have pairwise : (T : Set V).PairwiseDisjoint (fun v => G.neighborFinset v) := by
    intro v hv w hw hne
    apply Finset.disjoint_left.mpr
    intro b h1 h2
    have hAv := (memB v).mp (Finset.mem_filter.mp hv).1
    have hdegV := (Finset.mem_filter.mp hv).2
    have hdegW := (Finset.mem_filter.mp hw).2
    have hav := ((G.mem_neighborFinset _ _).mp h1).symm
    have hwa := (G.mem_neighborFinset _ _).mp h2
    have bound := odd_path_of_common_neighbor c h4 (d := m+1) (by omega)
      (fun u => by have := hmin u; omega) hav hwa hne.symm (by omega) (by omega)
      (fun u hu => by have := hmin u; simpa [other_color hAv hu.symm] using this)
    omega
  have neighborsA : T.biUnion (fun v => G.neighborFinset v) ⊆ A := by
    intro b hb'
    obtain ⟨v,hv,hb'⟩ := Finset.mem_biUnion.mp hb'
    exact (memA b).mpr (other_color ((memB v).mp (Finset.mem_filter.mp hv).1)
      (c.valid ((G.mem_neighborFinset _ _).mp hb')))
  have largeSum : ∑ v ∈ T, G.degree v ≤ A.card := by
    have h := Finset.card_le_card neighborsA
    rwa [Finset.card_biUnion pairwise] at h
  let L := B.filter fun v => ¬m+3 ≤ G.degree v
  have splitE : (∑ v ∈ T, G.degree v)+(∑ v ∈ L, G.degree v) = E :=
    (Finset.sum_filter_add_sum_filter_not B _ _).trans balance.symm
  have smallSum : ∑ v ∈ L, G.degree v ≤ B.card*(m+2) := by
    calc
      _ ≤ L.card*(m+2) := by
        simpa using (Finset.sum_le_sum (s := L) (f := fun v => G.degree v) (g := fun _ => m+2)
          (fun v hv => by have := (Finset.mem_filter.mp hv).2; omega))
      _ ≤ _ := Nat.mul_le_mul_right _ (Finset.card_le_card (Finset.filter_subset _ _))
  have lowerA : m*B.card ≤ A.card := by
    have he : A.card*(m+2) = (m+1)*A.card + A.card := by ring
    omega
  have lowerB : m*A.card ≤ 2*B.card := by
    have he : B.card*(m+2) = m*B.card+2*B.card := by ring
    have he' : (m+1)*A.card = m*A.card+A.card := by ring
    omega
  have := Nat.mul_le_mul_right A.card hm
  have := Nat.mul_le_mul_right B.card hm
  have := Fintype.card_pos (α := V)
  omega

end Wall133
