module

public import Erdos617.BoundedDegree
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Erdos617

variable {V : Type*}

private abbrev NoDiamond (G : SimpleGraph V) : Prop :=
  ∀ a b y z, G.Adj a b → G.Adj a y → G.Adj b y → G.Adj a z → G.Adj b z → y = z

private abbrev EveryTripleHasEdge (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, a ≠ b → a ≠ c → b ≠ c →
    G.Adj a b ∨ G.Adj a c ∨ G.Adj b c

/-- The usual six-vertex Ramsey argument, restricted to T. -/
private theorem triangle_in_six (G : SimpleGraph V) (T : Finset V) (hcard : 6 ≤ T.card)
    (hthree : EveryTripleHasEdge G T) :
    ∃ a ∈ T, ∃ b ∈ T, ∃ c ∈ T, G.Adj a b ∧ G.Adj a c ∧ G.Adj b c := by
  classical
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
  let U := T.erase x
  by_cases hN : 2 < (U.filter (G.Adj x)).card
  · obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hN
    simp only [Finset.mem_filter, U, Finset.mem_erase] at ha hb hc
    rcases hthree a ha.1.2 b hb.1.2 c hc.1.2 hab hac hbc with e | e | e
    · exact ⟨x, hx, a, ha.1.2, b, hb.1.2, ha.2, hb.2, e⟩
    · exact ⟨x, hx, a, ha.1.2, c, hc.1.2, ha.2, hc.2, e⟩
    · exact ⟨x, hx, b, hb.1.2, c, hc.1.2, hb.2, hc.2, e⟩
  · have hcU : U.card = T.card - 1 := Finset.card_erase_of_mem hx
    have hsum := U.card_filter_add_card_filter_not (G.Adj x)
    have houtside : 2 < (U.filter (fun y => ¬ G.Adj x y)).card := by omega
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp houtside
    simp only [Finset.mem_filter, U, Finset.mem_erase] at ha hb hc
    have edge (y z : V) (hy : (y ≠ x ∧ y ∈ T) ∧ ¬ G.Adj x y)
        (hz : (z ≠ x ∧ z ∈ T) ∧ ¬ G.Adj x z) (hyz : y ≠ z) : G.Adj y z :=
      ((hthree x hx y hy.1.2 z hz.1.2 hy.1.1.symm hz.1.1.symm hyz).resolve_left hy.2).resolve_left hz.2
    exact ⟨a, ha.1.2, b, hb.1.2, c, hc.1.2, edge a b ha hb hab, edge a c ha hc hac,
      edge b c hb hc hbc⟩

/-- Every vertex outside a triangle is adjacent to at most one of its vertices. -/
private theorem at_most_one (G : SimpleGraph V) (hd : NoDiamond G) {a b c x : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (ha : x ≠ a) (hb : x ≠ b) (hc : x ≠ c) :
    ¬ (G.Adj a x ∧ G.Adj b x) ∧ ¬ (G.Adj a x ∧ G.Adj c x) ∧ ¬ (G.Adj b x ∧ G.Adj c x) := by
  exact ⟨fun h => hc (hd a b x c hab h.1 h.2 hac hbc),
    fun h => hb (hd a c x b hac h.1 h.2 hab hbc.symm),
    fun h => ha (hd b c x a hbc h.1 h.2 hab.symm hac.symm)⟩

/-- The vertices outside any triangle form a clique: if x and y outside were
nonadjacent, their neighbors in the triangle could cover at most two vertices. -/
private theorem triangle_complement_clique (G : SimpleGraph V) (T : Finset V)
    (hcard : 6 ≤ T.card) (hd : NoDiamond G) (hthree : EveryTripleHasEdge G T) [DecidableEq V] :
    ∃ A : Finset V, A ⊆ T ∧ G.IsNClique 3 A ∧ G.IsClique (↑(T \ A) : Set V) := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := triangle_in_six G T hcard hthree
  refine ⟨{a,b,c}, by simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, ha, hb, hc], G.is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩, ?_⟩
  intro x hx y hy hxy
  simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
    not_or] at hx hy
  have hnx := at_most_one G hd hab hac hbc hx.2.1 hx.2.2.1 hx.2.2.2
  have hny := at_most_one G hd hab hac hbc hy.2.1 hy.2.2.1 hy.2.2.2
  by_contra hn
  have hedge (z : V) (hz : z ∈ T) (hxz : x ≠ z) (hyz : y ≠ z) :
      G.Adj z x ∨ G.Adj z y := by
    rcases (hthree x hx.1 y hy.1 z hz hxy hxz hyz).resolve_left hn with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  have ea := hedge a ha hx.2.1 hy.2.1
  have eb := hedge b hb hx.2.2.1 hy.2.2.1
  have ec := hedge c hc hx.2.2.2 hy.2.2.2
  rcases ea with ax | ay <;> rcases eb with bx | by' <;> rcases ec with cx | cy
  all_goals first
    | exact hnx.1 ⟨ax, bx⟩
    | exact hnx.2.1 ⟨ax, cx⟩
    | exact hnx.2.2 ⟨bx, cx⟩
    | exact hny.1 ⟨ay, by'⟩
    | exact hny.2.1 ⟨ay, cy⟩
    | exact hny.2.2 ⟨by', cy⟩

private theorem false_of_seven (G : SimpleGraph V) (T : Finset V) (hcard : T.card = 7)
    (hdiamond : NoDiamond G) (hthree : EveryTripleHasEdge G T) : False := by
  classical
  obtain ⟨A, hAT, hA, hB⟩ := triangle_complement_clique G T (by omega) hdiamond hthree
  have hc : 3 < (T \ A).card := by rw [Finset.card_sdiff_of_subset hAT, hcard, hA.card_eq]; decide
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩ :=
    Finset.three_lt_card_iff.mp hc
  exact hcd (hdiamond a b c d (hB ha hb hab) (hB ha hc hac) (hB hb hc hbc)
    (hB ha hd had) (hB hb hd hbd))

/-- On ten vertices, if all three color degrees at a vertex are at least three,
then every one of them is exactly three. -/
private theorem colorGraph_degree_eq_three {V : Type*} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V = 10) (c : Sym2 V → Fin 3) (x : V)
    (hmin : ∀ k, 3 ≤ (colorGraph c k).degree x) (k : Fin 3) :
    (colorGraph c k).degree x = 3 := by
  have hs := sum_colorGraph_degree c x
  rw [hV, Fin.sum_univ_three] at hs
  have h0 := hmin 0
  have h1 := hmin 1
  have h2 := hmin 2
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> decide
  rcases hk with rfl | rfl | rfl <;> omega

variable {V : Type*} [DecidableEq V] (c : Sym2 V → Fin 3)

/-- Six edge colors of a four-set, in the order ab, ad, ae, bd, be, de. -/
private def HitsFour : Prop :=
  ∀ (a b d e : V), a ≠ b → a ≠ d → a ≠ e → b ≠ d → b ≠ e → d ≠ e →
    ∀ k, c s(a, b) = k ∨ c s(a, d) = k ∨ c s(a, e) = k ∨
         c s(b, d) = k ∨ c s(b, e) = k ∨ c s(d, e) = k

private theorem hitsFour_of_no_witness
    (h : ¬ ∃ (S : Finset V) (k : Fin 3), S.card = 4 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u, v) ≠ k) : HitsFour c := by
  intro a b d e hab had hae hbd hbe hde k
  by_contra! hnone
  obtain ⟨n₁, n₂, n₃, n₄, n₅, n₆⟩ := hnone
  apply h
  refine ⟨{a, b, d, e}, k, by simp [hab, had, hae, hbd, hbe, hde], ?_⟩
  intro u hu v hv huv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl
  all_goals first | exact False.elim (huv rfl) | assumption | rwa [Sym2.eq_swap]

/-- Five edges of a diamond have one color, so its four vertices see at most two colors. -/
private theorem common_neighbor_unique (h : HitsFour c) (k : Fin 3)
    (a b y z : V) (hab : (colorGraph c k).Adj a b)
    (hay : (colorGraph c k).Adj a y) (hby : (colorGraph c k).Adj b y)
    (haz : (colorGraph c k).Adj a z) (hbz : (colorGraph c k).Adj b z) : y = z := by
  by_contra hyz
  have third : ∀ i j : Fin 3, ∃ l, l ≠ i ∧ l ≠ j := by decide
  obtain ⟨l, hli, hlj⟩ := third k (c s(y, z))
  have seen := h a b y z hab.ne hay.ne haz.ne hby.ne hbz.ne hyz l
  simp [hab.2, hay.2, haz.2, hby.2, hbz.2, hli.symm, hlj.symm] at seen

/-- An independent triple among the nonneighbors of x would extend to an independent four-set. -/
private theorem three_nonneighbors [Fintype V] (h : HitsFour c) (k : Fin 3)
    (x : V) (T : Finset V) (hT : T ⊆ (colorGraph c k)ᶜ.neighborFinset x)
    (a : V) (ha : a ∈ T) (b : V) (hb : b ∈ T) (d : V) (hd : d ∈ T)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    (colorGraph c k).Adj a b ∨ (colorGraph c k).Adj a d ∨ (colorGraph c k).Adj b d := by
  have prop (y : V) (hy : y ∈ T) : x ≠ y ∧ c s(x,y) ≠ k := by
    have hn := ((colorGraph c k)ᶜ.mem_neighborFinset x y).mp (hT hy)
    exact ⟨hn.ne, fun he => hn.2 ⟨hn.ne, he⟩⟩
  obtain ⟨hxa, na⟩ := prop a ha
  obtain ⟨hxb, nb⟩ := prop b hb
  obtain ⟨hxd, nd⟩ := prop d hd
  have seen := h x a b d hxa hxb hxd hab had hbd k
  simpa [colorGraph_adj, hab, had, hbd, na, nb, nd] using seen

/-- The unrestricted three-color case on ten vertices. -/
theorem three_colors {V : Type*} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V = 10) (c : Sym2 V → Fin 3) :
    ∃ (S : Finset V) (k : Fin 3), S.card = 4 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u, v) ≠ k := by
  by_contra h
  have seen := hitsFour_of_no_witness c h
  have hd (k : Fin 3) : NoDiamond (colorGraph c k) := common_neighbor_unique c seen k
  have hdeg (k : Fin 3) (x : V) : (colorGraph c k).degree x = 3 := by
    apply colorGraph_degree_eq_three hV c x _ k
    intro j
    by_contra! hj
    have seven : 7 ≤ ((colorGraph c j)ᶜ.neighborFinset x).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.degree_compl, hV]
      omega
    obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq seven
    exact false_of_seven _ T hcard (hd j) (three_nonneighbors c seen j x T hT)
  exact h (missing_of_bounded_color_degree 3 le_rfl hV c 0 (fun x => (hdeg 0 x).le))

end Erdos617
