import Wall133.OddRadiusFive

namespace Wall133
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

private def fourChain (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G) {a x u y b : V}
    (ha : a ≠ u) (hb : b ≠ u) (hxy : x ≠ y) (hax : G.Adj a x) (hux : G.Adj u x)
    (huy : G.Adj u y) (hby : G.Adj b y) : Chain G 4 := by
  have hab : a ≠ b := fun e => hxy (h4 ha hax hux (e ▸ hby) huy)
  have cay : ¬G.Adj a y := fun h => hxy (h4 ha hax hux h huy)
  have cbx : ¬G.Adj b x := fun h => hxy (h4 hb h hux hby huy)
  have ca := color_common c hax hux
  have cb := color_common c hby huy
  have cx := color_common c hux.symm huy.symm
  have no {z w : V} (he : c z = c w) : ¬G.Adj z w := fun h => c.valid h he
  have hax' : a ≠ y := fun e => c.valid hax ((congrArg c e).trans cx.symm)
  have hbx' : b ≠ x := fun e => c.valid hby ((congrArg c e).trans cx)
  let f : ℕ → V
    | 0 => a
    | 1 => x
    | 2 => u
    | 3 => y
    | _ => b
  refine ⟨f, ?_, ?_⟩
  · intro i j hi hj e
    interval_cases i <;> interval_cases j <;> first
      | rfl
      | simp only [f] at e
        grind [hax.ne, hux.ne, huy.ne, hby.ne]
  · intro i j hi hj
    interval_cases i <;> interval_cases j <;> simp [f, hax, hax.symm, hby, hby.symm,
      hux, hux.symm, huy, huy.symm, no ca, no ca.symm, no cb, no cb.symm,
      no cx, no cx.symm, no (ca.trans cb.symm), no (cb.trans ca.symm), cay, cbx,
      show ¬G.Adj y a from fun h => cay h.symm, show ¬G.Adj x b from fun h => cbx h.symm]

variable [Fintype V] [DecidableRel G.Adj]

/-- At or above an average degree threshold, two vertices meeting the
threshold occur as the endpoints of an induced four-edge path. -/
theorem exists_high_four_chain_of_average [Nonempty V] (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) {h : ℕ} (hh : 3 ≤ h) (hav : h * Fintype.card V ≤ ∑ v, G.degree v) :
    ∃ P : Chain G 4, h ≤ G.degree (P.vertex 0) ∧ h ≤ G.degree (P.vertex 4) := by
  classical
  let T := Finset.univ.filter fun u : V => h ≤ G.degree u
  let L := Finset.univ.filter fun u : V => ¬h ≤ G.degree u
  have memT (u : V) : u ∈ T ↔ h ≤ G.degree u := by simp [T]
  have size : T.card+L.card = Fintype.card V := by
    simpa [T,L] using Finset.univ.card_filter_add_card_filter_not (fun u : V => h ≤ G.degree u)
  have total : (∑ u ∈ T, G.degree u)+(∑ u ∈ L, G.degree u) = ∑ u, G.degree u :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have low : ∑ u ∈ L, G.degree u ≤ L.card * (h-1) := by
    simpa using (Finset.sum_le_sum (s := L) (f := fun u => G.degree u) (g := fun _ => h-1)
      (fun u hu => by have := (Finset.mem_filter.mp hu).2; omega))
  have nonempty : 0 < T.card := by
    by_contra! hT
    have he : T = ∅ := Finset.card_eq_zero.mp (by omega)
    simp only [he, Finset.card_empty, zero_add, Finset.sum_empty] at total size
    have hn := Fintype.card_pos (α := V)
    have hd := Nat.mul_lt_mul_of_pos_left (by omega : h-1 < h) hn
    rw [size] at low
    rw [Nat.mul_comm h] at hav
    omega
  let Private (u z : V) := ∀ w ∈ T, G.Adj w z → w = u
  let priv (u : V) := (G.neighborFinset u).filter (Private u)
  by_contra! hbad
  have unique (u : V) (hu : u ∈ T) :
      ((G.neighborFinset u).filter (fun z => ¬Private u z)).card ≤ 1 := by
    by_contra! htwo
    obtain ⟨x,y,hx,hy,hxy⟩ := Finset.one_lt_card_iff.mp htwo
    obtain ⟨hx,hx'⟩ := Finset.mem_filter.mp hx
    obtain ⟨hy,hy'⟩ := Finset.mem_filter.mp hy
    dsimp [Private] at hx' hy'
    push Not at hx' hy'
    obtain ⟨a,ha,hax,hau⟩ := hx'
    obtain ⟨b,hb,hby,hbu⟩ := hy'
    let P := fourChain c h4 hau hbu hxy hax ((G.mem_neighborFinset _ _).mp hx)
      ((G.mem_neighborFinset _ _).mp hy) hby
    have hpa : h ≤ G.degree (P.vertex 0) := (memT a).1 ha
    have hpb : h ≤ G.degree (P.vertex 4) := (memT b).1 hb
    exact (hbad P hpa).not_ge hpb
  have disj : (T : Set V).PairwiseDisjoint priv := by
    intro u hu w hw huw
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    have hn := (Finset.mem_filter.mp hz).2 w hw
      ((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hz').1)
    exact huw hn.symm
  have privsum : ∑ u ∈ T, (priv u).card ≤ Fintype.card V := by
    rw [← Finset.card_biUnion disj]
    exact Finset.card_le_univ _
  have high : ∑ u ∈ T, G.degree u ≤ Fintype.card V + T.card := by
    have per (u : V) (hu : u ∈ T) : G.degree u ≤ (priv u).card+1 := by
      have hcard := (G.neighborFinset u).card_filter_add_card_filter_not (Private u)
      rw [G.card_neighborFinset_eq_degree] at hcard
      have := unique u hu
      change (priv u).card + _ = _ at hcard
      omega
    have hh := Finset.sum_le_sum per
    rw [Finset.sum_add_distrib] at hh
    simpa using (hh.trans (Nat.add_le_add_right privsum _))
  have hhm : h-1+1 = h := by omega
  rw [← size] at hav high
  rw [← hhm, Nat.add_mul, Nat.one_mul, Nat.mul_add] at hav
  have ht := Nat.mul_le_mul_left T.card (show 2 ≤ h-1 by omega)
  rw [Nat.mul_comm T.card (h-1)] at ht
  rw [Nat.mul_comm L.card (h-1)] at low
  omega

end Wall133
