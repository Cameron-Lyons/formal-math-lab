module

public import Erdos617.BoundedDegree
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

@[expose] public section

namespace Erdos617

open SimpleGraph Finset

/-- A first failure of the independent-set bound inside a specified vertex set. -/
structure MinimalObstruction {V : Type*} {r : ℕ} (c : Sym2 V → Fin r) (k : Fin r)
    (t : ℕ) (S : Finset V) : Prop where
  card_eq : S.card = t * r + 1
  free : ∀ I ⊆ S, ¬ (colorGraph c k).IsNIndepSet (t + 1) I
  smaller : ∀ u < t, ∀ W ⊆ S, W.card = u * r + 1 →
    ∃ I ⊆ W, (colorGraph c k).IsNIndepSet (u + 1) I

variable {V : Type*} {r t : ℕ} {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V}

theorem MinimalObstruction.pos (h : MinimalObstruction c k t S) : 0 < t := by
  by_contra! ht
  obtain rfl := Nat.eq_zero_of_le_zero ht
  have hc : S.card = 1 := by simpa using h.card_eq
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc
  exact h.free {v} Finset.Subset.rfl ⟨by simp [IsIndepSet], by simp⟩

/-- Every smaller subset satisfies the bound, including orders between consecutive
numbers of the form u*r+1. -/
theorem MinimalObstruction.proper_subset (h : MinimalObstruction c k t S) (hr : 0 < r)
    (W : Finset V) (hW : W ⊂ S) :
    ∃ J ⊆ W, (colorGraph c k).IsIndepSet J ∧ W.card ≤ J.card * r := by
  classical
  rcases Nat.eq_zero_or_pos W.card with hzero | hpos
  · exact ⟨∅, Finset.empty_subset _, by simp [IsIndepSet], by simp [hzero]⟩
  let u := (W.card - 1) / r
  have hsmall : W.card < t * r + 1 := h.card_eq ▸ Finset.card_lt_card hW
  have hut : u < t := (Nat.div_lt_iff_lt_mul hr).mpr (by omega)
  have hlo : u * r + 1 ≤ W.card := by
    have : u * r ≤ W.card - 1 := Nat.div_mul_le_self _ _
    omega
  have hhi : W.card ≤ (u + 1) * r := by
    have : W.card - 1 < (u + 1) * r :=
      (Nat.div_lt_iff_lt_mul hr).mp (show (W.card - 1) / r < u + 1 from Nat.lt_succ_self u)
    omega
  obtain ⟨A, hAW, hA⟩ := Finset.exists_subset_card_eq hlo
  obtain ⟨J, hJA, hJ⟩ := h.smaller u hut A (hAW.trans hW.le) hA
  exact ⟨J, hJA.trans hAW, hJ.isIndepSet, hJ.card_eq ▸ hhi⟩

/-- Any vertex of a minimal obstruction has at least r neighbors inside it in its color.
Otherwise its nonneighbors contain a smaller independent set to which it can be added. -/
theorem MinimalObstruction.degree_ge [DecidableEq V] (h : MinimalObstruction c k t S) (x : V) (hx : x ∈ S) :
    r ≤ (S.filter ((colorGraph c k).Adj x)).card := by
  classical
  let G := colorGraph c k
  by_contra! hd
  let U := (S.erase x).filter fun v => ¬ G.Adj x v
  have hs := (S.erase x).card_filter_add_card_filter_not (G.Adj x)
  have hn : ((S.erase x).filter (G.Adj x)).card ≤ (S.filter (G.Adj x)).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset x S))
  rw [Finset.card_erase_of_mem hx, h.card_eq, Nat.add_sub_cancel] at hs
  have ht := h.pos
  have hsplit : (t - 1) * r + r = t * r := by
    rw [← Nat.succ_mul, show (t-1).succ = t by omega]
  have hu : (t-1)*r+1 ≤ U.card := by
    change (S.filter (G.Adj x)).card < r at hd
    change ((S.erase x).filter (G.Adj x)).card + U.card = t*r at hs
    omega
  obtain ⟨A, hAU, hA⟩ := Finset.exists_subset_card_eq hu
  have hAS : A ⊆ S := hAU.trans ((Finset.filter_subset _ _).trans (Finset.erase_subset x S))
  obtain ⟨I, hIA, hI⟩ := h.smaller (t-1) (by omega) A hAS hA
  have hIU := hIA.trans hAU
  have hxI : x ∉ I := fun hxI => (Finset.mem_erase.mp (Finset.mem_filter.mp (hIU hxI)).1).1 rfl
  have hi := independent_insert_of_nonadjacent G hI.isIndepSet x
    (fun _ hv => (Finset.mem_filter.mp (hIU hv)).2)
  apply h.free (insert x I) (Finset.insert_subset hx (hIA.trans hAS))
  exact ⟨hi, by rw [Finset.card_insert_of_notMem hxI, hI.card_eq, Nat.sub_add_cancel ht]⟩

/-- Minimize the size of a failed independence bound inside the given set. -/
theorem minimalObstruction_of_failure {s : ℕ} (hS : S.card = s*r+1)
    (hfree : ∀ I ⊆ S, ¬ (colorGraph c k).IsNIndepSet (s+1) I) :
    ∃ (t : ℕ) (W : Finset V), t ≤ s ∧ W ⊆ S ∧ MinimalObstruction c k t W := by
  classical
  let Bad (u : ℕ) := ∃ W ⊆ S, W.card = u*r+1 ∧
    ∀ I ⊆ W, ¬ (colorGraph c k).IsNIndepSet (u+1) I
  have hs : Bad s := ⟨S, Subset.rfl, hS, hfree⟩
  have he : ∃ u, Bad u := ⟨s, hs⟩
  obtain ⟨W, hWS, hW, hf⟩ := Nat.find_spec he
  refine ⟨Nat.find he, W, Nat.find_min' he hs, hWS, hW, hf, ?_⟩
  intro u hu A hAW hA
  by_contra! hn
  exact Nat.find_min he hu ⟨A, hAW.trans hWS, hA, hn⟩

/-- A hypothetical balanced coloring has a minimal obstruction strictly before the
last block. The last local step guarantees a failure at or below r−1. -/
theorem exists_minimalObstruction [Fintype V] [DecidableEq V] (hr : 3 ≤ r)
    (hV : Fintype.card V = r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c) :
    ∃ (k : Fin r) (t : ℕ) (S : Finset V), 1 ≤ t ∧ t < r ∧ MinimalObstruction c k t S := by
  classical
  let Bad (u : ℕ) := ∃ (k : Fin r) (S : Finset V), S.card = u*r+1 ∧
    ∀ I ⊆ S, ¬ (colorGraph c k).IsNIndepSet (u+1) I
  have hlast : Bad (r-1) := by
    by_contra hn
    obtain ⟨S, k, hS, hmiss⟩ := missing_of_last_local_step hr hV c (by
      intro _ k S hS
      by_contra! hf
      exact hn ⟨k, S, hS, by simpa [Nat.sub_add_cancel (show 1 ≤ r by omega)] using hf⟩)
    obtain ⟨u, hu, v, hv, huv, he⟩ := hb S hS k
    exact hmiss u hu v hv huv he
  obtain ⟨k, S, hS, hf⟩ := hlast
  obtain ⟨t, W, ht, _, hm⟩ := minimalObstruction_of_failure hS hf
  exact ⟨k, t, W, hm.pos, by omega, hm⟩

/-- A full clique can be removed from a first obstruction. Its complement supplies an
independent set of size t, which leaves at least one member of the clique available. -/
theorem MinimalObstruction.no_clique (h : MinimalObstruction c k t S)
    (hb : Balanced c) (ht : t < r) (C : Finset V) (hCS : C ⊆ S) :
    ¬ (colorGraph c k).IsNClique r C := by
  classical
  intro hC
  have hpos := h.pos
  have hrest : (S \ C).card = (t-1)*r+1 := by
    rw [Finset.card_sdiff_of_subset hCS, h.card_eq, hC.card_eq]
    have := Nat.succ_mul (t-1) r
    rw [show (t-1).succ = t by omega] at this
    omega
  obtain ⟨J, hJsub, hJ⟩ := h.smaller (t-1) (by omega) _ Finset.sdiff_subset hrest
  rw [Nat.sub_add_cancel hpos] at hJ
  have hdisj : Disjoint C J := Finset.disjoint_left.mpr
    fun _ hc hj => (Finset.mem_sdiff.mp (hJsub hj)).2 hc
  obtain ⟨I, hI, hi⟩ := extend_across_clique_within (colorGraph c k) C J hC hJ hdisj ht
    (fun x hx _ hy _ hz => exterior_clique_neighbor_unique c hb k C hC x hx hy hz)
  exact h.free I (hI.trans (Finset.union_subset hCS (hJsub.trans Finset.sdiff_subset))) hi

/-- A small total excess leaves a maximum independent set whose vertices each
have excess at most one. -/
private theorem MinimalObstruction.exists_maximum_low_excess {V : Type*} [DecidableEq V] {r t : ℕ}
    {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V} (h : MinimalObstruction c k t S)
    (ht : t < r) :
    let G := colorGraph (fun e : Sym2 S => c (Sym2.map Subtype.val e)) k
    (∑ v, (G.degree v - r)) < 2*r-2 →
      ∃ I, G.IsMaximumIndepSet I ∧ (∑ v ∈ I, (G.degree v - r)) < r := by
  classical
  intro G hT
  let d (v : S) := G.degree v - r
  let H := univ.filter fun v => 2 ≤ d v
  have hH : 2 * H.card ≤ ∑ v, d v := calc
    2 * H.card = ∑ _ ∈ H, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ v ∈ H, d v := sum_le_sum fun _ hv => (mem_filter.mp hv).2
    _ ≤ ∑ v, d v := sum_le_sum_of_subset_of_nonneg (subset_univ H) (by simp)
  change (∑ v, d v) < 2*r-2 at hT
  have htr : (t-1)*r+r = t*r := by rw [← Nat.succ_mul, show (t-1).succ = t by have := h.pos; omega]
  have many : (t-1)*r+1 ≤ Hᶜ.card := by
    rw [card_compl, Fintype.card_coe, h.card_eq]
    omega
  obtain ⟨W, hWL, hW⟩ := exists_subset_card_eq many
  let incl := Function.Embedding.subtype (· ∈ S)
  have hWS : W.map incl ⊆ S := fun _ hy => W.property_of_mem_map_subtype hy
  obtain ⟨J, hJW, hJ⟩ := h.smaller (t-1) (by have := h.pos; omega) (W.map incl)
    hWS ((card_map _).trans hW)
  let I := J.subtype (· ∈ S)
  have hmap : I.map incl = J := subtype_map_of_mem (hJW.trans hWS)
  have hIW : I ⊆ W := map_subset_map.mp (hmap ▸ hJW)
  have hIcard : I.card = t := by
    rw [← card_map incl, hmap, hJ.card_eq, Nat.sub_add_cancel h.pos]
  have hI : G.IsIndepSet I := by
    intro a ha b hb hab e
    have hne : a.val ≠ b.val := fun he => hab (Subtype.ext he)
    exact hJ.isIndepSet (mem_subtype.mp ha) (mem_subtype.mp hb) hne ⟨hne, e.2⟩
  refine ⟨I, ⟨hI, ?_⟩, ?_⟩
  · intro K hK
    rw [hIcard]
    by_contra! hlarge
    obtain ⟨A, hAK, hA⟩ := exists_subset_card_eq hlarge
    obtain ⟨B, hBS, hB⟩ := lift_independent_subset c k S
      ⟨A, hK.mono hAK, hA⟩
    exact h.free B hBS hB
  · have hone (v : S) (hv : v ∈ I) : d v ≤ 1 := by
      have hn := mem_compl.mp (hWL (hIW hv))
      simpa [H] using hn
    exact (sum_le_sum hone).trans_lt (by simpa [hIcard] using ht)

/-- After restricting the coloring to a first obstruction, the total excess of its
degrees above r is at least 2r−2. -/
theorem MinimalObstruction.excess_ge [DecidableEq V] (h : MinimalObstruction c k t S)
    (hr : 3 ≤ r) (hb : Balanced c) (ht : t < r) :
    2*r-2 ≤ ∑ x : S, ((colorGraph (fun e : Sym2 S => c (Sym2.map Subtype.val e)) k).degree x - r) := by
  classical
  let G := colorGraph (fun e : Sym2 S => c (Sym2.map Subtype.val e)) k
  have hfree : G.IndepSetFree (t+1) := by
    intro I hI
    obtain ⟨J, hJS, hJ⟩ := lift_independent_subset c k S ⟨I, hI⟩
    exact h.free J hJS hJ
  by_contra! hsmall
  obtain ⟨C, hC⟩ := clique_of_small_independent_excess r t hr G ((Fintype.card_coe S).trans h.card_eq)
    hsmall hfree (h.exists_maximum_low_excess ht hsmall)
  let incl := Function.Embedding.subtype (· ∈ S)
  apply h.no_clique hb ht (C.map incl) (fun _ hx => C.property_of_mem_map_subtype hx)
  refine ⟨?_, (Finset.card_map _).trans hC.card_eq⟩
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨b, hb', rfl⟩ := Finset.mem_map.mp hy
  exact ⟨hxy, (hC.isClique ha hb' (fun he => hxy (congrArg incl he))).2⟩

/-- The color of a first obstruction occupies at least this many edge incidences
inside it. Degrees in this statement are relative to the obstruction. -/
theorem MinimalObstruction.twice_edges_ge [DecidableEq V] (h : MinimalObstruction c k t S)
    (hr : 3 ≤ r) (hb : Balanced c) (ht : t < r) :
    let G := colorGraph (fun e : Sym2 S => c (Sym2.map Subtype.val e)) k
    S.card*r + (2*r-2) ≤ 2*G.edgeFinset.card := by
  classical
  intro G
  have hd (x : S) : r ≤ G.degree x := by
    have hn : (G.neighborFinset x).map (Function.Embedding.subtype (· ∈ S)) =
        S.filter ((colorGraph c k).Adj x.val) := by
      ext v
      constructor
      · intro hv
        obtain ⟨y, hy, rfl⟩ := mem_map.mp hv
        have he := (G.mem_neighborFinset x y).mp hy
        exact mem_filter.mpr ⟨y.prop, fun hxy => he.1 (Subtype.ext hxy), he.2⟩
      · intro hv
        obtain ⟨hvS, he⟩ := mem_filter.mp hv
        refine mem_map.mpr ⟨⟨v, hvS⟩, (G.mem_neighborFinset _ _).mpr ?_, rfl⟩
        exact ⟨fun hxy => he.1 (congrArg Subtype.val hxy), he.2⟩
    have hc := congrArg Finset.card hn
    rw [card_map, card_neighborFinset_eq_degree] at hc
    exact hc ▸ h.degree_ge x.val x.prop
  have hs := h.excess_ge hr hb ht
  calc
    S.card*r + (2*r-2) ≤ S.card*r + ∑ x, (G.degree x-r) := Nat.add_le_add_left hs _
    _ = ∑ x, (r + (G.degree x-r)) := by simp [Finset.sum_add_distrib]
    _ = ∑ x, G.degree x := Finset.sum_congr rfl fun x _ => Nat.add_sub_of_le (hd x)
    _ = 2*G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges

/-- A cut in a minimal obstruction retains an edge after fewer than the
respective residue-sized numbers of vertices are deleted on each side. -/
theorem MinimalObstruction.cross_edge_after_deletions {V : Type*} [DecidableEq V]
    {r t a b u v : ℕ} {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V}
    (h : MinimalObstruction c k t S) (A B A₀ B₀ : Finset V)
    (disj : Disjoint A B) (cover : A ∪ B = S)
    (hA : A.card = a*r+u) (hB : B.card = b*r+v) (huv : u+v = r+1)
    (hA₀ : A₀ ⊆ A) (hB₀ : B₀ ⊆ B) (hdelA : A₀.card < u) (hdelB : B₀.card < v) :
    ∃ x ∈ A \ A₀, ∃ y ∈ B \ B₀, (colorGraph c k).Adj x y := by
  have ht : (a+b+1)*r = t*r := by
    have hc := congrArg Finset.card cover
    rw [card_union_of_disjoint disj, h.card_eq, hA, hB] at hc
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
    omega
  have hab := Nat.eq_of_mul_eq_mul_right (show 0 < r by omega) ht
  have pick {X D : Finset V} {s z : ℕ} (hXS : X ⊆ S) (hDX : D ⊆ X)
      (hX : X.card = s*r+z) (hD : D.card < z) (hs : s < t) :
      ∃ I ⊆ X \ D, (colorGraph c k).IsNIndepSet (s+1) I := by
    have hc : s*r+1 ≤ (X \ D).card := by rw [card_sdiff_of_subset hDX, hX]; omega
    obtain ⟨W, hWX, hw⟩ := exists_subset_card_eq hc
    obtain ⟨I, hIW, hI⟩ := h.smaller s hs W (hWX.trans (sdiff_subset.trans hXS)) hw
    exact ⟨I, hIW.trans hWX, hI⟩
  have hAS : A ⊆ S := cover ▸ subset_union_left
  have hBS : B ⊆ S := cover ▸ subset_union_right
  obtain ⟨I, hIA, hI⟩ := pick hAS hA₀ hA hdelA (by omega)
  obtain ⟨J, hJB, hJ⟩ := pick hBS hB₀ hB hdelB (by omega)
  by_contra! hn
  have hIJ := disj.mono (hIA.trans sdiff_subset) (hJB.trans sdiff_subset)
  apply h.free (I ∪ J)
    (union_subset (hIA.trans (sdiff_subset.trans hAS)) (hJB.trans (sdiff_subset.trans hBS)))
  refine ⟨?_, by rw [card_union_of_disjoint hIJ, hI.card_eq, hJ.card_eq]; omega⟩
  intro x hx y hy hxy e
  rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
  · exact hI.isIndepSet hx hy hxy e
  · exact hn x (hIA hx) y (hJB hy) e
  · exact hn y (hIA hy) x (hJB hx) e.symm
  · exact hJ.isIndepSet hx hy hxy e

end Erdos617
