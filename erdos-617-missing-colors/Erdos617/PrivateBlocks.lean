import Erdos617.CheapClique
import Erdos617.CrossEdgeBudget

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] {r t : ℕ} {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V}

/-- The closed neighborhoods of an independent set partition the vertices that
hit exactly one anchor into cliques. All remaining vertices hit at least two. -/
theorem MinimalObstruction.private_blocks_with_hits (h : MinimalObstruction c k t S)
    {I : Finset V} (hIS : I ⊆ S) (hi : (colorGraph c k).IsNIndepSet t I)
    {L : ℕ} (hcost : (∑ x ∈ I, (S.filter ((colorGraph c k).Adj x)).card) ≤ t*r+L) :
    ∃ (B : I → Finset V) (X : Finset V), Pairwise (fun a b => Disjoint (B a) (B b)) ∧
      (∀ a, B a ⊆ S ∧ (colorGraph c k).IsClique (B a : Set V)) ∧
      X = S \ univ.biUnion B ∧ X.card+1 ≤ L+t ∧
      ∀ a, B a = S.filter (fun x => I.filter (fun y => x = y ∨ (colorGraph c k).Adj x y) = {a.val}) := by
  classical
  let G := colorGraph c k
  change (∑ x ∈ I, (S.filter (G.Adj x)).card) ≤ t*r+L at hcost
  let hits (x y : V) := x = y ∨ G.Adj x y
  let N (x : V) := I.filter (hits x)
  let B (a : I) := S.filter (fun x => N x = {a.val})
  let U := univ.biUnion B
  let X := S \ U
  have dis : Pairwise (fun a b => Disjoint (B a) (B b)) := by
    intro a b hne
    exact Finset.disjoint_left.mpr fun _ hx hy =>
      hne (Subtype.ext (singleton_injective ((mem_filter.mp hx).2.symm.trans (mem_filter.mp hy).2)))
  have nohit {a : I} {x y : V} (hx : x ∈ B a) (hy : y ∈ I.erase a.val) : ¬ hits x y := by
    intro he
    have hn : y ∈ N x := mem_filter.mpr ⟨mem_of_mem_erase hy,he⟩
    exact (mem_erase.mp hy).1 (mem_singleton.mp ((mem_filter.mp hx).2 ▸ hn))
  have cl (a : I) : G.IsClique (B a : Set V) := by
    intro x hx y hy hxy
    by_contra hn
    let J := I.erase a.val
    have hxJ : x ∉ J := fun h => nohit hx h (Or.inl rfl)
    have hyJ : y ∉ insert x J := by
      intro h
      rcases mem_insert.mp h with eq | hj
      · exact hxy eq.symm
      · exact nohit hy hj (Or.inl rfl)
    have hJ := hi.isIndepSet.mono (erase_subset a.val I)
    have h1 := independent_insert_of_nonadjacent G hJ x (fun _ hz e => nohit hx hz (Or.inr e))
    have h2 := independent_insert_of_nonadjacent G h1 y (by
      intro z hz e
      rcases mem_insert.mp hz with rfl | hz
      · exact hn e.symm
      · exact nohit hy hz (Or.inr e))
    apply h.free (insert y (insert x J))
      (insert_subset (mem_filter.mp hy).1 (insert_subset (mem_filter.mp hx).1 ((erase_subset ..).trans hIS)))
    refine ⟨h2, ?_⟩
    rw [card_insert_of_notMem hyJ, card_insert_of_notMem hxJ,
      show J.card+1 = I.card from card_erase_add_one a.prop, hi.card_eq]
  have dom (x : V) (hx : x ∈ S) : 1 ≤ (N x).card := by
    by_contra! hn
    have he : ∀ y ∈ I, ¬ hits x y := by
      intro y hy e
      have := card_pos.mpr (show (N x).Nonempty from ⟨y, mem_filter.mpr ⟨hy,e⟩⟩)
      omega
    have hxI : x ∉ I := fun h => he x h (Or.inl rfl)
    exact h.free (insert x I) (insert_subset hx hIS)
      ⟨independent_insert_of_nonadjacent G hi.isIndepSet x (fun _ hy e => he _ hy (Or.inr e)),
        by rw [card_insert_of_notMem hxI, hi.card_eq]⟩
  have many (x : V) (hx : x ∈ X) : 2 ≤ (N x).card := by
    have hdom := dom x (mem_sdiff.mp hx).1
    by_contra! hn
    obtain ⟨a, ha⟩ := card_eq_one.mp (show (N x).card = 1 by omega)
    have haN : a ∈ N x := ha ▸ mem_singleton_self _
    let i : I := ⟨a,(mem_filter.mp haN).1⟩
    exact (mem_sdiff.mp hx).2 (mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨(mem_sdiff.mp hx).1,ha⟩⟩)
  have bound (a : V) (ha : a ∈ I) :
      (S.filter (fun x => hits x a)).card = (S.filter (G.Adj a)).card+1 := by
    have he : S.filter (fun x => hits x a) = insert a (S.filter (G.Adj a)) := by
      ext y
      simp only [mem_filter, mem_insert, hits]
      constructor
      · rintro ⟨hs,rfl | e⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hs,e.symm⟩
      · rintro (rfl | ⟨hs,e⟩)
        · exact ⟨hIS ha,Or.inl rfl⟩
        · exact ⟨hs,Or.inr e.symm⟩
    rw [he, card_insert_of_notMem (by simp)]
  have total : (∑ z ∈ S, (N z).card) ≤ t*r+L+t := calc
    _ = ∑ a ∈ I, (S.filter fun x => hits x a).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow hits
    _ = ∑ a ∈ I, ((S.filter (G.Adj a)).card+1) := sum_congr rfl bound
    _ ≤ _ := by simpa only [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one, Nat.cast_id, hi.card_eq] using Nat.add_le_add_right hcost t
  have hUS : U ⊆ S := biUnion_subset.mpr fun _ _ => filter_subset .. 
  have h1 := sum_le_sum (s := U) fun x hx => dom x (hUS hx)
  have h2 := sum_le_sum (s := X) many
  have hparts := sum_union (s₁ := U) (s₂ := X) (f := fun z => (N z).card) disjoint_sdiff
  rw [show U ∪ X = S from union_sdiff_of_subset hUS] at hparts
  have hc : X.card+U.card=S.card := card_sdiff_add_card_eq_card hUS
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,mul_one] at h1 h2
  refine ⟨B, X, dis, fun a => ⟨filter_subset ..,cl a⟩, rfl, ?_, fun _ => rfl⟩
  rw [h.card_eq] at hc
  omega

/-- Disjoint private cliques and the cardinality bound on their complement. -/
theorem MinimalObstruction.private_blocks (h : MinimalObstruction c k t S)
    {I : Finset V} (hIS : I ⊆ S) (hi : (colorGraph c k).IsNIndepSet t I)
    {L : ℕ} (hcost : (∑ x ∈ I, (S.filter ((colorGraph c k).Adj x)).card) ≤ t*r+L) :
    ∃ (B : I → Finset V) (X : Finset V), Pairwise (fun a b => Disjoint (B a) (B b)) ∧
      (∀ a, B a ⊆ S ∧ (colorGraph c k).IsClique (B a : Set V)) ∧
      X = S \ univ.biUnion B ∧ X.card+1 ≤ L+t := by
  obtain ⟨B,X,hd,hB,hX,hs,_⟩ := h.private_blocks_with_hits hIS hi hcost
  exact ⟨B,X,hd,hB,hX,hs⟩

/-- A cheap independent set supplies disjoint cliques covering almost the
entire obstruction, with a common bound on the edges crossing between them. -/
theorem MinimalObstruction.exists_sparse_clique_cover (h : MinimalObstruction c k t S)
    (hr : 3 ≤ r) (hb : Balanced c) (htr : t < r) (hscale : 2*t^2 ≤ r) :
    ∃ (I : Finset V) (B : I → Finset V), Fintype.card I = t ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧ (∀ i, B i ⊆ S) ∧
      (∀ i, (colorGraph c k).IsClique (B i : Set V)) ∧ (∀ i, (B i).card ≤ r) ∧
      (S \ univ.biUnion B).card ≤ 3*t^2 ∧
      ∃ F : Finset (Sym2 V), F.card ≤ 5*r*t^2 ∧
        ∀ i j, i ≠ j → ∀ x ∈ B i, ∀ y ∈ B j, (colorGraph c k).Adj x y → s(x,y) ∈ F := by
  classical
  have ht := h.pos
  obtain ⟨I, hIS, hi, hcost⟩ := h.exists_independent_degree_sum_le hr (h.two_le_parameter hr hb htr)
    htr hscale hb
  obtain ⟨B, X, hd, hB, hXeq, hX⟩ := h.private_blocks hIS hi hcost
  have hIt : Fintype.card I = t := (Fintype.card_coe I).trans hi.card_eq
  have hsub := fun i => (hB i).1
  have hcl := fun i => (hB i).2
  have hsize (i : I) : (B i).card ≤ r := by
    by_contra! hbig
    obtain ⟨C, hCB, hC⟩ := exists_subset_card_eq (Nat.le_of_lt hbig)
    exact h.no_clique hb htr C (hCB.trans (hsub i))
      ⟨fun _ hx _ hy hxy => hcl i (hCB hx) (hCB hy) hxy, hC⟩
  have h12 : t ≤ t^2 := by simpa [pow_two] using Nat.mul_le_mul_left t ht
  have hfew : (S \ univ.biUnion B).card ≤ 3*t^2 := by rw [← hXeq]; omega
  exact ⟨I, B, hIt, hd, hsub, hcl, hsize, hfew,
    cross_edge_budget (colorGraph c k) S B hIt hd hsub hcl hsize hfew
      (h.twice_edges_le (by omega) hb) h.card_eq ht (le_refl (t^2))⟩

end Erdos617
