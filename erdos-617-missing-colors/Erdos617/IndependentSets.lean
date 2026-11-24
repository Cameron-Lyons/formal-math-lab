import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Erdos617

open SimpleGraph Finset

theorem independent_insert_of_nonadjacent {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {S : Finset V} (hS : G.IsIndepSet S) (v : V) (h : ∀ w ∈ S, ¬ G.Adj v w) :
    G.IsIndepSet (insert v S : Finset V) := by
  rw [Finset.coe_insert]
  exact hS.insert fun w hw _ ↦ ⟨h w hw, fun e ↦ h w hw e.symm⟩

/-- Private neighbors of a vertex of a maximum independent set, together with the vertex,
form a clique. Otherwise two private neighbors can replace it in the independent set. -/
theorem private_clique {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (I : Finset V) (hI : G.IsMaximumIndepSet I)
    (i : V) (hi : i ∈ I) :
    G.IsClique (insert i (Iᶜ.filter fun x ↦ I.filter (G.Adj x) = {i}) : Finset V) := by
  let P := Iᶜ.filter fun x ↦ I.filter (G.Adj x) = {i}
  have hxdata {x : V} (hx : x ∈ P) :
      x ∉ I ∧ G.Adj x i ∧ ∀ w ∈ I.erase i, ¬ G.Adj x w := by
    obtain ⟨hxo, hsingle⟩ := mem_filter.mp hx
    have hadj : i ∈ I.filter (G.Adj x) := hsingle ▸ mem_singleton_self _
    refine ⟨mem_compl.mp hxo, (mem_filter.mp hadj).2, fun w hw e ↦ ?_⟩
    obtain ⟨hwi, hwI⟩ := mem_erase.mp hw
    have : w ∈ I.filter (G.Adj x) := mem_filter.mpr ⟨hwI, e⟩
    exact hwi (mem_singleton.mp (hsingle ▸ this))
  change G.IsClique ((insert i P : Finset V) : Set V)
  rw [coe_insert]
  refine IsClique.insert ?_ fun x hx _ ↦ (hxdata hx).2.1.symm
  intro x hx y hy hxy
  by_contra hn
  obtain ⟨hxI, _, hxrest⟩ := hxdata hx
  obtain ⟨hyI, _, hyrest⟩ := hxdata hy
  have hbase : G.IsIndepSet (I.erase i) := hI.isIndepSet.mono (erase_subset i I)
  have hxind := independent_insert_of_nonadjacent G hbase x hxrest
  have hyind := independent_insert_of_nonadjacent G hxind y (by
    intro w hw
    rcases mem_insert.mp hw with rfl | hw
    · exact fun e ↦ hn e.symm
    · exact hyrest w hw)
  have hsize := hI.maximum _ hyind
  have hxe : x ∉ I.erase i := fun h ↦ hxI (mem_of_mem_erase h)
  have hye : y ∉ insert x (I.erase i) := by
    simp only [mem_insert, not_or]
    exact ⟨hxy.symm, fun h ↦ hyI (mem_of_mem_erase h)⟩
  rw [card_insert_of_notMem hye, card_insert_of_notMem hxe, card_erase_of_mem hi] at hsize
  have : 0 < I.card := card_pos.mpr ⟨i, hi⟩
  omega

/-- If one maximum independent set has total degree excess below r, then
fewer than 2r−2 excess incidences in the whole graph force an r-clique. -/
theorem clique_of_small_independent_excess (r t : ℕ) (hr : 3 ≤ r)
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = t * r + 1) (hT : (∑ v, (G.degree v - r)) < 2*r-2)
    (hi : G.IndepSetFree (t + 1))
    (hcheap : ∃ I, G.IsMaximumIndepSet I ∧ (∑ v ∈ I, (G.degree v - r)) < r) :
    ∃ S, G.IsNClique r S := by
  classical
  by_contra hcl
  let d (v : V) := G.degree v - r
  let F := univ.filter (fun S : Finset V ↦ G.IsMaximumIndepSet S)
  obtain ⟨I₀, hI₀, hcost⟩ := hcheap
  have hF : F.Nonempty := ⟨I₀, mem_filter.mpr ⟨mem_univ _, hI₀⟩⟩
  obtain ⟨I, hiF, hmin⟩ := F.exists_min_image (fun S ↦ ∑ v ∈ S, d v) hF
  have hI : G.IsMaximumIndepSet I := (mem_filter.mp hiF).2
  have hIr : I.card ≤ t := by
    by_contra! h
    obtain ⟨S, hSI, hS⟩ := exists_subset_card_eq h
    exact hi S ⟨hI.isIndepSet.mono hSI, hS⟩
  let N (x : V) := I.filter (G.Adj x)
  let P (i : V) := Iᶜ.filter (fun x ↦ N x = {i})
  have hpriv (i : V) (h : i ∈ I) : (P i).card ≤ r - 2 := by
    have hnot : i ∉ P i := by simp [P, h]
    have hcard : (insert i (P i)).card < r := by
      by_contra! hle
      obtain ⟨S, hS, hSr⟩ := exists_subset_card_eq hle
      exact hcl ⟨S, (private_clique G I hI i h).subset hS, hSr⟩
    rw [card_insert_of_notMem hnot] at hcard
    omega
  have hdom (x : V) (hx : x ∈ Iᶜ) : 0 < (N x).card := by
    by_contra! hempty
    have hnone : ∀ i ∈ I, ¬ G.Adj x i := by
      intro i hI e
      have : (N x).Nonempty := ⟨i, mem_filter.mpr ⟨hI, e⟩⟩
      exact (not_lt_of_ge hempty) (card_pos.mpr this)
    have hb := hI.maximum _ (independent_insert_of_nonadjacent G hI.isIndepSet x hnone)
    rw [card_insert_of_notMem (mem_compl.mp hx)] at hb
    omega
  have hlower (x : V) (hx : x ∈ Iᶜ) :
      2 ≤ (N x).card + (I.filter (fun i ↦ N x = {i})).card := by
    have hpos := hdom x hx
    by_cases hs : (N x).card = 1
    · obtain ⟨i, hi'⟩ := card_eq_one.mp hs
      have hiN : i ∈ N x := hi' ▸ mem_singleton_self _
      have hpos' : (I.filter (fun i ↦ N x = {i})).Nonempty :=
        ⟨i, mem_filter.mpr ⟨(mem_filter.mp hiN).1, hi'⟩⟩
      have := card_pos.mpr hpos'
      omega
    · omega
  let x := ∑ i ∈ I, d i
  have hsplit : x + ∑ z ∈ Iᶜ, d z = ∑ v, (G.degree v - r) := I.sum_add_sum_compl d
  have hxlt : x < r :=
    (hmin I₀ (mem_filter.mpr ⟨mem_univ _, hI₀⟩)).trans_lt hcost
  have hinc (i : V) : (Iᶜ.filter fun z ↦ G.Adj z i).card ≤ r + d i := by
    apply le_trans _ (show G.degree i ≤ r + d i by dsimp [d]; omega)
    apply card_le_card
    exact fun z hz ↦ (G.mem_neighborFinset i z).mpr (mem_filter.mp hz).2.symm
  have he : (∑ z ∈ Iᶜ, (N z).card) ≤ I.card * r + x := by
    rw [show (∑ z ∈ Iᶜ, (N z).card) = ∑ i ∈ I, (Iᶜ.filter fun z ↦ G.Adj z i).card from
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj]
    simpa [sum_add_distrib, x] using sum_le_sum (s := I) (fun i _ ↦ hinc i)
  have hl := sum_le_sum (s := Iᶜ) hlower
  simp only [sum_const, nsmul_eq_mul, sum_add_distrib] at hl
  rw [show (∑ z ∈ Iᶜ, (I.filter fun i ↦ N z = {i}).card) = ∑ i ∈ I, (P i).card from
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun z i ↦ N z = {i})] at hl
  have huniv := card_add_card_compl I
  rw [hV] at huniv
  have hsub : r - 2 + 2 = r := by omega
  have hlarge : I.card * (r - 2) + 2 ≤ x + ∑ i ∈ I, (P i).card := by
    nlinarith only [hl, he, huniv, Nat.mul_le_mul_right r hIr,
      congrArg (fun n ↦ I.card * n) hsub]
  have hp : (∑ i ∈ I, (P i).card) ≤ I.card * (r - 2) := by
    simpa using sum_le_sum (s := I) hpriv
  have hxpos : 2 ≤ x := by omega
  have hplow (i : V) (h : i ∈ I) : r - x ≤ (P i).card := by
    have hrest : (∑ a ∈ I.erase i, (P a).card) ≤ (I.erase i).card * (r - 2) := by
      simpa using sum_le_sum (s := I.erase i) (fun a ha ↦ hpriv a (mem_of_mem_erase ha))
    have hs := sum_erase_add I (fun a ↦ (P a).card) h
    have hc := card_erase_add_one h
    have hm := congrArg (fun n ↦ n * (r - 2)) hc
    nlinarith only [hrest, hlarge, hs, hm, hsub, Nat.sub_add_cancel (le_of_lt hxlt)]
  -- Exchanging the anchor for a private neighbor preserves the cardinality of I.
  have hswap (i : V) (hiI : i ∈ I) (z : V) (hz : z ∈ P i) : d i ≤ d z := by
    obtain ⟨hout, hsingle⟩ := mem_filter.mp hz
    have hzI := mem_compl.mp hout
    have hzE : z ∉ I.erase i := fun h ↦ hzI (mem_of_mem_erase h)
    have hbase : G.IsIndepSet (I.erase i) := hI.isIndepSet.mono (erase_subset i I)
    let J := insert z (I.erase i)
    have hJ : G.IsIndepSet J := independent_insert_of_nonadjacent G hbase z (by
      intro w hw e
      have hwN : w ∈ N z := mem_filter.mpr ⟨mem_of_mem_erase hw, e⟩
      exact (mem_erase.mp hw).1 (mem_singleton.mp (hsingle ▸ hwN)))
    have hsize : J.card = I.card := by
      rw [show J = insert z (I.erase i) by rfl, card_insert_of_notMem hzE, card_erase_add_one hiI]
    have hmaxJ : G.IsMaximumIndepSet J :=
      ⟨hJ, fun T hT' ↦ hsize ▸ hI.maximum T hT'⟩
    have hm := hmin J (mem_filter.mpr ⟨mem_univ _, hmaxJ⟩)
    change (∑ i ∈ I, d i) ≤ ∑ v ∈ insert z (I.erase i), d v at hm
    rw [sum_insert hzE] at hm
    have hs := sum_erase_add I d hiI
    omega
  have hblock (i : V) (h : i ∈ I) :
      (r-x) * d i ≤ ∑ z ∈ P i, d z := by
    calc
      _ ≤ (P i).card * d i := Nat.mul_le_mul_right _ (hplow i h)
      _ ≤ _ := by simpa using sum_le_sum (s := P i) (hswap i h)
  have hdisj : (↑I : Set V).PairwiseDisjoint P := by
    intro i hiI j hjI hij
    apply Finset.disjoint_left.mpr
    intro z hiz hjz
    have hsing : ({i} : Finset V) = {j} :=
      (mem_filter.mp hiz).2.symm.trans (mem_filter.mp hjz).2
    exact hij (singleton_injective hsing)
  have hu : I.biUnion P ⊆ Iᶜ := by
    intro z hz
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp hz
    exact (mem_filter.mp hi).1
  have hpacked := sum_le_sum (s := I) hblock
  rw [← Finset.mul_sum, ← sum_biUnion hdisj] at hpacked
  change (r - x) * x ≤ ∑ z ∈ I.biUnion P, d z at hpacked
  have hrest : (∑ z ∈ I.biUnion P, d z) ≤ ∑ z ∈ Iᶜ, d z :=
    sum_le_sum_of_subset_of_nonneg hu (fun _ _ _ ↦ Nat.zero_le _)
  have hmul : 2*r-2 ≤ x + (r-x)*x := by
    obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le hxpos
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hxlt)
    have : r-x = 1+b := by omega
    rw [this]
    nlinarith only [ha, hb, Nat.zero_le (a*b), Nat.sub_add_cancel (show 2 ≤ 2*r by omega)]
  omega

/-- If fewer than r incidences exceed the per-vertex degree allowance r, a
graph on tr+1 vertices with independence number at most t contains an r-clique. -/
theorem clique_of_total_excess_lt (r t : ℕ) (hr : 3 ≤ r)
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = t * r + 1) (hT : (∑ v, (G.degree v - r)) < r)
    (hi : G.IndepSetFree (t + 1)) : ∃ S, G.IsNClique r S := by
  apply clique_of_small_independent_excess r t hr G hV (by omega) hi
  obtain ⟨I, hI⟩ := G.maximumIndepSet_exists
  exact ⟨I, hI, (Finset.sum_le_sum_of_subset (I.subset_univ)).trans_lt hT⟩

theorem clique_of_degree_le_of_indepSetFree (r t : ℕ) (hr : 3 ≤ r)
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = t * r + 1) (hd : ∀ v, G.degree v ≤ r)
    (hi : G.IndepSetFree (t + 1)) : ∃ S, G.IsNClique r S := by
  apply clique_of_total_excess_lt r t hr G hV _ hi
  simpa [fun v => Nat.sub_eq_zero_of_le (hd v)] using (show 0 < r by omega)

/-- Each outside vertex blocks at most one member of C. Fewer than |C| outside
vertices therefore leave a free member that can be added to an independent set. -/
theorem extend_across_clique_within {V : Type*} [DecidableEq V] (G : SimpleGraph V) {r t : ℕ}
    (C J : Finset V) (hC : G.IsNClique r C) (hJ : G.IsNIndepSet t J)
    (disj : Disjoint C J) (ht : t < r)
    (hout : ∀ x ∉ C, ∀ y ∈ C, ∀ z ∈ C, G.Adj x y → G.Adj x z → y = z) :
    ∃ S ⊆ C ∪ J, G.IsNIndepSet (t+1) S := by
  classical
  have hfree : ∃ v ∈ C, ∀ w ∈ J, ¬ G.Adj w v := by
    by_contra! h
    have hhit (v : C) : ∃ w : J, G.Adj w.val v.val := by
      obtain ⟨w, hw, he⟩ := h v v.property
      exact ⟨⟨w, hw⟩, he⟩
    choose f hf using hhit
    have hinj : Function.Injective f := by
      intro a b he
      have hfa : (f a).val ∉ C := fun hc => Finset.disjoint_left.mp disj hc (f a).property
      exact Subtype.ext (hout _ hfa a a.property b b.property (hf a) (he ▸ hf b))
    have hcount := Fintype.card_le_of_injective f hinj
    simp only [Fintype.card_coe, hC.card_eq, hJ.card_eq] at hcount
    omega
  obtain ⟨v, hv, hfree⟩ := hfree
  have hvJ : v ∉ J := Finset.disjoint_left.mp disj hv
  refine ⟨insert v J, insert_subset (mem_union_left _ hv) subset_union_right, ?_,
    by rw [Finset.card_insert_of_notMem hvJ, hJ.card_eq]⟩
  rw [Finset.coe_insert]
  exact hJ.isIndepSet.insert fun w hw _ => ⟨fun e => hfree w hw e.symm, hfree w hw⟩

theorem extend_across_clique {V : Type*} (G : SimpleGraph V) {r t : ℕ}
    (C J : Finset V) (hC : G.IsNClique r C) (hJ : G.IsNIndepSet t J)
    (disj : Disjoint C J) (ht : t < r)
    (hout : ∀ x ∉ C, ∀ y ∈ C, ∀ z ∈ C, G.Adj x y → G.Adj x z → y = z) :
    ∃ S, G.IsNIndepSet (t+1) S := by
  classical
  obtain ⟨S, _, hS⟩ := extend_across_clique_within G C J hC hJ disj ht hout
  exact ⟨S, hS⟩

end Erdos617
