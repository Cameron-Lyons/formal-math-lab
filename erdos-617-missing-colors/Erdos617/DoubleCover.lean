module

public import Erdos617.OddBags

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V ι : Type*} [DecidableEq V] [Fintype ι] [DecidableEq ι]

/-- A vertex in two covering cliques contributes twice to the total size and
once to the sum of overlaps of either clique with the others. -/
theorem double_cover_counts (S : Finset V) (B : ι → Finset V)
    (hsub : ∀ i, B i ⊆ S) (htwo : ∀ x ∈ S, (univ.filter fun i => x ∈ B i).card = 2) :
    (∑ i, (B i).card) = 2*S.card ∧
      ∀ i, (∑ j ∈ univ.erase i, (B i ∩ B j).card) = (B i).card := by
  classical
  constructor
  · have hc : (∑ i, (S.filter fun x => x ∈ B i).card) =
        ∑ x ∈ S, (univ.filter fun i => x ∈ B i).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun i x => x ∈ B i)
    have left (i : ι) : S.filter (fun x => x ∈ B i) = B i := by
      rw [filter_mem_eq_inter, inter_eq_right.mpr (hsub i)]
    simp only [left] at hc
    rw [sum_congr rfl htwo, sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm] at hc
    exact hc
  · intro i
    have hc : (∑ j ∈ univ.erase i, ((B i).filter fun x => x ∈ B j).card) =
        ∑ x ∈ B i, ((univ.erase i).filter fun j => x ∈ B j).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun j x => x ∈ B j)
    have one (x : V) (hx : x ∈ B i) : ((univ.erase i).filter fun j => x ∈ B j).card = 1 := by
      have hi : i ∈ univ.filter (fun j => x ∈ B j) := mem_filter.mpr ⟨mem_univ i,hx⟩
      rw [filter_erase, card_erase_of_mem hi, htwo x (hsub i hx)]
    simpa only [filter_mem_eq_inter, sum_congr rfl one, sum_const, nsmul_eq_mul,
      Nat.cast_id, Nat.mul_one] using hc

omit [Fintype ι] [DecidableEq ι] in
/-- In a twofold cover, t independent vertices use 2t different cliques. -/
private theorem double_cover_independent_bound (G : SimpleGraph V) (I : Finset V)
    (B : ι → Finset V) (K : Finset ι) (hcl : ∀ i, G.IsClique (B i : Set V))
    (hind : G.IsIndepSet (I : Set V))
    (htwo : ∀ x ∈ I, (K.filter fun i => x ∈ B i).card = 2) : 2*I.card ≤ K.card := by
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := I) (t := K) (fun x i => x ∈ B i)
  have hsum : (∑ x ∈ I, (K.filter fun i => x ∈ B i).card) =
      ∑ i ∈ K, (I.filter fun x => x ∈ B i).card := h
  have one (i : ι) (_ : i ∈ K) : (I.filter fun x => x ∈ B i).card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    obtain ⟨hxI,hxB⟩ := mem_filter.mp hx
    obtain ⟨hyI,hyB⟩ := mem_filter.mp hy
    by_contra hne
    exact hind hxI hyI hne (hcl i hxB hyB hne)
  have hs := sum_le_sum (s := K) one
  rw [← hsum, sum_congr rfl htwo] at hs
  simpa [Nat.mul_comm] using hs

/-- Algebraic constraints on the clique sizes and pair overlaps of a twofold
monochromatic cover by 2t+1 cliques. -/
theorem MinimalObstruction.double_cover_data {r t : ℕ} {S : Finset V}
    {c : Sym2 V → Fin r} {k : Fin r} (h : MinimalObstruction c k t S) (hb : Balanced c)
    (ht : 2 ≤ t) (htr : t < r) (B : ι → Finset V) (hcount : Fintype.card ι = 2*t+1)
    (hsub : ∀ i, B i ⊆ S) (hcl : ∀ i, (colorGraph c k).IsClique (B i : Set V))
    (htwo : ∀ x ∈ S, (univ.filter fun i => x ∈ B i).card = 2) :
    (∑ i, (B i).card) = 2*(t*r+1) ∧ (∀ i, (B i).card ≤ r-1) ∧
      (∀ i, (∑ j ∈ univ.erase i, (B i ∩ B j).card) = (B i).card) ∧
      ∀ i j, i ≠ j → r+1 ≤ (B i ∪ B j).card ∧
        (r-1)*((B i ∪ B j).card-r) ≤ (B i \ B j).card*(B j \ B i).card := by
  obtain ⟨hs,hrow⟩ := double_cover_counts S B hsub htwo
  refine ⟨h.card_eq ▸ hs,?_,hrow,?_⟩
  · intro i
    by_contra! hlarge
    obtain ⟨C,hC,hn⟩ := exists_subset_card_eq (s := B i) (show r ≤ (B i).card by omega)
    exact h.no_clique hb htr C (hC.trans (hsub i)) ⟨(hcl i).subset hC, hn⟩
  · intro i j hij
    have hbig : r+1 ≤ (B i ∪ B j).card := by
      by_contra! hsmall
      have hU : B i ∪ B j ⊆ S := union_subset (hsub i) (hsub j)
      have size : (t-1)*r+1 ≤ (S \ (B i ∪ B j)).card := by
        rw [card_sdiff_of_subset hU,h.card_eq]
        have mult := congrArg (·*r) (show t-1+1=t by omega)
        rw [Nat.add_mul,Nat.one_mul] at mult
        omega
      obtain ⟨W,hW,hn⟩ := exists_subset_card_eq size
      obtain ⟨I,hI,hind⟩ := h.smaller (t-1) (by omega) W (hW.trans sdiff_subset) hn
      have hcard : I.card=t := by rw [hind.card_eq]; omega
      let K := (univ.erase i).erase j
      have hK : K.card=2*t-1 := by simp [K,hij.symm,hcount]
      have two (x : V) (hx : x ∈ I) : (K.filter fun a => x ∈ B a).card=2 := by
        obtain ⟨hxS,hxU⟩ := mem_sdiff.mp (hW (hI hx))
        have hmem : K.filter (fun a => x ∈ B a) = univ.filter (fun a => x ∈ B a) := by
          ext a
          simp only [K, mem_filter, mem_erase, mem_univ, and_true, true_and, mem_union] at *
          grind
        rw [hmem,htwo x hxS]
      have hle := double_cover_independent_bound _ I B K hcl hind.isIndepSet two
      rw [hcard,hK] at hle
      omega
    refine ⟨hbig, ?_⟩
    have hp := foreign_pair_budget c hb k (B i ∪ B j) ((B i \ B j) ×ˢ (B j \ B i)) (by
      intro x hx y hy hxy hcol
      have h1 : ¬ (x ∈ B i ∧ y ∈ B i) := fun h => hcol (hcl i h.1 h.2 hxy).2
      have h2 : ¬ (x ∈ B j ∧ y ∈ B j) := fun h => hcol (hcl j h.1 h.2 hxy).2
      simp only [mem_union, mem_product, mem_sdiff] at *
      grind)
    rw [card_product] at hp
    have hsplit := congrArg ((r-1)*·) (Nat.sub_add_cancel (show r ≤ (B i ∪ B j).card by omega))
    rw [Nat.mul_add] at hsplit
    omega

end Erdos617
