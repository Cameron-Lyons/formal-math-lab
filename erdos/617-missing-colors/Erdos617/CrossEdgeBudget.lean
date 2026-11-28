module

public import Erdos617.RankEdges
public import Erdos617.ColorCounts

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

private theorem clique_tangent (r b : ℕ) (hb : b ≤ r) :
    2*r*b ≤ 2*(b.choose 2) + r^2 + b := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hb
  nlinarith only [twice_choose_two b, Nat.zero_le (u*u)]

/-- All edges crossing between almost-covering cliques belong to a set of size
at most 5rq if at most 3q vertices are uncovered and q is at least t². -/
theorem cross_edge_budget {V ι : Type*} [DecidableEq V] [Fintype ι]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (B : ι → Finset V)
    {r t q : ℕ} (ht : Fintype.card ι = t) (hd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hsub : ∀ i, B i ⊆ S) (hc : ∀ i, G.IsClique (B i : Set V))
    (hsize : ∀ i, (B i).card ≤ r) (hX : (S \ univ.biUnion B).card ≤ 3*q)
    (he : 2*blockEdges G S ≤ r*S.card+r*t^2) (hS : S.card = t*r+1)
    (htpos : 0 < t) (hq : t^2 ≤ q) :
    ∃ F : Finset (Sym2 V), F.card ≤ 5*r*q ∧
      ∀ i j, i ≠ j → ∀ x ∈ B i, ∀ y ∈ B j, G.Adj x y → s(x,y) ∈ F := by
  classical
  let internal (i : ι) := inducedEdgeSet G (B i)
  let allInternal := univ.biUnion internal
  let F := inducedEdgeSet G S \ allInternal
  have edis : (Set.univ : Set ι).PairwiseDisjoint internal := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro e hei hej
    induction e using Sym2.inductionOn with
    | _ x y =>
      exact disjoint_left.mp (hd hij) ((mem_inducedEdgeSet G).mp hei).1
        ((mem_inducedEdgeSet G).mp hej).1
  have sub : allInternal ⊆ inducedEdgeSet G S := by
    intro e he
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp he
    induction e using Sym2.inductionOn with
    | _ x y =>
      obtain ⟨hx, hy, hxy⟩ := (mem_inducedEdgeSet G).mp hi
      exact (mem_inducedEdgeSet G).mpr ⟨hsub i hx, hsub i hy, hxy⟩
  have count : F.card + ∑ i, (B i).card.choose 2 = blockEdges G S := by
    have internal_card (i : ι) : (internal i).card = (B i).card.choose 2 := by
      change (inducedEdgeSet G (B i)).card = (B i).card.choose 2
      rw [card_inducedEdgeSet, blockEdges]
      have hi := G.induce_eq_top.mpr (hc i)
      have heq : (G.induce (B i : Set V)).edgeFinset = (⊤ : SimpleGraph (B i)).edgeFinset := by
        ext e
        simp only [mem_edgeFinset, hi]
        rfl
      rw [heq, card_edgeFinset_top_eq_card_choose_two, Fintype.card_coe]
    have h := card_sdiff_add_card_eq_card sub
    change F.card + (univ.biUnion internal).card = (inducedEdgeSet G S).card at h
    rw [card_biUnion (show (↑(univ : Finset ι) : Set ι).PairwiseDisjoint internal by simpa using edis),
      card_inducedEdgeSet] at h
    simpa only [internal_card] using h
  have bdis : (↑(univ : Finset ι) : Set ι).PairwiseDisjoint B :=
    fun _ _ _ _ hij => hd hij
  have cover := card_sdiff_add_card_eq_card (s := univ.biUnion B) (t := S)
    (biUnion_subset.mpr (fun i _ => hsub i))
  rw [card_biUnion bdis, hS] at cover
  have tangent := sum_le_sum (s := univ) (fun i _ => clique_tangent r (B i).card (hsize i))
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, ht, nsmul_eq_mul, Nat.cast_id] at tangent
  have sizes : (∑ i, (B i).card) ≤ t*r := by simpa [ht] using sum_le_sum (s := univ) fun i _ => hsize i
  have hmiss := Nat.mul_le_mul_left (2*r) hX
  have hcover := congrArg (fun z => (2*r)*z) cover
  have hrq := Nat.mul_le_mul_left r hq
  have hrt := Nat.mul_le_mul_left r (show t ≤ q from
    (show t ≤ t^2 by simpa [pow_two] using Nat.mul_le_mul_left t htpos).trans hq)
  rw [hS] at he
  refine ⟨F, ?_, ?_⟩
  · nlinarith only [count, he, tangent, sizes, hmiss, hcover, hrq, hrt]
  · intro i j hij x hx y hy hxy
    refine mem_sdiff.mpr ⟨(mem_inducedEdgeSet G).mpr ⟨hsub i hx, hsub j hy, hxy⟩, ?_⟩
    intro hmem
    obtain ⟨a, _, ha⟩ := mem_biUnion.mp hmem
    obtain ⟨hxa, hya, _⟩ := (mem_inducedEdgeSet G).mp ha
    by_cases heq : i = a
    · subst a
      exact disjoint_left.mp (hd hij) hya hy
    · exact disjoint_left.mp (hd heq) hx hxa

end Erdos617
