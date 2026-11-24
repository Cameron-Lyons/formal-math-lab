import Erdos617.BlockSizes
import Erdos617.GreedyBlocks

namespace Erdos617

open SimpleGraph Finset

/-- With independence number at most `a` and clique number at most `t`,
a graph on `t*a+1` vertices has at least `a * t.choose 2 + 2*t - 1` edges.
This special case of Brouwer's refinement of Turán's theorem is proved here
by minimum-degree elimination. See [Bougard and Joret, §5](https://gjoret.be/papers/turan.pdf). -/
theorem edge_bound_of_clique_and_indep_caps {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {a t : ℕ} (ht : 2 ≤ t)
    (hN : Fintype.card V = t*a+1) (hα : G.IndepSetFree (a+1)) (hω : G.CliqueFree (t+1)) :
    a*t.choose 2 + 2*t-1 ≤ G.edgeFinset.card := by
  by_contra! hsmall
  obtain ⟨bs, _, hvalid, hsize, hcost, _⟩ := exists_greedyBlocks G
  obtain ⟨I, _, hI⟩ := independent_pivots G bs hvalid
  have hlen : bs.length ≤ a := by
    by_contra! h
    obtain ⟨S, hSI, hS⟩ := exists_subset_card_eq (s := I)
      (show a+1 ≤ I.card by rw [hI.card_eq]; omega)
    exact hα S ⟨hI.isIndepSet.mono hSI, hS⟩
  let sizes := bs.map (fun b => b.vertices.card)
  obtain ⟨hfull, ⟨v, hv, hvbig⟩, hlarge⟩ := block_sizes_of_small_budget
    sizes a t (bs.map TransversalBlock.cost).sum ht (by simpa [sizes] using hlen)
    (by simpa [sizes, hN] using hsize)
    (by simpa [sizes, List.map_map, Function.comp_def, hcost] using hsmall)
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hv
  have hbad : ¬ G.IsClique (b.vertices : Set V) := by
    intro hc
    obtain ⟨S, hS, hcard⟩ := exists_subset_card_eq (s := b.vertices) hvbig
    exact hω S ⟨hc.subset hS, hcard⟩
  obtain ⟨J, _, hJ⟩ := larger_independent_of_nonclique_block G bs hvalid
    (fun c hc => hlarge _ (List.mem_map_of_mem hc)) ⟨b, hb, hbad⟩
  have heq : bs.length = a := by simpa [sizes] using hfull
  exact hα J (heq ▸ hJ)

end Erdos617
