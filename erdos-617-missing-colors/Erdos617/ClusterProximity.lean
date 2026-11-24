import Erdos617.MinimalObstruction
import Erdos617.SparseTransversal
import Mathlib.Data.Nat.Sqrt

namespace Erdos617

open Finset SimpleGraph

/-- Every outside vertex misses only a few vertices of at least one block.
Otherwise its nonneighbors admit an independent transversal, which extends
to a forbidden independent set by adding the outside vertex. -/
theorem MinimalObstruction.exists_close_block {V ι : Type*} [DecidableEq V] [Fintype ι]
    {r t : ℕ} {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V}
    (h : MinimalObstruction c k t S) (B : ι → Finset V) (ht : Fintype.card ι = t)
    (hd : Pairwise (fun i j => Disjoint (B i) (B j))) (hBS : ∀ i, B i ⊆ S)
    (F : Finset (Sym2 V))
    (hf : ∀ i j, i ≠ j → ∀ u ∈ B i, ∀ v ∈ B j, (colorGraph c k).Adj u v → s(u,v) ∈ F)
    {x : V} (hx : x ∈ S \ univ.biUnion B) :
    ∃ i, ((B i).filter (fun y => ¬(colorGraph c k).Adj x y)).card ≤ Nat.sqrt F.card := by
  classical
  let G := colorGraph c k
  let N (i : ι) := (B i).filter (fun y => ¬G.Adj x y)
  by_contra! hlarge
  have hdis : Pairwise (fun i j => Disjoint (N i) (N j)) :=
    fun i j hne => (hd hne).mono (filter_subset ..) (filter_subset ..)
  obtain ⟨f, hmem, hfree⟩ := sparse_independent_transversal G N hdis F
    (Nat.succ_pos _) (fun i => Nat.succ_le_of_lt (hlarge i))
    (fun i j hij u hu v hv => hf i j hij u (mem_filter.mp hu).1 v (mem_filter.mp hv).1)
    (Nat.lt_succ_sqrt' F.card)
  let I := univ.image f
  have inj : Function.Injective f := by
    intro i j he
    by_contra hn
    exact disjoint_left.mp (hdis hn) (hmem i) (he ▸ hmem j)
  have hIS : I ⊆ S := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := mem_image.mp hy
    exact hBS i (mem_filter.mp (hmem i)).1
  have hi : G.IsIndepSet (I : Set V) := by
    intro u hu v hv huv hadj
    obtain ⟨i, _, rfl⟩ := mem_image.mp hu
    obtain ⟨j, _, rfl⟩ := mem_image.mp hv
    exact hfree i j (fun h => huv (congrArg f h)) hadj
  have hxi : x ∉ I := by
    intro hxI
    obtain ⟨i, _, he⟩ := mem_image.mp hxI
    exact (mem_sdiff.mp hx).2 (mem_biUnion.mpr ⟨i, mem_univ i, he ▸ (mem_filter.mp (hmem i)).1⟩)
  apply h.free (insert x I) (insert_subset (mem_sdiff.mp hx).1 hIS)
  refine ⟨independent_insert_of_nonadjacent G hi x ?_, ?_⟩
  · intro y hy
    obtain ⟨i, _, rfl⟩ := mem_image.mp hy
    exact (mem_filter.mp (hmem i)).2
  · rw [card_insert_of_notMem hxi, show I.card = t by simp [I, card_image_of_injective _ inj, ht]]

end Erdos617
