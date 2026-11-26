module

public import Wall133.FirstBands
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace Wall133

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] [DecidableEq V] in
/-- If all cycles are triangles, each non-tree edge closes a two-edge path
in every spanning tree. -/
private lemma exists_tree_neighbor (hcyc : ∀ {u} (p : G.Walk u u), p.IsCycle → p.length ≤ 3)
    {T : SimpleGraph V} (hT : T.IsTree) (hTG : T ≤ G) {v w : V} (hvw : G.Adj v w) :
    ∃ u, T.Adj v u ∧ (w = u ∨ T.Adj w u) := by
  by_cases ht : T.Adj v w
  · exact ⟨w, ht, Or.inl rfl⟩
  obtain ⟨p, hp, hd⟩ := hT.connected.exists_path_of_dist v w
  let q := p.mapLe hTG
  have hc : (Walk.cons hvw.symm q).IsCycle := by
    apply (Walk.cons_isCycle_iff _ _).2
    refine ⟨(Walk.isPath_mapLe _).2 hp, ?_⟩
    simpa [q] using fun h => ht (p.adj_of_mem_edges h).symm
  have hlen := hcyc _ hc
  have htwo : p.length = 2 := by
    have hle : p.length + 1 ≤ 3 := by simpa [q] using hlen
    have hp0 : 0 < p.length := by rw [hd]; exact Nat.pos_of_ne_zero fun h => hvw.ne (hT.connected.dist_eq_zero_iff.mp h)
    have hn1 : p.length ≠ 1 := fun h => ht (dist_eq_one_iff_adj.mp (hd ▸ h))
    omega
  refine ⟨p.getVert 1, ?_, Or.inr ?_⟩
  · simpa using p.adj_getVert_succ (i := 0) (by omega)
  · have h := (p.adj_getVert_succ (i := 1) (by omega)).symm
    simpa only [show 1+1 = p.length by omega, Walk.getVert_length] using h

/-- If every cycle is a triangle, the number of independent neighbors of `v`
is bounded by its degree in an arbitrary spanning tree. -/
private lemma local_le_tree_degree (h4 : NoFourCycle G)
    (hcyc : ∀ {u} (p : G.Walk u u), p.IsCycle → p.length ≤ 3)
    {T : SimpleGraph V} (hT : T.IsTree) (hTG : T ≤ G) [DecidableRel T.Adj] (v : V) :
    G.indepNeighborsCard v ≤ T.degree v := by
  classical
  obtain ⟨s, hs⟩ := exists_isNIndepSet_indepNum (G := G.induce (G.neighborSet v))
  change (G.induce (G.neighborSet v)).indepNum ≤ _
  rw [← hs.card_eq, ← T.card_neighborSet_eq_degree, ← Fintype.card_coe]
  have hstep (x : s) := exists_tree_neighbor hcyc hT hTG x.1.2
  choose f hf hxf using hstep
  apply Fintype.card_le_of_injective (fun x : s => (⟨f x, hf x⟩ : T.neighborSet v))
  intro x y h
  have heq : f x = f y := congrArg Subtype.val h
  by_contra hne
  have hval : x.1 ≠ y.1 := fun h => hne (Subtype.ext h)
  have hind : ¬G.Adj x.1.1 y.1.1 := hs.isIndepSet x.2 y.2 hval
  rcases hxf x with hx | hx <;> rcases hxf y with hy | hy
  · exact hval (Subtype.ext (hx.trans (heq.trans hy.symm)))
  · exact hind (by rw [hx, heq]; exact hTG hy.symm)
  · exact hind (by rw [hy, ← heq]; exact hTG hx)
  · have hy' : G.Adj (f x) y.1.1 := heq ▸ hTG hy.symm
    exact hval (Subtype.ext (h4 (hTG (hf x)).ne x.1.2 (hTG hx.symm) y.1.2 hy'))

/-- A connected graph all of whose cycles are triangles has neighborhood
independence average strictly below two. -/
theorem l_lt_two_of_cycles_triangles [Nonempty V] (hconn : G.Connected) (h4 : NoFourCycle G)
    (hcyc : ∀ {u} (p : G.Walk u u), p.IsCycle → p.length ≤ 3) : l G < 2 := by
  classical
  obtain ⟨T, hTG, hT⟩ := hconn.exists_isTree_le
  have hsum : (∑ v : V, G.indepNeighborsCard v) ≤ 2 * T.edgeFinset.card := by
    rw [← T.sum_degrees_eq_twice_card_edges]
    exact Finset.sum_le_sum fun v _ => local_le_tree_degree h4 hcyc hT hTG v
  unfold l averageIndepNeighbors indepNeighbors
  apply (div_lt_iff₀ (by exact_mod_cast Fintype.card_pos : 0 < (Fintype.card V : ℝ))).2
  rw [← Nat.cast_sum]
  exact_mod_cast (show ∑ v : V, G.indepNeighborsCard v < 2 * Fintype.card V by
    have := hT.card_edgeFinset
    omega)

end Wall133
