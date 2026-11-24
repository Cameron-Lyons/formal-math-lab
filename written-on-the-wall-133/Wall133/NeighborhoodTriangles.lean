import Wall133.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! # Independence inside a four-cycle-free neighborhood -/
namespace Wall133
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/-- In a four-cycle-free graph, two edges inside the neighborhood of a
fixed vertex cannot share an endpoint unless they are the same edge. -/
theorem neighborhood_adj_unique (h4 : NoFourCycle G) (v : V)
    {x y z : G.neighborSet v}
    (hxy : (G.induce (G.neighborSet v)).Adj x y)
    (hxz : (G.induce (G.neighborSet v)).Adj x z) : y = z :=
  Subtype.ext (h4 (x := v) (y := x.val) x.property.ne y.property hxy z.property hxz)

/-- For disjoint edges and isolated vertices, a maximum independent set
omits exactly one vertex per edge. -/
theorem indepNum_add_edge_card_of_adj_unique [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (huniq : ∀ {x y z : V}, G.Adj x y → G.Adj x z → y = z) :
    G.indepNum + G.edgeFinset.card = Fintype.card V := by
  classical
  obtain ⟨I,hI⟩ := exists_isNIndepSet_indepNum (G := G)
  have dominated {x : V} (hx : x ∉ I) : ∃ y ∈ I, G.Adj x y := by
    by_contra! h
    have hind : G.IsIndepSet (↑(insert x I : Finset V) : Set V) := by
      intro a ha b hb hne hab
      rcases Finset.mem_insert.mp ha with hax | haI
      · rcases Finset.mem_insert.mp hb with hbx | hbI
        · exact hne (hax.trans hbx.symm)
        · exact h b hbI (hax ▸ hab)
      · rcases Finset.mem_insert.mp hb with hbx | hbI
        · exact h a haI (hbx ▸ hab.symm)
        · exact hI.isIndepSet haI hbI hne hab
    have hh := hind.card_le_indepNum
    rw [Finset.card_insert_of_notMem hx, hI.card_eq] at hh
    omega
  have part : G.IsBipartiteWith (↑(Iᶜ : Finset V) : Set V) (↑I : Set V) := by
    constructor
    · apply Set.disjoint_left.mpr
      intro x hx hy
      exact (Finset.mem_compl.mp hx) hy
    · intro x y hxy
      by_cases hx : x ∈ I
      · exact Or.inr ⟨hx, Finset.mem_compl.mpr (fun hy => hI.isIndepSet hx hy hxy.ne hxy)⟩
      · obtain ⟨z,hz,hxz⟩ := dominated hx
        exact Or.inl ⟨Finset.mem_compl.mpr hx, huniq hxy hxz ▸ hz⟩
  have edges := isBipartiteWith_sum_degrees_eq_card_edges part
  have one (x : V) (hx : x ∈ Iᶜ) : G.degree x = 1 := by
    obtain ⟨y,_,hy⟩ := dominated (Finset.mem_compl.mp hx)
    exact degree_eq_one_iff_existsUnique_adj.mpr ⟨y,hy,fun z hz => huniq hz hy⟩
  have hcount : G.edgeFinset.card = (Iᶜ : Finset V).card := by
    calc
      _ = ∑ x ∈ Iᶜ, G.degree x := edges.symm
      _ = ∑ _x ∈ Iᶜ, 1 := Finset.sum_congr rfl one
      _ = _ := by simp
  rw [← hI.card_eq, hcount, Finset.card_compl]
  have := Finset.card_le_univ I
  omega

/-- The neighborhood independence number equals the degree minus the
number of triangles containing the vertex, counted by the edges between
its neighbors. -/
theorem indepNeighborsCard_eq_degree_sub_neighborhood_edges [Fintype V] [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (v : V) :
    G.indepNeighborsCard v = G.degree v - (G.induce (G.neighborSet v)).edgeFinset.card := by
  classical
  have h := indepNum_add_edge_card_of_adj_unique (G := G.induce (G.neighborSet v))
    (fun hxy hxz => neighborhood_adj_unique h4 v hxy hxz)
  rw [G.card_neighborSet_eq_degree] at h
  change (G.induce (G.neighborSet v)).indepNum = _
  omega

end Wall133
