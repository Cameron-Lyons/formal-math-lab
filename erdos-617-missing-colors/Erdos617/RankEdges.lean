module

public import Erdos617.BlockAccount

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- Graph edges with both endpoints in the given finite set, using the ambient vertex type. -/
def inducedEdgeSet (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset (Sym2 V) :=
  S.sym2.filter (· ∈ G.edgeSet)

omit [DecidableEq V] in
@[simp] theorem mem_inducedEdgeSet (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {x y : V} : s(x,y) ∈ inducedEdgeSet G S ↔ x ∈ S ∧ y ∈ S ∧ G.Adj x y := by
  simp [inducedEdgeSet, and_assoc]

omit [DecidableEq V] in
theorem card_inducedEdgeSet (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (inducedEdgeSet G S).card = blockEdges G S := by
  let H := G.induce (S : Set V)
  let f := Function.Embedding.subtype (· ∈ S)
  have he : H.edgeFinset.map f.sym2Map = inducedEdgeSet G S := by
    ext e
    induction e using Sym2.inductionOn with
    | _ a b =>
      constructor
      · intro h
        obtain ⟨z, hz, hmap⟩ := mem_map.mp h
        induction z using Sym2.inductionOn with
        | _ x y =>
          change s(x.val,y.val) = s(a,b) at hmap
          rw [← hmap]
          exact (mem_inducedEdgeSet G).mpr ⟨x.prop, y.prop, mem_edgeFinset.mp hz⟩
      · intro h
        obtain ⟨ha, hb, hab⟩ := (mem_inducedEdgeSet G).mp h
        exact mem_map.mpr ⟨s(⟨a,ha⟩, ⟨b,hb⟩), mem_edgeFinset.mpr hab, rfl⟩
  simpa [blockEdges, H] using (congrArg Finset.card he).symm

theorem boundary_edge_count (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (P : Finset (Finset V)) (hu : P.biUnion id ⊆ S)
    (hd : (↑P : Set (Finset V)).PairwiseDisjoint id) :
    (inducedEdgeSet G S \ P.biUnion (inducedEdgeSet G)).card +
      (∑ A ∈ P, blockEdges G A) = blockEdges G S := by
  have hsub : P.biUnion (inducedEdgeSet G) ⊆ inducedEdgeSet G S := by
    intro e he
    obtain ⟨A, hA, hea⟩ := mem_biUnion.mp he
    have hAS : A ⊆ S := fun _ hx => hu (mem_biUnion.mpr ⟨A,hA,hx⟩)
    induction e using Sym2.inductionOn with
    | _ x y =>
      obtain ⟨hx, hy, ha⟩ := (mem_inducedEdgeSet G).mp hea
      exact (mem_inducedEdgeSet G).mpr ⟨hAS hx, hAS hy, ha⟩
  have dis : (↑P : Set (Finset V)).PairwiseDisjoint (inducedEdgeSet G) := by
    intro A ha B hb hne
    apply Finset.disjoint_left.mpr
    intro e he hf
    induction e using Sym2.inductionOn with
    | _ x y =>
      exact Finset.disjoint_left.mp (hd ha hb hne) ((mem_inducedEdgeSet G).mp he).1
        ((mem_inducedEdgeSet G).mp hf).1
  have hE := Finset.card_sdiff_of_subset hsub
  have hle := Finset.card_le_card hsub
  rw [Finset.card_biUnion dis] at hE hle
  simp_rw [card_inducedEdgeSet] at hE hle
  omega

end Erdos617
