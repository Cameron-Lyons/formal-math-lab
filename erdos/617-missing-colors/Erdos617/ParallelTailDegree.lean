module

public import Erdos617.ParallelRowGreedy

@[expose] public section

namespace Erdos617

open Finset SimpleGraph
open scoped Classical

/-- A vertex of the remainder either has at least r neighbors there or
belongs to an independent triple and has one neighbor on every full row. -/
theorem parallel_two_tail_degree {V : Type*} [DecidableEq V] {r : ℕ} {c : Sym2 V → Fin r}
    (hr : 11≤r) (hb : Balanced c) (k : Fin r) (R : Fin (r-2) → Finset V)
    (full : ∀ i,(colorGraph c k).IsNClique r (R i)) (dis : Pairwise fun i j => Disjoint (R i) (R j))
    (T : Finset V) (order : T.card=2*r+1) (apart : ∀ i,Disjoint T (R i)) (v : V) (hv : v∈T) :
    r≤(T.filter ((colorGraph c k).Adj v)).card+2*((univ.biUnion R).filter ((colorGraph c k).Adj v)).card := by
  classical
  let G := colorGraph c k
  let N := (T.erase v).filter fun w => ¬G.Adj v w
  by_cases cl : G.IsClique (N : Set V)
  · have cap : N.card≤r := by
      by_contra! large
      obtain ⟨A,sub,size⟩ := exists_subset_card_eq (show r+1≤N.card by omega)
      obtain ⟨j,hj⟩ : (univ.erase k).Nonempty := card_pos.mp (by simp; omega)
      obtain ⟨x,hx,y,hy,ne,eq⟩ := hb A size j
      exact (mem_erase.mp hj).1 (eq.symm.trans (cl (sub hx) (sub hy) ne).2)
    have cnt := card_filter_add_card_filter_not (s:=T.erase v) (G.Adj v)
    have eq : (T.erase v).filter (G.Adj v)=T.filter (G.Adj v) := by
      ext x
      constructor
      · intro h
        obtain ⟨hx,adj⟩ := mem_filter.mp h
        exact mem_filter.mpr ⟨(mem_erase.mp hx).2,adj⟩
      · intro h
        obtain ⟨hx,adj⟩ := mem_filter.mp h
        exact mem_filter.mpr ⟨mem_erase.mpr ⟨adj.ne.symm,hx⟩,adj⟩
    change ((T.erase v).filter (G.Adj v)).card+N.card=(T.erase v).card at cnt
    rw [eq,card_erase_of_mem hv,order] at cnt
    change r≤(T.filter (G.Adj v)).card+_
    omega
  · obtain ⟨x,y,ne,miss⟩ := G.not_isClique_iff.mp cl
    obtain ⟨vx,xt⟩ := mem_erase.mp (mem_filter.mp x.prop).1
    obtain ⟨vy,yt⟩ := mem_erase.mp (mem_filter.mp y.prop).1
    have xy : x.val≠y.val := fun eq => ne (Subtype.ext eq)
    let A : Finset V := {v,x.val,y.val}
    have sub : A⊆T := insert_subset hv (insert_subset xt (singleton_subset_iff.mpr yt))
    have ind : G.IsNIndepSet 3 A := by
      apply G.isNClique_compl.mp
      exact (is3Clique_triple_iff (G:=Gᶜ) (a:=v) (b:=x.val) (c:=y.val)).mpr ⟨⟨vx.symm,(mem_filter.mp x.prop).2⟩,
        ⟨vy.symm,(mem_filter.mp y.prop).2⟩,⟨xy,miss⟩⟩
    have spoke := parallel_family_vertex_spoke c k hb (show r-2+2=r by omega)
      R full dis A ind (fun i => (apart i).mono_left sub) v (mem_insert_self ..)
    have count : ((univ.biUnion R).filter (G.Adj v)).card=r-2 := by
      rw [filter_biUnion,card_biUnion]
      · simpa [G] using sum_congr (s₁:=univ) rfl (fun i _ => spoke i)
      · intro i _ j _ ne
        exact (dis ne).mono (filter_subset ..) (filter_subset ..)
    change r≤_+2*((univ.biUnion R).filter (G.Adj v)).card
    rw [count]
    omega

end Erdos617
