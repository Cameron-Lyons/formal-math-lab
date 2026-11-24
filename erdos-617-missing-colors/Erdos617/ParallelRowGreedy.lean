import Erdos617.ColorGraph
import Erdos617.IndependentSets

namespace Erdos617

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [DecidableEq V] {r : ℕ}

private theorem fill_parallel_rows {m : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (R : Fin m → Finset V)
    (full : ∀ i,(R i).card=r) (dis : Pairwise fun i j => Disjoint (R i) (R j))
    (one : ∀ i x, x∉R i → ((R i).filter (G.Adj x)).card≤1)
    (S : Finset V) (si : G.IsIndepSet (S:Set V)) (T : Finset (Fin m))
    (apart : ∀ i∈T, Disjoint S (R i)) (sz : S.card+T.card≤r) :
    ∃ I : Finset V, S⊆I ∧ I⊆S∪T.biUnion R ∧ I.card=S.card+T.card ∧ G.IsIndepSet (I:Set V) := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨S,Subset.rfl,subset_union_left,by simp,si⟩
  | @insert j T hj ih =>
    have grow := card_insert_of_notMem hj
    obtain ⟨I,sub,inside,order,ind⟩ := ih (fun i hi => apart _ (mem_insert_of_mem hi)) (by omega)
    have off (x : V) (hx : x∈I) : x∉R j := by
      rcases mem_union.mp (inside hx) with hs|ht
      · exact Finset.disjoint_left.mp (apart j (mem_insert_self ..)) hs
      · obtain ⟨i,hi,xi⟩ := mem_biUnion.mp ht
        have ij : i≠j := fun eq => hj (eq ▸ hi)
        exact Finset.disjoint_left.mp (dis ij) xi
    let K := I.biUnion fun x => (R j).filter (G.Adj x)
    have few := (card_biUnion_le (s:=I) (t:=fun x => (R j).filter (G.Adj x))).trans
      (sum_le_sum fun x hx => one j x (off x hx))
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at few
    have short : K.card<(R j).card := by change K.card≤I.card at few; rw [full]; omega
    obtain ⟨w,hw,nw⟩ := not_subset.mp (show ¬R j⊆K from fun h => short.not_ge (card_le_card h))
    have none (x : V) (hx : x∈I) : ¬ G.Adj w x := fun e =>
      nw (mem_biUnion.mpr ⟨x,hx,mem_filter.mpr ⟨hw,e.symm⟩⟩)
    refine ⟨insert w I,sub.trans (subset_insert ..),?_,?_,independent_insert_of_nonadjacent G ind w none⟩
    · rw [biUnion_insert]
      refine insert_subset (mem_union_right _ (mem_union_left _ hw)) ?_
      exact inside.trans (union_subset_union (Subset.rfl) subset_union_right)
    · rw [card_insert_of_notMem (fun h => off w h hw),grow,order]
      omega

private theorem reaches_every_point {m : ℕ} (c : Sym2 V → Fin r) (k : Fin r) (hb : Balanced c)
    (R : Fin m → Finset V) (size : ∀ i,(R i).card=r)
    (one : ∀ j x, x∉R j → ((R j).filter ((colorGraph c k).Adj x)).card≤1)
    (j : Fin m) (I : Finset V) (order : I.card=r) (ind : (colorGraph c k).IsIndepSet (I:Set V))
      (outside : ∀ u∈I,u∉R j) (u : V) (hu : u∈I) : ((R j).filter ((colorGraph c k).Adj u)).card=1 := by
    let G := colorGraph c k
    let N (i : Fin m) (v : V) := (R i).filter (G.Adj v)
    have all : R j ⊆ I.biUnion (N j) := by
      intro y hy
      by_contra no
      have none (v : V) (hv : v∈I) : ¬G.Adj y v := fun e =>
        no (mem_biUnion.mpr ⟨v,hv,mem_filter.mpr ⟨hy,e.symm⟩⟩)
      have add := independent_insert_of_nonadjacent G ind y none
      obtain ⟨a,ha,b,hb,ne,edge⟩ := hb (insert y I)
        ((card_insert_of_notMem (fun h => outside _ h hy)).trans (congrArg (·+1) order)) k
      exact add ha hb ne ⟨ne,edge⟩
    have needed := (card_le_card all).trans card_biUnion_le
    rw [size j] at needed
    change r≤∑ v∈I,((R j).filter ((colorGraph c k).Adj v)).card at needed
    have bound (v : V) (hv : v∈I) := one j v (outside v hv)
    apply (sum_eq_sum_iff_of_le bound).mp _ u hu
    have upper := sum_le_sum bound
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,order] at upper ⊢
    omega

/-- In r disjoint monochromatic r-cliques, one exterior vertex forces a
neighbor in each row and at least r−1 edges between each pair of rows. -/
theorem parallel_row_forcing (c : Sym2 V → Fin r) (k : Fin r) (hr : 3≤r) (hb : Balanced c)
    (R : Fin r → Finset V) (full : ∀ i,(colorGraph c k).IsNClique r (R i))
    (dis : Pairwise fun i j => Disjoint (R i) (R j)) (x : V) (out : ∀ i,x∉R i) :
    let G := colorGraph c k
    (∀ i, ((R i).filter (G.Adj x)).card=1) ∧
      ∀ i j,i≠j → r-1≤∑ u∈R i,((R j).filter (G.Adj u)).card := by
  classical
  let G := colorGraph c k
  let N (j : Fin r) (a : V) := (R j).filter (G.Adj a)
  have one (j) (a : V) (ha : a∉R j) : (N j a).card≤1 := by
    apply card_le_one.mpr
    intro u hu v hv
    exact exterior_clique_neighbor_unique c hb k _ (full j) a ha (mem_filter.mp hu).1 (mem_filter.mp hv).1
      (mem_filter.mp hu).2 (mem_filter.mp hv).2
  have demand := reaches_every_point c k hb R (fun i => (full i).card_eq) one
  have baseline (j : Fin r) : (N j x).card=1 := by
    let T := univ.erase j
    have nt : T.card=r-1 := by simp [T]
    have s : G.IsIndepSet (({x}:Finset V):Set V) := by simp
    obtain ⟨I,sub,inside,sz,ind⟩ := fill_parallel_rows G R (fun q => (full q).card_eq) dis one {x} s T
      (fun q _ => by simpa using out q) (by simp; omega)
    apply demand j I (by simpa using (show I.card=1+T.card by simpa using sz) |>.trans (by omega)) ind _ x (sub (mem_singleton_self x))
    intro u hu
    rcases mem_union.mp (inside hu) with he|hT
    · exact mem_singleton.mp he ▸ out j
    · obtain ⟨q,hq,uq⟩ := mem_biUnion.mp hT
      exact Finset.disjoint_left.mp (dis (mem_erase.mp hq).1) uq
  refine ⟨baseline,?_⟩
  intro i j ij
  let W := (R i).filter fun u => ¬G.Adj x u
  have wn : W.card=r-1 := by
    have h := card_filter_add_card_filter_not (s:=R i) (G.Adj x)
    change (N i x).card+W.card=(R i).card at h
    rw [baseline,(full i).card_eq] at h
    omega
  have per (u : V) (hu : u∈W) : 1≤(N j u).card := by
    obtain ⟨ui,missing⟩ := mem_filter.mp hu
    have ux : u≠x := fun eq => out i (eq ▸ ui)
    let T := (univ.erase i).erase j
    have nT : T.card=r-2 := by
      dsimp [T]
      rw [card_erase_of_mem (mem_erase.mpr ⟨ij.symm,mem_univ _⟩),card_erase_of_mem (mem_univ _),card_univ,Fintype.card_fin]
      omega
    let S := ({u,x}:Finset V)
    have pair : S.card=2 := card_pair ux
    have start : G.IsIndepSet (S:Set V) :=
      independent_insert_of_nonadjacent G (by simp : G.IsIndepSet (({x}:Finset V):Set V)) u (fun v hv e =>
        missing (mem_singleton.mp hv ▸ e.symm))
    have off {q} (hq : q≠i) : Disjoint S (R q) := by
      apply Finset.disjoint_left.mpr
      intro v hv
      rcases mem_insert.mp hv with rfl|eq
      · exact Finset.disjoint_left.mp (dis hq.symm) ui
      · exact mem_singleton.mp eq ▸ out q
    obtain ⟨I,sub,inside,sz,ind⟩ := fill_parallel_rows G R (fun q => (full q).card_eq) dis one S start T
      (fun q hq => off (mem_erase.mp (mem_erase.mp hq).2).1) (by omega)
    apply Nat.le_of_eq (Eq.symm (demand j I (by omega) ind _ u (sub (mem_insert_self ..))))
    intro v hv
    rcases mem_union.mp (inside hv) with vs|vt
    · exact Finset.disjoint_left.mp (off ij.symm) vs
    · obtain ⟨q,hq,vq⟩ := mem_biUnion.mp vt
      exact Finset.disjoint_left.mp (dis (mem_erase.mp hq).1) vq
  have lower := sum_le_sum per
  have all := sum_le_sum_of_subset_of_nonneg (filter_subset (fun u => ¬G.Adj x u) (R i))
    (f:=fun u => (N j u).card) (by simp)
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,wn] at lower
  exact lower.trans all

/-- An independent exterior set one vertex larger than the uncovered rank
forces many edges between each pair of disjoint full rows. -/
theorem parallel_family_cross_floor (c : Sym2 V → Fin r) (k : Fin r) (hb : Balanced c)
    {m q : ℕ} (mq : m+q=r) (R : Fin m → Finset V)
    (full : ∀ i,(colorGraph c k).IsNClique r (R i))
    (dis : Pairwise fun i j => Disjoint (R i) (R j))
    (A : Finset V) (ind : (colorGraph c k).IsNIndepSet (q+1) A) (off : ∀ i,Disjoint A (R i)) :
    ∀ i j,i≠j → m-1≤∑ u∈R i,((R j).filter ((colorGraph c k).Adj u)).card := by
  classical
  let G := colorGraph c k
  let N (i : Fin m) (u : V) := (R i).filter (G.Adj u)
  have one (i : Fin m) (u : V) (hu : u∉R i) : (N i u).card≤1 := by
    apply card_le_one.mpr
    intro a ha b hb'
    exact exterior_clique_neighbor_unique c hb k _ (full i) u hu
      (mem_filter.mp ha).1 (mem_filter.mp hb').1 (mem_filter.mp ha).2 (mem_filter.mp hb').2
  intro i j ij
  have two : 2≤m := by
    have count := card_le_univ ({i,j}:Finset (Fin m))
    rw [card_pair ij,Fintype.card_fin] at count
    exact count
  let W := R i \ A.biUnion (N i)
  have enough : m-1≤W.card := by
    have ub := (card_biUnion_le (s:=A) (t:=N i)).trans (sum_le_sum (fun u hu => one i u (Finset.disjoint_left.mp (off i) hu)))
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,ind.card_eq] at ub
    have split : W.card+(R i∩A.biUnion (N i)).card=(R i).card := card_sdiff_add_card_inter .. 
    have hi := card_le_card (inter_subset_right : R i∩A.biUnion (N i)⊆A.biUnion (N i))
    rw [(full i).card_eq] at split
    omega
  have per (u : V) (hu : u∈W) : 1≤(N j u).card := by
    obtain ⟨ui,un⟩ := mem_sdiff.mp hu
    let T := (univ.erase i).erase j
    have nT : T.card=m-2 := by
      dsimp [T]
      rw [card_erase_of_mem (mem_erase.mpr ⟨ij.symm,mem_univ _⟩),card_erase_of_mem (mem_univ _),card_univ,Fintype.card_fin]
      omega
    let S := insert u A
    have ord : S.card=q+2 := by
      rw [show S=insert u A by rfl,card_insert_of_notMem (Finset.disjoint_left.mp (off i).symm ui),ind.card_eq]
    have start : G.IsIndepSet (S:Set V) := independent_insert_of_nonadjacent G ind.isIndepSet u
      (fun v hv e => un (mem_biUnion.mpr ⟨v,hv,mem_filter.mpr ⟨ui,e.symm⟩⟩))
    have disS {p} (pi : p≠i) : Disjoint S (R p) := by
      apply Finset.disjoint_left.mpr
      intro z hz
      rcases mem_insert.mp hz with rfl|za
      · exact Finset.disjoint_left.mp (dis pi.symm) ui
      · exact Finset.disjoint_left.mp (off p) za
    obtain ⟨I,sub,inside,nI,stable⟩ := fill_parallel_rows G R (fun p => (full p).card_eq) dis one S start T
      (fun p hp => disS (mem_erase.mp (mem_erase.mp hp).2).1) (by omega)
    apply Nat.le_of_eq (Eq.symm (reaches_every_point c k hb R (fun p => (full p).card_eq) one j I
      (by omega) stable _ u (sub (mem_insert_self ..))))
    intro y hy
    rcases mem_union.mp (inside hy) with ys|yt
    · exact Finset.disjoint_left.mp (disS ij.symm) ys
    · obtain ⟨p,hp,yp⟩ := mem_biUnion.mp yt
      exact Finset.disjoint_left.mp (dis (mem_erase.mp hp).1) yp
  have sum := sum_le_sum per
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at sum
  exact enough.trans (sum.trans (sum_le_sum_of_subset_of_nonneg (sdiff_subset : W⊆R i) (by simp)))

/-- Every vertex in an exterior independent (q+1)-set has exactly one
neighbor on each of m disjoint full rows when m+q=r. -/
theorem parallel_family_vertex_spoke (c : Sym2 V → Fin r) (k : Fin r) (hb : Balanced c)
    {m q : ℕ} (mq : m+q=r) (R : Fin m → Finset V)
    (full : ∀ i,(colorGraph c k).IsNClique r (R i))
    (dis : Pairwise fun i j => Disjoint (R i) (R j))
    (A : Finset V) (ind : (colorGraph c k).IsNIndepSet (q+1) A) (off : ∀ i,Disjoint A (R i))
    (v : V) (hv : v∈A) (i : Fin m) : ((R i).filter ((colorGraph c k).Adj v)).card=1 := by
  classical
  let G := colorGraph c k
  have one (j : Fin m) (u : V) (hu : u∉R j) : ((R j).filter (G.Adj u)).card≤1 := by
    apply card_le_one.mpr
    intro a ha b hb'
    exact exterior_clique_neighbor_unique c hb k _ (full j) u hu
      (mem_filter.mp ha).1 (mem_filter.mp hb').1 (mem_filter.mp ha).2 (mem_filter.mp hb').2
  let T := univ.erase i
  have order : A.card+T.card=r := by
    have nt : T.card=m-1 := by simp [T]
    have := i.isLt
    rw [ind.card_eq]
    omega
  obtain ⟨I,sub,inside,nI,stable⟩ := fill_parallel_rows G R (fun j => (full j).card_eq) dis one A
    ind.isIndepSet T (fun j _ => off j) order.le
  apply reaches_every_point c k hb R (fun j => (full j).card_eq) one i I (nI.trans order) stable _ v (sub hv)
  intro w hw
  rcases mem_union.mp (inside hw) with wa|wt
  · exact Finset.disjoint_left.mp (off i) wa
  · obtain ⟨j,hj,wj⟩ := mem_biUnion.mp wt
    exact Finset.disjoint_left.mp (dis (mem_erase.mp hj).1) wj

end Erdos617
