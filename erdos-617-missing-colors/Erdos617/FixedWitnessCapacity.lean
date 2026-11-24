import Erdos617.ExteriorPairCounts

namespace Erdos617

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [DecidableEq V]

/-- To extend two nonadjacent vertices, keep J fixed and choose one
representative from each remaining row. -/
theorem fixed_witness_pair_blocked [Fintype V] {r n : ℕ} {c : Sym2 V → Fin r} {k : Fin r}
    (hb : Balanced c) (J : Finset V) (P : Fin n → Finset V) (size : n+J.card=r-1) (hr : 1≤r)
    (indJ : (colorGraph c k).IsIndepSet (J : Set V))
    (dis : Pairwise fun i j => Disjoint (P i) (P j)) (apart : ∀ i,Disjoint (P i) J)
    (sep : ∀ i j,i≠j → ∀ u∈P i,∀ v∈P j,¬(colorGraph c k).Adj u v)
    (sepJ : ∀ i,∀ u∈P i,∀ v∈J,¬(colorGraph c k).Adj u v)
    (A : Finset V) (indA : (colorGraph c k).IsIndepSet (A : Set V))
    (off : ∀ i,Disjoint A (P i)) (offJ : Disjoint A J)
    (noJ : ∀ x∈A,∀ y∈J,¬(colorGraph c k).Adj x y)
    {x y : V} (hx : x∈A) (hy : y∈A) (xy : x≠y) :
    ∃ i,nonneighborRemainder (colorGraph c k) (P i) {x,y}=∅ := by
  classical
  let G := colorGraph c k
  by_contra! all
  choose w hw using all
  have row (i) := (mem_nonneighborRemainder G).mp (hw i)
  let I := univ.image w
  have inj : Function.Injective w := by
    intro i j eq
    by_contra ij
    exact disjoint_left.mp (dis ij) (row i).1 (eq ▸ (row j).1)
  have indep : G.IsIndepSet (I : Set V) := by
    intro a ha b hb ab
    obtain ⟨i,_,rfl⟩ := mem_image.mp ha
    obtain ⟨j,_,rfl⟩ := mem_image.mp hb
    exact sep i j (fun eq => ab (congrArg w eq)) _ (row i).1 _ (row j).1
  have non (a : V) (ha : a∈I) (b : V) (hb : b∈J) : ¬G.Adj a b := by
    obtain ⟨i,_,rfl⟩ := mem_image.mp ha
    exact sepJ i _ (row i).1 b hb
  have joint : G.IsIndepSet ((I∪J : Finset V) : Set V) := by
    intro a ha b hb ab e
    rcases mem_union.mp ha with aI|aJ <;> rcases mem_union.mp hb with bI|bJ
    · exact indep aI bI ab e
    · exact non a aI b bJ e
    · exact non b bI a aJ e.symm
    · exact indJ aJ bJ ab e
  have IJ : Disjoint I J := disjoint_left.mpr (by
    intro a ha hJ
    obtain ⟨i,_,rfl⟩ := mem_image.mp ha
    exact disjoint_left.mp (apart i) (row i).1 hJ)
  have none (z : V) (hz : z∈({x,y} : Finset V)) (v : V) (hv : v∈I∪J) : ¬G.Adj z v := by
    rcases mem_union.mp hv with h|h
    · obtain ⟨i,_,rfl⟩ := mem_image.mp h
      exact (row i).2 z hz
    · exact noJ z ((insert_subset hx (singleton_subset_iff.mpr hy)) hz) v h
  have outside (z : V) (hz : z∈A) : z∉I∪J := by
    intro inside
    rcases mem_union.mp inside with h|h
    · obtain ⟨i,_,rfl⟩ := mem_image.mp h
      exact disjoint_left.mp (off i) hz (row i).1
    · exact disjoint_left.mp offJ hz h
  have large := independent_insert_of_nonadjacent G
    (independent_insert_of_nonadjacent G joint y (none _ (by simp))) x
    (fun v hv => (mem_insert.mp hv).elim (fun e => e ▸ indA hx hy xy) (none _ (by simp) v))
  have count : (insert x (insert y (I∪J))).card=r+1 := by
    rw [card_insert_of_notMem (by simp [xy,outside _ hx]),card_insert_of_notMem (outside _ hy),
      card_union_of_disjoint IJ,card_image_of_injective _ inj,card_univ,Fintype.card_fin,size]
    omega
  obtain ⟨a,ha,b,hb',ne,e⟩ := hb _ count k
  exact large ha hb' ne ⟨ne,e⟩

/-- A line with at most two spokes to any row vertex can leave only
O(√n) outside vertices individually unassigned to its n cleaned rows. -/
theorem fixed_witness_line_capacity [Fintype V] {r n : ℕ} {c : Sym2 V → Fin r} {k : Fin r}
    (hb : Balanced c) (J : Finset V) (P : Fin n → Finset V) (size : n+J.card=r-1) (hr : 1≤r)
    (indJ : (colorGraph c k).IsIndepSet (J : Set V)) (pos : ∀ i,(P i).Nonempty)
    (dis : Pairwise fun i j => Disjoint (P i) (P j)) (apart : ∀ i,Disjoint (P i) J)
    (sep : ∀ i j,i≠j → ∀ u∈P i,∀ v∈P j,¬(colorGraph c k).Adj u v)
    (sepJ : ∀ i,∀ u∈P i,∀ v∈J,¬(colorGraph c k).Adj u v)
    (A : Finset V) (indA : (colorGraph c k).IsIndepSet (A : Set V))
    (off : ∀ i,Disjoint A (P i)) (offJ : Disjoint A J)
    (noJ : ∀ x∈A,∀ y∈J,¬(colorGraph c k).Adj x y)
    (cap : ∀ i,∀ u∈P i,(A.filter fun w => (colorGraph c k).Adj w u).card≤2)
    (free : ∀ i,∀ w∈A,(nonneighborRemainder (colorGraph c k) (P i) {w}).Nonempty) :
    A.card*A.card≤A.card+8*n := by
  classical
  let G := colorGraph c k
  let E (i : Fin n) := A.offDiag.filter fun p => nonneighborRemainder G (P i) {p.1,p.2}=∅
  have charge : A.offDiag⊆univ.biUnion E := by
    rintro ⟨x,y⟩ h
    obtain ⟨hx,hy,xy⟩ := mem_offDiag.mp h
    obtain ⟨i,stuck⟩ := fixed_witness_pair_blocked hb J P size hr indJ dis apart sep sepJ
      A indA off offJ noJ hx hy xy
    exact mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨h,stuck⟩⟩
  have row (i : Fin n) : (E i).card≤8 := by
    have cols (u : V) (hu : u∈P i) : (A.filter fun w => G.Adj w u).card≤2 := cap i u hu
    apply exterior_row_blocked_pairs G A (P i) (pos i) _ (free i)
    intro u hu
    convert cols u hu using 2
    apply filter_congr_decidable
  have all := (card_le_card charge).trans (card_biUnion_le.trans (sum_le_sum fun i _ => row i))
  rw [offDiag_card] at all
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at all
  omega

/-- Charge a cleaned row to one outside vertex if its original (r−1)-clique
lost fewer than half its vertices. Every other nonempty row costs at most
four on a pair of full lines. -/
theorem cleaned_row_two_line_capacity {r : ℕ} {c : Sym2 V → Fin r} {k : Fin r}
    (hr : 2≤r) (hb : Balanced c) (O P C D : Finset V) (sub : P⊆O) (nonempty : P.Nonempty)
    (cl : (colorGraph c k).IsClique (O : Set V)) (dis : Disjoint O (C∪D))
    (capC : ∀ u∈P,(C.filter fun w => (colorGraph c k).Adj w u).card≤2)
    (capD : ∀ u∈P,(D.filter fun w => (colorGraph c k).Adj w u).card≤2) :
    ((C∪D).filter fun w => ∀ u∈P,(colorGraph c k).Adj w u).card ≤
      if O.card=r-1 ∧ 2*(O.card-P.card)+1<r-1 then 1 else 4 := by
  classical
  let W := (C∪D).filter fun w => ∀ u∈P,(colorGraph c k).Adj w u
  split
  · rename_i h
    obtain ⟨full,few⟩ := h
    apply near_neighbors_of_large_clique hb (b:=1) (q:=O.card-P.card)
      (by simpa using few) O W (by omega) cl (dis.mono_right (filter_subset ..))
    intro w hw
    have le : (O.filter fun x => ¬(colorGraph c k).Adj w x)⊆O \ P := by
      intro v hv
      exact mem_sdiff.mpr ⟨(mem_filter.mp hv).1,fun bad => (mem_filter.mp hv).2 ((mem_filter.mp hw).2 v bad)⟩
    exact (card_le_card le).trans_eq (card_sdiff_of_subset sub)
  · obtain ⟨u,hu⟩ := nonempty
    have inc : W⊆(C.filter fun w => (colorGraph c k).Adj w u)∪(D.filter fun w => (colorGraph c k).Adj w u) := by
      intro w hw
      obtain ⟨inside,all⟩ := mem_filter.mp hw
      exact (mem_union.mp inside).elim (fun h => mem_union_left _ (mem_filter.mpr ⟨h,all _ hu⟩))
        (fun h => mem_union_right _ (mem_filter.mpr ⟨h,all _ hu⟩))
    exact (card_le_card inc).trans ((card_union_le ..).trans (Nat.add_le_add (capC u hu) (capD u hu)))

end Erdos617
