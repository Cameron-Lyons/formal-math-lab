module

public import Erdos617.ExteriorBlocks

@[expose] public section

namespace Erdos617

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [DecidableEq V]

/-- Once pairs of uncovered outside vertices are charged to individual
blocks, an exterior line contains only O(√r) uncovered vertices. -/
theorem line_unassigned_pair_capacity [Fintype V] {r : ℕ} {c : Sym2 V → Fin r} {k : Fin r}
    (hr : 3≤r) (hb : Balanced c) (H : Finset V) (P : Fin (r-3) → Finset V)
    (dis : Pairwise fun i j => Disjoint (P i) (P j)) (apart : ∀ i,Disjoint (P i) H)
    (sep : ∀ i j,i≠j → ∀ u∈P i,∀ v∈P j,¬(colorGraph c k).Adj u v)
    (sepH : ∀ i,∀ u∈P i,∀ v∈H,¬(colorGraph c k).Adj u v)
    (A : Finset V) (ind : (colorGraph c k).IsIndepSet (A : Set V))
    (offH : Disjoint A H) (off : ∀ i,Disjoint A (P i))
    (row : ∀ i,(A.offDiag.filter fun p =>
      nonneighborRemainder (colorGraph c k) (P i) {p.1,p.2}=∅).card≤16)
    (core : (A.offDiag.filter fun p => (colorGraph c k).IsClique
      (nonneighborRemainder (colorGraph c k) H {p.1,p.2} : Set V)).card≤64) :
    A.card*A.card≤A.card+16*(r-3)+64 := by
  classical
  let G := colorGraph c k
  let E (i : Fin (r-3)) := A.offDiag.filter fun p => nonneighborRemainder G (P i) {p.1,p.2}=∅
  let F := A.offDiag.filter fun p => G.IsClique (nonneighborRemainder G H {p.1,p.2} : Set V)
  have charge : A.offDiag ⊆ univ.biUnion E ∪ F := by
    rintro ⟨x,y⟩ h
    obtain ⟨hx,hy,xy⟩ := mem_offDiag.mp h
    have sub : {x,y}⊆A := insert_subset hx (singleton_subset_iff.mpr hy)
    rcases exterior_pair_blocked hr hb H P dis apart sep sepH x y xy (ind hx hy xy)
      (offH.mono_left sub) (fun i => (off i).mono_left sub) with ⟨i,stuck⟩|stuck
    · exact mem_union_left _ (mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨h,stuck⟩⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨h,stuck⟩)
  have all := (card_le_card charge).trans (card_union_le ..)
  have budget := card_biUnion_le (s:=univ) (t:=E) |>.trans (sum_le_sum (fun i _ => row i))
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at budget
  rw [offDiag_card] at all
  change F.card≤64 at core
  omega

/-- Two lines whose union has size 2r−1 cannot both satisfy the pair
capacity after at most r−3+g row assignments and sixteen core assignments. -/
theorem two_line_capacity_numeric {r g a b : ℕ} (hr : 100000≤r) (gap : 4*g≤3*r)
    (many : 2*r-1≤r-3+g+16+a+b)
    (ca : a*a≤a+16*(r-3)+64) (cb : b*b≤b+16*(r-3)+64) : False := by
  have bound (n : ℕ) (cap : n*n≤n+16*(r-3)+64) : 16*n<r := by
    by_contra! large
    have grow := Nat.mul_le_mul_right r (show 100000≤r from hr)
    have sq := Nat.mul_le_mul large large
    by_cases big : r≤n
    · have more := Nat.mul_le_mul_left n (show 100000≤n by omega)
      nlinarith only [more,cap,big,show r-3≤r by omega,hr]
    · have small : n≤r := by omega
      nlinarith only [grow,sq,cap,small,show r-3≤r by omega,hr]
  have aa := bound a ca
  have bb := bound b cb
  omega

end Erdos617
