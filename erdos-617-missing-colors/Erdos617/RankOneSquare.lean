module

public import Erdos617.RankOneDeletion
public import Erdos617.RankOneFamilies
public import Erdos617.RankFiveRange

@[expose] public section

namespace Erdos617

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ} {c : Sym2 V → Fin r}

/-- A lower bound of m+2 on every first obstruction gives a square m colors
smaller, on which two distinct original colors meet the smaller balance test. -/
theorem exists_square_of_obstruction_rank (hr : 3≤r) (hn : Fintype.card V=r^2+1)
    (hb : Balanced c) {m : ℕ} (hm : 2≤m)
    (floor : ∀ (k : Fin r) (t : ℕ) (W : Finset V), MinimalObstruction c k t W → t<r → m+2≤t) :
    ∃ (i j : Fin r) (U : Finset V), i≠j ∧ U.card=(r-m)^2+1 ∧
      rankOn (colorGraph c i) U≤r-m ∧ rankOn (colorGraph c j) U≤r-m := by
  obtain ⟨i,j,P,Q,ne,cp,cq,_,_,clP,clQ,ri,rj⟩ :=
    exists_rank_one_families hr hn hb (m+2) (by omega) floor
  simp only [Nat.add_sub_cancel] at cp cq ri rj
  obtain ⟨k,t,W,_,high,h⟩ := exists_minimalObstruction_ceil_half hr hn c hb
  have low := floor k t W h (by omega)
  obtain ⟨U,sz,ra,rb⟩ := exists_square_of_clique_rows hn hb ne (by omega : m≤r) P Q cp cq clP clQ ri rj
  exact ⟨i,j,U,ne,sz,ra,rb⟩

/-- An unbounded reduction in square order. It holds simultaneously for all
m≥2 with 1000(m+1)²<r, without restrictions on the coloring's degrees. -/
theorem exists_square_of_quadratic_gap (hr : 3≤r) (hn : Fintype.card V=r^2+1)
    (hb : Balanced c) {m : ℕ} (hm : 2≤m) (gap : 1000*(m+1)^2<r) :
    ∃ (i j : Fin r) (U : Finset V), i≠j ∧ U.card=(r-m)^2+1 ∧
      rankOn (colorGraph c i) U≤r-m ∧ rankOn (colorGraph c j) U≤r-m := by
  apply exists_square_of_obstruction_rank hr hn hb hm
  intro k t W h htr
  by_contra! low
  have floor := h.quadratic_bound hr hb htr
  have limit := Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left (show t≤m+1 by omega) 2)
  omega

/-- Four units of reduction already apply at 33 colors. -/
theorem exists_four_row_square (hr : 33≤r) (hn : Fintype.card V=r^2+1) (hb : Balanced c) :
    ∃ (i j : Fin r) (U : Finset V), i≠j ∧ U.card=(r-4)^2+1 ∧
      rankOn (colorGraph c i) U≤r-4 ∧ rankOn (colorGraph c j) U≤r-4 :=
  exists_square_of_obstruction_rank (by omega) hn hb (by decide)
    (fun _ _ _ h ht => h.six_le_of_thirty_three_le hr hb ht)

end Erdos617
