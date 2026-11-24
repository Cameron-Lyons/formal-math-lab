import Erdos617.BudgetedGoodColor
import Erdos617.GrowingSquareExcess

namespace Erdos617

open Finset SimpleGraph
open scoped Classical

/-- On every smaller square disjoint from a pair of transverse full lines,
the number of individually avoidable colors grows at least on the order of √r. -/
theorem two_line_avoidable_quadratic_bound {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c)
    {i j : Fin r} (C D U : Finset V)
    (fullC : (colorGraph c i).IsNClique r C) (fullD : (colorGraph c j).IsNClique r D)
    (meet : (C∩D).card=1) (out : Disjoint U (C∪D)) (sz : U.card=(r-1)^2+1) :
    let d := fun e : Sym2 U => c (e.map Subtype.val)
    let b := (univ.filter fun k => ¬HitsPalette d (r-1) {k}).card
    r≤4000*(b/2+1)^2 := by
  intro d b
  by_contra! high
  have twice : b≤2*(b/2)+1 := by omega
  have broad := Nat.pow_le_pow_left (show b+2≤3*(b/2+1) by omega) 2
  have sparse : 10*(b+1)≤r := by nlinarith only [high,twice,Nat.zero_le ((b/2)^2),Nat.zero_le (b/2)]
  have square : (b+2)^2≤r := by nlinarith only [high,broad,Nat.zero_le ((b/2)^2),Nat.zero_le (b/2)]
  obtain ⟨k,ki,kj,cap,no,upper⟩ := exists_budgeted_good_color hn c hb U sz i j sparse square
  exact impossible_small_two_line_good (b:=b/2) high hb ki kj C D U
    fullC fullD meet out sz cap no upper

/-- A two-direction restriction and an explicit bound on its avoidable colors
hold together on the same square. -/
theorem exists_row_square_growing_avoidable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (hr : 5≤r) (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c) :
    ∃ (i j : Fin r) (C D : Finset V), i≠j ∧ (colorGraph c i).IsNClique r C ∧
      (colorGraph c j).IsNClique r D ∧ (C∩D).card=1 ∧
      let U := (C∪D)ᶜ
      let d := fun e : Sym2 U => c (e.map Subtype.val)
      let b := (univ.filter fun k => ¬HitsPalette d (r-1) {k}).card
      U.card=(r-1)^2+1 ∧ rankOn (colorGraph c i) U≤r-1 ∧ rankOn (colorGraph c j) U≤r-1 ∧
      r≤4000*(b/2+1)^2 := by
  obtain ⟨i,j,C,D,ne,fullC,fullD,meet,sz,ri,rj⟩ := exists_two_line_square hr hn c hb
  exact ⟨i,j,C,D,ne,fullC,fullD,meet,sz,ri,rj,
    two_line_avoidable_quadratic_bound hn c hb C D (C∪D)ᶜ fullC fullD meet disjoint_compl_left sz⟩

/-- The number of individually avoidable colors on a square outside two
intersecting full rows is at least (r−99)/33. -/
theorem two_line_avoidable_linear_bound {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c)
    {i j : Fin r} (C D U : Finset V)
    (fullC : (colorGraph c i).IsNClique r C) (fullD : (colorGraph c j).IsNClique r D)
    (meet : (C∩D).card=1) (out : Disjoint U (C∪D)) (sz : U.card=(r-1)^2+1) :
    let d := fun e : Sym2 U => c (e.map Subtype.val)
    let b := (univ.filter fun k => ¬HitsPalette d (r-1) {k}).card
    r≤33*b+99 := by
  intro d b
  by_contra! large
  have many : 3≤b := three_avoidable_on_every_square (by omega) hn c hb U sz
  obtain ⟨k,ki,kj,cap,no,budget⟩ :=
    exists_good_color_for_linear_contradiction hn c hb U sz i j (show 33*b+100≤r by omega)
  exact impossible_linear_two_line_good (b:=33*b/64) (by omega) (by omega) hb ki kj C D U
    fullC fullD meet out sz cap no budget

/-- Deleting two full rows exhibits a common smaller square, two hitting
colors, and a family of r-vertex witnesses avoiding a linear number of colors. -/
theorem exists_row_square_many_ambient_witnesses {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (hr : 5≤r) (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c) :
    ∃ (i j : Fin r) (C D K : Finset V), i≠j ∧ (colorGraph c i).IsNClique r C ∧
      (colorGraph c j).IsNClique r D ∧ (C∩D).card=1 ∧ K=(C∪D)ᶜ ∧
      K.card=(r-1)^2+1 ∧ rankOn (colorGraph c i) K≤r-1 ∧ rankOn (colorGraph c j) K≤r-1 ∧
      ∃ (J : Finset (Fin r)) (W : J → Finset V), r≤33*J.card+99 ∧
        ∀ k, W k⊆K ∧ (colorGraph c k.val).IsNIndepSet r (W k) := by
  classical
  obtain ⟨i,j,C,D,ne,clC,clD,meet,sz,ri,rj⟩ := exists_two_line_square hr hn c hb
  let K := (C∪D)ᶜ
  let d := fun e : Sym2 K => c (e.map Subtype.val)
  let J := univ.filter fun k => ¬HitsPalette d (r-1) {k}
  have bound := two_line_avoidable_linear_bound hn c hb C D K clC clD meet disjoint_compl_left sz
  have witness (k : J) : ∃ W⊆K, (colorGraph c k.val).IsNIndepSet r W := by
    have miss := (mem_filter.mp k.prop).2
    have big : r-1<(colorGraph d k.val).indepNum := by
      apply lt_of_not_ge
      intro small
      exact miss ((hitsPalette_singleton_iff_indepNum d (r-1) k.val).2 small)
    obtain ⟨I,ind⟩ := (colorGraph d k.val).exists_isNIndepSet_indepNum
    obtain ⟨W,sub,n⟩ := exists_subset_card_eq (s:=I) (show r≤I.card by rw [ind.card_eq]; omega)
    exact lift_independent_subset c k.val K ⟨W,ind.isIndepSet.mono sub,n⟩
  choose W sub ind using witness
  exact ⟨i,j,C,D,K,ne,clC,clD,meet,rfl,sz,ri,rj,J,W,bound,fun k => ⟨sub k,ind k⟩⟩

end Erdos617
