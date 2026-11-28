module

public import Erdos617.RankFiveShell

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] {r : ℕ} {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V}

local notation "G" => colorGraph c k

omit [DecidableEq V] in
private theorem order_cap (h : MinimalObstruction c k 5 S) (hr : 0<r) {A : Finset V}
    (sub : A⊂S) {q : ℕ} (rk : rankOn (colorGraph c k) A≤q) : A.card≤q*r := by
  obtain ⟨I,hi,ind,small⟩ := h.proper_subset hr A sub
  exact small.trans (Nat.mul_le_mul_right _ ((card_le_rankOn _ hi ind).trans rk))

private theorem short_density (h : MinimalObstruction c k 5 S) (hr : 10≤r) (hb : Balanced c)
    {A : Finset V} (sub : A⊂S) {q : ℕ} (qlo : 2≤q) (qhi : q≤3)
    (sz : A.card+1=q*r) (rk : rankOn (colorGraph c k) A≤q) :
    r*A.card≤blockEdges (colorGraph c k) A+(r.choose 2+1)*q+(r-1) := by
  have prod := Nat.mul_le_mul_right r qlo
  have ins : RankInseparable G A := by
    refine ⟨card_pos.mp (by omega),?_⟩
    intro X Y posX posY dis eq
    by_contra! sum
    have ax : X⊆A := eq ▸ subset_union_left
    have ay : Y⊆A := eq ▸ subset_union_right
    have lx := rankOn_pos G posX
    have ly := rankOn_pos G posY
    change rankOn G A≤q at rk
    have small (Z : Finset V) (incl : Z⊆A) (pos : Z.Nonempty) (cap : rankOn G Z≤2) :
        Z.card<rankOn G Z*r := by
      have bound := order_cap h (by omega) (incl.trans_ssubset sub) (le_refl (rankOn G Z))
      refine lt_of_le_of_ne bound fun e => ?_
      have := h.three_le_tight_rank hb (by omega) (by omega) (incl.trans sub.le) pos e
      change 3≤rankOn G Z at this
      omega
    have u := small X ax posX (by omega)
    have v := small Y ay posY (by omega)
    have both := Nat.mul_le_mul_right r (sum.trans rk)
    rw [Nat.add_mul] at both
    have sizes := congrArg card eq
    rw [card_union_of_disjoint dis] at sizes
    omega
  have bound := rank_density G A ins r
  exact bound.trans (by gcongr)

/-- A lower edge bound at exact rank-three order, inside a rank-five obstruction. -/
theorem MinimalObstruction.rank_three_at_three_rows (h : MinimalObstruction c k 5 S) (hr : 10≤r) (hb : Balanced c)
    {A : Finset V} (sub : A⊂S) (sz : A.card=3*r) (rk : rankOn (colorGraph c k) A≤3) :
    3*r*(r+1)≤2*blockEdges (colorGraph c k) A+14 := by
  obtain ⟨d,W,cost,ws,card,rank,eq,avg,prices⟩ := h.rank_shell hb hr (by omega) sub.le
    (card_pos.mp (by omega))
  change rankOn G W+1≤rankOn G A at rank
  change rankOn G A≤3 at rk
  have low := h.rank_two_card_lt hb (by omega) (by omega) (ws.le.trans sub.le) (by omega)
  rw [sz] at card avg
  by_cases high : r+1≤d
  · exact (Nat.mul_le_mul_left (3*r) high).trans (avg.trans (Nat.le_add_right ..))
  have deq : d=r := by omega
  have nw : W.card+1=2*r := by omega
  have den := short_density h hr hb (ws.trans sub) (q:=2) (by decide) (by decide) nw (by omega)
  have mid := (prices r (by
    intro D ds rd
    have one : rankOn G D≤1 := by omega
    have b := order_cap h (by omega) (ds.trans_ssubset (ws.trans sub)) one
    simp only [Nat.one_mul] at b
    have less : D.card<r := by
      refine lt_of_le_of_ne b fun e => ?_
      have pos : D.Nonempty := card_pos.mp (by omega)
      have q := rankOn_pos G pos
      have one' : rankOn G D=1 := by omega
      exact h.no_clique hb (by omega) D ((ds.trans ws.le).trans sub.le) ⟨rank_one_clique _ one',e⟩
    omega)).2.1 deq
  rw [deq,Nat.choose_succ_succ' r 1,Nat.choose_one_right] at eq
  have m := congrArg (r*·) nw
  have e := twice_choose_two r
  change r*W.card≤blockEdges G W+(r.choose 2+1)*2+(r-1) at den
  change blockEdges G A=r+r.choose 2+cost+blockEdges G W at eq
  change 3*r*(r+1)≤2*blockEdges G A+14
  nlinarith only [den,m,e,mid,eq,Nat.sub_add_cancel (show 1≤r by omega)]

/-- The corresponding floor at exact rank-four order. -/
theorem MinimalObstruction.rank_four_at_four_rows (h : MinimalObstruction c k 5 S) (hr : 10≤r) (hb : Balanced c)
    {A : Finset V} (sub : A⊂S) (sz : A.card=4*r) (rk : rankOn (colorGraph c k) A≤4) :
    2*r*(r+1)≤blockEdges (colorGraph c k) A+8 := by
  obtain ⟨d,W,cost,ws,card,rank,eq,avg,prices⟩ := h.rank_shell hb hr (by omega) sub.le (card_pos.mp (by omega))
  rw [sz] at card avg
  change rankOn G W+1≤rankOn G A at rank
  change rankOn G A≤4 at rk
  have low := order_cap h (by omega) (ws.trans sub) (q:=3) (by omega)
  change 2*r*(r+1)≤blockEdges G A+8
  by_cases high : r+1≤d
  · have comp := Nat.mul_le_mul_left (4*r) high
    nlinarith only [avg,comp]
  rcases show d+1=r ∨ d=r by omega with deq | deq
  · have nw : W.card=3*r := by omega
    have den := h.rank_three_at_three_rows hr hb (ws.trans sub) nw (by omega)
    have mid := (prices (r+1) (by
      intro D ds rd
      have cap := h.rank_two_card_lt hb (by omega) (by omega) ((ds.trans ws.le).trans sub.le) (by omega)
      omega)).1 deq
    rw [deq] at eq
    have ch := twice_choose_two r
    change 3*r*(r+1)≤2*blockEdges G W+14 at den
    nlinarith only [den,mid,eq,ch]
  · have nw : W.card+1=3*r := by omega
    have den := short_density h hr hb (ws.trans sub) (q:=3) (by decide) (by decide) nw (by omega)
    have mid := (prices r (by
      intro D ds rd
      have cap := h.rank_two_card_lt hb (by omega) (by omega) ((ds.trans ws.le).trans sub.le) (by omega)
      omega)).2.1 deq
    rw [deq,Nat.choose_succ_succ' r 1,Nat.choose_one_right] at eq
    have m := congrArg (r*·) nw
    have ch := twice_choose_two r
    change r*W.card≤blockEdges G W+(r.choose 2+1)*3+(r-1) at den
    nlinarith only [den,m,ch,mid,eq,Nat.sub_add_cancel (show 1≤r by omega)]

/-- Four rows less one vertex still require at least 2r²−6 edges. -/
theorem MinimalObstruction.rank_four_one_short (h : MinimalObstruction c k 5 S) (hr : 10≤r) (hb : Balanced c)
    {A : Finset V} (sub : A⊂S) (sz : A.card+1=4*r) (rk : rankOn G A≤4) :
    2*r*r≤blockEdges G A+6 := by
  classical
  have pos : A.Nonempty := card_pos.mp (by omega)
  by_cases ins : RankInseparable G A
  · have den := (rank_density G A ins r).trans (Nat.add_le_add_right (Nat.add_le_add_left
      (Nat.mul_le_mul_left (r.choose 2+1) rk) (blockEdges G A)) (r-1))
    have mult := congrArg (r*·) sz
    nlinarith only [den,mult,twice_choose_two r,Nat.sub_add_cancel (show 1≤r by omega)]
  obtain ⟨X,Y,posX,posY,dis,union,sum⟩ : ∃ X Y : Finset V, X.Nonempty ∧ Y.Nonempty ∧
      Disjoint X Y ∧ X∪Y=A ∧ rankOn G X+rankOn G Y≤rankOn G A := by
    by_contra! every
    exact ins ⟨pos,fun {X Y} hx hy hd he => every X Y hx hy hd he⟩
  have split {X Y : Finset V} (dis : Disjoint X Y) (union : X∪Y=A)
      (one : rankOn G X=1) (three : rankOn G Y=3) : 2*r*r≤blockEdges G A+6 := by
    have subX : X⊆A := union ▸ subset_union_left
    have subY : Y⊆A := union ▸ subset_union_right
    have nx := order_cap h (by omega) (subX.trans_ssubset sub) one.le
    simp only [Nat.one_mul] at nx
    have ny := order_cap h (by omega) (subY.trans_ssubset sub) three.le
    have hx : X.card<r := lt_of_le_of_ne nx (fun eq => h.no_clique hb (by omega) X
      (subX.trans sub.le) ⟨rank_one_clique G one,eq⟩)
    have sizes := congrArg card union
    rw [card_union_of_disjoint dis] at sizes
    have den := h.rank_three_at_three_rows hr hb (subY.trans_ssubset sub) (by omega) three.le
    have hedge : 2*blockEdges G X+X.card=X.card*X.card := by
      rw [←block_degree_sum]
      have loc (v : V) (hv : v∈X) : X.filter ((colorGraph c k).Adj v)=X.erase v := by
        ext u
        constructor
        · intro hu
          exact mem_erase.mpr ⟨(mem_filter.mp hu).2.ne.symm,(mem_filter.mp hu).1⟩
        · intro hu
          obtain ⟨ne,hu⟩ := mem_erase.mp hu
          exact mem_filter.mpr ⟨hu,rank_one_clique G one hv hu ne.symm⟩
      have div (v : V) (hv : v∈X) : (X.filter ((colorGraph c k).Adj v)).card=X.card-1 := by rw [loc v hv,card_erase_of_mem hv]
      rw [sum_congr rfl div,sum_const,nsmul_eq_mul]
      have nx' : 1≤X.card := by omega
      have step := congrArg (X.card*·) (Nat.sub_add_cancel nx')
      simpa [Nat.mul_add] using step
    have total := blockEdges_union G dis
    rw [union] at total
    have xr : X.card+1=r := by omega
    have sq := congrArg (fun a : ℕ => a*a) xr
    nlinarith only [den,total,hedge,sq,xr,Nat.zero_le (∑ x∈X,(Y.filter ((colorGraph c k).Adj x)).card)]
  have Xle : X⊆A := union ▸ subset_union_left
  have Yle : Y⊆A := union ▸ subset_union_right
  have rx := rankOn_pos G posX
  have ry := rankOn_pos G posY
  by_cases highX : 3≤rankOn G X
  · exact split dis.symm ((union_comm Y X).trans union) (by omega) (by omega)
  by_cases highY : 3≤rankOn G Y
  · exact split dis union (by omega) (by omega)
  have small {D : Finset V} (inc : D⊆A) (pos : D.Nonempty) (s : rankOn G D<3) : D.card<rankOn G D*r := by
    exact lt_of_le_of_ne (order_cap h (by omega) (inc.trans_ssubset sub) le_rfl)
      (fun eq => (Nat.not_le_of_gt s) (h.three_le_tight_rank hb (by omega) (by omega) (inc.trans sub.le) pos eq))
  have bX := small Xle posX (by omega)
  have bY := small Yle posY (by omega)
  have sizes := congrArg card union
  rw [card_union_of_disjoint dis] at sizes
  have prod := Nat.mul_le_mul_right r (sum.trans rk)
  rw [Nat.add_mul] at prod
  omega

/-- A rank-five minimal obstruction costs more edges than the palette allows
when the number of colors is at least 33. -/
theorem MinimalObstruction.rank_five_lt_thirty_three (h : MinimalObstruction c k 5 S)
    (hb : Balanced c) : r<33 := by
  classical
  by_contra! hr
  have ht : 5<r := by omega
  have sz := h.card_eq
  have rk := h.rank_eq (by omega)
  have total := sum_color_edges (fun e : Sym2 S => c (Sym2.map Subtype.val e))
  rw [←sum_erase_add _ _ (mem_univ k),Fintype.card_coe,sz] at total
  have foreign := h.foreign_edge_sum hb (by omega)
  rw [←color_blockEdges_eq] at total
  norm_num [Nat.choose] at foreign
  have nedge := twice_choose_two (5*r+1)
  have top : 2*blockEdges G S ≤ 5*r*r+7*r+18 := by
    have multi := congrArg (·*(10*r+9)) (Nat.sub_add_cancel (show 1≤r by omega))
    nlinarith only [total,foreign,nedge,multi,Nat.sub_add_cancel (show 1≤r by omega)]
  obtain ⟨d,W,cost,ws,card,rank,eq,avg,prices⟩ := h.rank_shell hb (by omega) ht Subset.rfl (card_pos.mp (by omega))
  have base := order_cap h (by omega) ws (q:=4) (by omega)
  rw [sz] at card avg
  have dhigh : d≤r+1 := by
    by_contra! hlarge
    have mul := Nat.mul_le_mul_left (5*r+1) (Nat.succ_le_of_lt hlarge)
    nlinarith only [mul,avg,top,hr]
  rcases show d=r ∨ d=r+1 by omega with deq | deq
  · have nw : W.card=4*r := by omega
    have den := h.rank_four_at_four_rows (by omega) hb ws nw (by omega)
    have price := (prices r (by
      intro D ds rd
      have bound := order_cap h (by omega) (ds.trans_ssubset ws) (q:=3) (by omega)
      omega)).2.1 deq
    rw [deq,Nat.choose_succ_succ' r 1,Nat.choose_one_right] at eq
    nlinarith only [den,price,eq,top,twice_choose_two r,hr]
  · have nw : W.card+1=4*r := by omega
    have den := h.rank_four_one_short (by omega) hb ws nw (by omega)
    have price := (prices (r-1) (by
      intro D ds rd
      have bound := order_cap h (by omega) (ds.trans_ssubset ws) (q:=3) (by omega)
      omega)).2.2 deq
    rw [deq,Nat.choose_succ_succ' (r+1) 1,Nat.choose_succ_succ' r 1,
      Nat.choose_one_right,Nat.choose_one_right] at eq
    nlinarith only [den,price,eq,top,twice_choose_two r,hr,Nat.sub_add_cancel (show 1≤r by omega)]

/-- Every first obstruction on at least 33 colors has independence rank at least six. -/
theorem MinimalObstruction.six_le_of_thirty_three_le {t : ℕ} (h : MinimalObstruction c k t S)
    (hr : 33≤r) (hb : Balanced c) (ht : t<r) : 6≤t := by
  have lower := h.five_le_of_nine_le hb (by omega) ht
  by_contra! small
  obtain rfl : t=5 := by omega
  exact (h.rank_five_lt_thirty_three hb).not_ge hr

/-- In a balanced coloring on at least 33 colors, every set of 5r+1 vertices
contains an independent six-set in every prescribed color. -/
theorem independent_six_in_subset_of_thirty_three_le (hr : 33≤r) (hb : Balanced c)
    (sz : S.card=5*r+1) (k : Fin r) : ∃ I⊆S, (colorGraph c k).IsNIndepSet 6 I := by
  by_contra! failure
  obtain ⟨t,W,small,_,h⟩ := minimalObstruction_of_failure sz failure
  have := h.six_le_of_thirty_three_le hr hb (by omega)
  omega

end Erdos617
