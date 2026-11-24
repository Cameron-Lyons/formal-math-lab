import Erdos617.SquareFourWitnesses

namespace Erdos617

open Finset SimpleGraph
open scoped Classical

/-- Difference of the two one-color floors, and their palette budget on a square. -/
private theorem square_floor_budget (r : ℕ) (hr : 2≤r) :
    let s := r-1
    let G := s*s.choose 2+2*s-1
    let B := r*(r-2).choose 2+2*(r-2)
    G=B+r.choose 2 ∧ (s^2+1).choose 2+2*r.choose 2=r*G+1 := by
  obtain ⟨a,rfl⟩ : ∃ a,r=a+2 := ⟨r-2,by omega⟩
  intro s G B
  have ss : s=a+1 := by dsimp [s]
  have gg : G+1=s*s.choose 2+2*s := by dsimp [G]; omega
  rw [ss] at gg ⊢
  dsimp only [B]
  rw [Nat.add_sub_cancel]
  exact ⟨by nlinarith only [twice_choose_two (a+2),gg,congrArg ((a+2)*·) (twice_choose_two a),
    congrArg ((a+1)*·) (twice_choose_two (a+1))],
    by nlinarith only [twice_choose_two ((a+1)^2+1),twice_choose_two (a+2),
      congrArg ((a+2)*·) gg,congrArg (fun z => (a+2)*(a+1)*z) (twice_choose_two (a+1))]⟩

private theorem half_budget_arithmetic (r b x : ℕ) (sparse : 10*(b+1)≤r)
    (square : (b+2)^2≤r) (many : r≤x+b+2) :
    b*r.choose 2+1<x*((b/2)*(r-2)+1)+2*r.choose 2 := by
  generalize hq : b/2=q at ⊢
  have edge := twice_choose_two r
  have times := congrArg (b*·) edge
  have p : 2≤r := by omega
  zify [p] at edge times square ⊢
  by_cases bz : b=0
  · subst b; have qzero : q=0 := by omega
    subst q; simp only [Nat.cast_zero,zero_mul,zero_add] at *
    omega
  have lo : 0≤((x:ℤ)+b+2-r)*((r:ℤ)-2)*((b:ℤ)-1) :=
    mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)
  have rounded : 0≤(2*(q:ℤ)+1-b)*x*((r:ℤ)-2) :=
    mul_nonneg (mul_nonneg (by omega) (by positivity)) (by omega)
  have wide : 0≤(r:ℤ)*(r-((b:ℤ)+2)^2) := mul_nonneg (by positivity) (by omega)
  nlinarith only [edge,times,lo,rounded,wide,sq_nonneg (b:ℤ),
    show (0:ℤ)<r by omega,show (0:ℤ)<x by omega,show (0:ℤ)<b by omega,
    mul_nonneg (show (0:ℤ)≤b by positivity) (show (0:ℤ)≤r by positivity)]

/-- Select a hitting color whenever the total cost of the other eligible
colors would exceed the available edge count. -/
private theorem select_good_color {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c)
    (U : Finset V) (sz : U.card=(r-1)^2+1) (i j : Fin r) (f : ℕ → ℕ) :
    let d := fun e : Sym2 U => c (e.map Subtype.val)
    let b := (univ.filter fun k => ¬HitsPalette d (r-1) {k}).card
    10*(b+1)≤r →
    (∀ x, r≤x+b+2 → b*r.choose 2+1<x*(f b*(r-2)+1)+2*r.choose 2) → ∃ k : Fin r, k≠i ∧ k≠j ∧ rankOn (colorGraph c k) U≤r-1 ∧
      (∀ S⊆U, ¬(colorGraph c k).IsNClique r S) ∧
      blockEdges (colorGraph c k) U≤(r-1)*(r-1).choose 2+2*(r-1)-1+f b*(r-2) := by
  classical
  intro d b sparse cost
  let s := r-1
  let bad := univ.filter fun j => ¬HitsPalette d s {j}
  let P := badᶜ
  let X := (P.erase i).erase j
  let G := s*s.choose 2+2*s-1
  let B := r*(r-2).choose 2+2*(r-2)
  let E (k : Fin r) := blockEdges (colorGraph c k) U
  have profile (k : Fin r) (hk : k∈P) :=
    square_good_color_profile (by omega) c U sz k (show bad.card<r-1 by change b<r-1; omega) (mem_compl.mp hk)
  have count : P.card+b=r := by simpa only [Fintype.card_fin] using card_compl_add_card bad
  have xs : X⊆P := (erase_subset ..).trans (erase_subset ..)
  have many : r≤X.card+b+2 := by
    have a := pred_card_le_card_erase (s:=P) (a:=i)
    have b' := pred_card_le_card_erase (s:=P.erase i) (a:=j)
    dsimp [X]; omega
  have extract : ∃ k∈X, E k≤G+f b*(r-2) := by
    by_contra! strict
    have extra := sum_le_sum (s:=X) (f:=fun _ => G+(f b*(r-2)+1)) (g:=E) (fun k hk => by have := strict k hk; omega)
    have rest := sum_le_sum (s:=P\X) (f:=fun _ => G) (g:=E) fun k hk => (profile k (mem_sdiff.mp hk).1).2.2
    have other := sum_le_sum (s:=Pᶜ) (f:=fun _ => B) (g:=E) fun k _ => by
      have bound := strict_square_turan_floor (by omega) hn c hb U sz k
      change B<(colorGraph d k).edgeFinset.card at bound
      change B≤blockEdges (colorGraph c k) U
      rw [color_blockEdges_eq]
      exact Nat.le_of_lt bound
    have pc : Pᶜ.card=b := by simp [P,bad,b,s]
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id,pc] at extra rest other
    have component := sum_sdiff xs (f:=E)
    have split := sum_add_sum_compl P E
    have total : (∑ k,E k)=(s^2+1).choose 2 := by
      simp only [E,color_blockEdges_eq]
      change (∑ k,(colorGraph d k).edgeFinset.card)=_
      rw [sum_color_edges,Fintype.card_coe,sz]
    rw [total] at split
    have num := congrArg (·*G) (card_sdiff_add_card_eq_card xs)
    have sumg := congrArg (·*G) count
    rw [Nat.add_mul] at num sumg
    have ⟨floor_eq,id⟩ := square_floor_budget r (by omega)
    change G=B+r.choose 2 at floor_eq
    change (s^2+1).choose 2+2*r.choose 2=r*G+1 at id
    have prod := congrArg (b*·) floor_eq
    rw [Nat.mul_add] at prod extra
    have arithmetic := cost X.card many
    omega
  obtain ⟨k,hk,small⟩ := extract
  obtain ⟨nj,hk'⟩ := mem_erase.mp hk
  obtain ⟨ni,pk⟩ := mem_erase.mp hk'
  exact ⟨k,ni,nj,(profile k pk).1,(profile k pk).2.1,small⟩

/-- When only b colors can be avoided, at least one of the remaining colors
outside two named directions has at most ⌊b/2⌋(r−2) edges above the Brouwer floor
when r is at least (b+2)². -/
theorem exists_budgeted_good_color {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c)
    (U : Finset V) (sz : U.card=(r-1)^2+1) (i j : Fin r) :
    let d := fun e : Sym2 U => c (e.map Subtype.val)
    let b := (univ.filter fun k => ¬HitsPalette d (r-1) {k}).card
    10*(b+1)≤r → (b+2)^2≤r → ∃ k : Fin r, k≠i ∧ k≠j ∧ rankOn (colorGraph c k) U≤r-1 ∧
      (∀ S⊆U, ¬(colorGraph c k).IsNClique r S) ∧
      blockEdges (colorGraph c k) U≤(r-1)*(r-1).choose 2+2*(r-1)-1+(b/2)*(r-2) := by
  intro d b sparse square
  exact select_good_color hn c hb U sz i j (fun n => n/2) sparse
    (fun x many => half_budget_arithmetic r b x sparse square many)

private theorem linear_budget_arithmetic (r b x : ℕ) (sparse : 10*(b+1)≤r)
    (many : r≤x+b+2) :
    b*r.choose 2+1<x*((3*b/5)*(r-2)+1)+2*r.choose 2 := by
  have edge := twice_choose_two r
  have large : 1<r.choose 2 := by
    have sq := Nat.mul_le_mul_right r (by omega : 3≤r)
    nlinarith only [sq,edge,sparse,Nat.zero_le b]
  by_cases lo : b≤1
  · have := Nat.mul_le_mul_right (r.choose 2) lo
    omega
  have cap : 5*r.choose 2≤3*x*(r-2) := by
    have p : 2≤r := by omega
    zify [p] at edge ⊢
    have room : 0≤(10*(x:ℤ)+10-9*r)*((r:ℤ)-2) := mul_nonneg (by omega) (by omega)
    have rs : 0≤(r:ℤ)*(r-30) := mul_nonneg (by positivity) (by omega)
    nlinarith only [room,rs,edge,show (0:ℤ)≤r by positivity]
  have frac : 3*(b-2)≤5*(3*b/5) := by omega
  have budget : (b-2)*r.choose 2≤x*((3*b/5)*(r-2)) := by
    nlinarith only [Nat.mul_le_mul_left (b-2) cap,Nat.mul_le_mul_right (x*(r-2)) frac]
  have sum := congrArg (·*r.choose 2) (Nat.sub_add_cancel (by omega : 2≤b))
  rw [Nat.add_mul] at sum
  nlinarith only [budget,sum,show 1<x by omega]

/-- When only b colors can be avoided, at least one of the remaining colors
outside two named directions has at most ⌊3b/5⌋(r−2) edges above the Brouwer floor
whenever 10(b+1)≤r. -/
theorem exists_linear_budgeted_good_color {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c)
    (U : Finset V) (sz : U.card=(r-1)^2+1) (i j : Fin r) :
    let d := fun e : Sym2 U => c (e.map Subtype.val)
    let b := (univ.filter fun k => ¬HitsPalette d (r-1) {k}).card
    10*(b+1)≤r → ∃ k : Fin r, k≠i ∧ k≠j ∧ rankOn (colorGraph c k) U≤r-1 ∧
      (∀ S⊆U, ¬(colorGraph c k).IsNClique r S) ∧
      blockEdges (colorGraph c k) U≤(r-1)*(r-1).choose 2+2*(r-1)-1+(3*b/5)*(r-2) := by
  intro d b sparse
  exact select_good_color hn c hb U sz i j (fun n => 3*n/5) sparse
    (fun x many => linear_budget_arithmetic r b x sparse many)

/-- When only b colors can be avoided, at least one of the remaining colors
outside two named directions has at most ⌊33b/64⌋(r−2) edges above the Brouwer floor
whenever 33b+100≤r. -/
theorem exists_good_color_for_linear_contradiction {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c)
    (U : Finset V) (sz : U.card=(r-1)^2+1) (i j : Fin r) :
    let d := fun e : Sym2 U => c (e.map Subtype.val)
    let b := (univ.filter fun k => ¬HitsPalette d (r-1) {k}).card
    33*b+100≤r → ∃ k : Fin r, k≠i ∧ k≠j ∧ rankOn (colorGraph c k) U≤r-1 ∧
      (∀ S⊆U, ¬(colorGraph c k).IsNClique r S) ∧
      blockEdges (colorGraph c k) U≤(r-1)*(r-1).choose 2+2*(r-1)-1+(33*b/64)*(r-2) := by
  intro d b tall
  apply select_good_color hn c hb U sz i j (fun n => 33*n/64) (show 10*(b+1)≤r by omega)
  intro x many
  change r≤x+b+2 at many
  change b*r.choose 2+1<x*((33*b/64)*(r-2)+1)+2*r.choose 2
  have edge := twice_choose_two r
  have large : 1<r.choose 2 := by
    have sq := Nat.mul_le_mul_right r (by omega : 3≤r)
    nlinarith only [sq,edge,tall,Nat.zero_le b]
  by_cases lo : b≤1
  · have := Nat.mul_le_mul_right (r.choose 2) lo
    omega
  have capacity : 64*r.choose 2 ≤ 33*x*(r-2) := by
    have mult := Nat.mul_le_mul_right (r-2) (show 32*r+34≤33*x by omega)
    have rp := congrArg ((32*r+34)*·) (Nat.sub_add_cancel (show 2≤r by omega))
    nlinarith only [edge,mult,rp,tall,Nat.zero_le b]
  have fit : 33*(b-2)≤64*(33*b/64) := by omega
  have paid : (b-2)*r.choose 2≤x*((33*b/64)*(r-2)) := by
    nlinarith only [Nat.mul_le_mul_left (b-2) capacity,Nat.mul_le_mul_right (x*(r-2)) fit]
  have sum := congrArg (·*r.choose 2) (Nat.sub_add_cancel (by omega : 2≤b))
  rw [Nat.add_mul] at sum
  nlinarith only [paid,sum,show 1<x by omega]

end Erdos617
