import Erdos617.SquareThreeWitnesses
import Erdos617.RowDescent

namespace Erdos617

open Finset SimpleGraph
open scoped Classical

private theorem square_four_arithmetic (r : ℕ) (hr : 11≤r) :
    ((r-1)^2+1).choose 2 <
      (r-3)*((r-1)*(r-1).choose 2+2*(r-1)-1) +
      (r-5)*(3*r/4+1)+3*(r*(r-2).choose 2+2*(r-2)+1) := by
  obtain ⟨t,rfl⟩ : ∃ t,r=t+5 := ⟨r-5,by omega⟩
  simp only [show t+5-1=t+4 by omega,show t+5-3=t+2 by omega,show t+5-2=t+3 by omega,
    Nat.add_sub_cancel]
  let G := (t+4)*(t+4).choose 2+2*(t+4)-1
  let B := (t+5)*(t+3).choose 2+2*(t+3)
  have gg : G+1=(t+4)*(t+4).choose 2+2*(t+4) := by dsimp [G]; omega
  have budget : ((t+4)^2+1).choose 2=(t+2)*G+3*B+(t+5).choose 2+1 := by
    dsimp [B]
    nlinarith only [twice_choose_two ((t+4)^2+1),twice_choose_two (t+5),
      congrArg (fun n => (t+2)*(t+4)*n) (twice_choose_two (t+4)),
      congrArg (fun n => 3*(t+5)*n) (twice_choose_two (t+3)),congrArg ((t+2)*·) gg]
  change _<(t+2)*G+t*(3*(t+5)/4+1)+3*(B+1)
  rw [budget]
  by_cases eq : t=6
  · subst t
    have z : (6+5).choose 2=55 := by decide
    rw [z]
    omega
  have div : 3*(t+5)+1≤4*(3*(t+5)/4+1) := by omega
  have times := Nat.mul_le_mul_left t div
  have sq := Nat.mul_le_mul_left (t+5) (show 12≤t+5 by omega)
  nlinarith only [times,twice_choose_two (t+5),sq]

/-- If fewer than r−1 colors are avoidable, every hitting color has the
smaller independence bound, excludes a full clique, and pays the Brouwer floor. -/
theorem square_good_color_profile {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (hr : 5≤r) (c : Sym2 V → Fin r) (U : Finset V) (sz : U.card=(r-1)^2+1) (k : Fin r) :
    let s := r-1
    let d := fun e : Sym2 U => c (e.map Subtype.val)
    let bad := univ.filter fun j => ¬HitsPalette d s {j}
    bad.card<r-1 → k∉bad →
      rankOn (colorGraph c k) U≤s ∧ (∀ S⊆U, ¬(colorGraph c k).IsNClique r S) ∧
      s*s.choose 2+2*s-1≤blockEdges (colorGraph c k) U := by
  classical
  intro s d bad few good
  have sr : s+1=r := by dsimp [s]; omega
  have free (k : Fin r) : (colorGraph d k).CliqueFree (s+1) := by
    intro A hA
    have sub : univ.erase k ⊆ bad := by
      intro j' hj'
      refine mem_filter.mpr ⟨mem_univ _,?_⟩
      intro hit
      obtain ⟨x,hx,y,hy,ne,e⟩ := hit A hA.card_eq
      exact (mem_erase.mp hj').1 ((mem_singleton.mp e).symm.trans (hA.isClique hx hy ne).2)
    have lim := card_le_card sub
    simp only [card_erase_of_mem (mem_univ k),card_univ,Fintype.card_fin] at lim
    omega
  have cap : (colorGraph d k).indepNum≤s := by
    apply (hitsPalette_singleton_iff_indepNum d s k).mp
    by_contra miss
    exact good (mem_filter.mpr ⟨mem_univ _,miss⟩)
  refine ⟨?_,?_,?_⟩
  · obtain ⟨I,subI,ind,hI⟩ := exists_max_indep (colorGraph c k) U
    let J := I.subtype (·∈U)
    have eq : J.card=I.card := by simp [J,filter_eq_self.mpr subI]
    have no : (colorGraph d k).IsIndepSet (J : Set U) := by
      intro x hx y hy ne e
      exact ind (mem_subtype.mp hx) (mem_subtype.mp hy) (fun h => ne (Subtype.ext h))
        ⟨fun h => ne (Subtype.ext h),e.2⟩
    have lim := no.card_le_indepNum.trans cap
    omega
  · intro S subS cl
    let T := S.subtype (·∈U)
    apply free k T
    refine ⟨?_,?_⟩
    · intro x hx y hy ne
      exact ⟨ne,(cl.isClique (mem_subtype.mp hx) (mem_subtype.mp hy) (fun a => ne (Subtype.ext a))).2⟩
    · simp [T,filter_eq_self.mpr subS,cl.card_eq,sr]
  · rw [color_blockEdges_eq]
    change _≤(colorGraph d k).edgeFinset.card
    apply edge_bound_of_clique_and_indep_caps _ (by omega : 2≤s)
      (by simpa [pow_two] using (Fintype.card_coe U).trans sz)
      (fun C ind => by have := ind.isIndepSet.card_le_indepNum.trans cap; rw [ind.card_eq] at this; omega) (free k)

/-- A one-step square has four avoidable colors if the hitting colors outside
two exceptions each exceed the Brouwer floor by more than three quarters of r. -/
theorem four_avoidable_of_good_edge_excess {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (hr : 11≤r) (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c)
    (U : Finset V) (sz : U.card=(r-1)^2+1) (i j : Fin r)
    (high : ∀ k, k≠i → k≠j → rankOn (colorGraph c k) U≤r-1 →
      (∀ S⊆U, ¬(colorGraph c k).IsNClique r S) →
      (r-1)*(r-1).choose 2+2*(r-1)-1+3*r/4<blockEdges (colorGraph c k) U) :
    let d := fun e : Sym2 U => c (e.map Subtype.val)
    4≤(univ.filter fun k => ¬HitsPalette d (r-1) {k}).card := by
  classical
  intro d
  let s := r-1
  let bad := univ.filter fun k => ¬HitsPalette d s {k}
  let E (k : Fin r) := (colorGraph d k).edgeFinset.card
  let G := s*s.choose 2+2*s-1
  let B := r*(r-2).choose 2+2*(r-2)
  have sr : s+1=r := by dsimp [s]; omega
  have order : Fintype.card U=s^2+1 := (Fintype.card_coe U).trans sz
  change 4≤bad.card
  by_contra! few
  have all : badᶜ.card+bad.card=r := by simp
  obtain ⟨P,sub,count⟩ := exists_subset_card_eq (s:=badᶜ) (show r-3≤badᶜ.card by omega)
  have pc : Pᶜ.card=3 := by have z := card_compl_add_card P; rw [Fintype.card_fin] at z; omega
  have profile (k : Fin r) (hk : k∈P) :=
    square_good_color_profile (by omega) c U sz k (show bad.card<r-1 by omega) (mem_compl.mp (sub hk))
  have lower (k : Fin r) (h : k∈P) : G≤E k := by
    have low := (profile k h).2.2
    rw [color_blockEdges_eq] at low
    exact low
  let X := (P.erase i).erase j
  have xs : X⊆P := (erase_subset ..).trans (erase_subset ..)
  have enough : r-5≤X.card := by
    have a := pred_card_le_card_erase (s:=P) (a:=i)
    have b := pred_card_le_card_erase (s:=P.erase i) (a:=j)
    dsimp [X]; omega
  have strict (k : Fin r) (hk : k∈X) : G+(3*r/4+1)≤E k := by
    obtain ⟨dj,h⟩ := mem_erase.mp hk
    obtain ⟨di,pk⟩ := mem_erase.mp h
    have bound := high k di dj (profile k pk).1 (profile k pk).2.1
    rw [color_blockEdges_eq] at bound
    change G+3*r/4<E k at bound
    omega
  have extra := sum_le_sum strict
  have rest := sum_le_sum (s:=P\X) (f:=fun _ => G) (g:=E) fun k hk => lower k (mem_sdiff.mp hk).1
  have others := sum_le_sum (s:=Pᶜ) (f:=fun _ => B+1) (g:=E) fun k _ =>
    strict_square_turan_floor (by omega) hn c hb U sz k
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,pc] at extra rest others
  have np := card_sdiff_add_card_eq_card xs
  have component := sum_sdiff xs (f:=E)
  have split := sum_add_sum_compl P E
  change _=∑ k,(colorGraph d k).edgeFinset.card at split
  rw [sum_color_edges,order] at split
  have numeric := square_four_arithmetic r hr
  change (s^2+1).choose 2<(r-3)*G+(r-5)*(3*r/4+1)+3*(B+1) at numeric
  have sumg := congrArg (·*G) (np.trans count)
  rw [Nat.add_mul] at sumg
  rw [Nat.mul_add] at extra
  have plus := Nat.mul_le_mul_right (3*r/4+1) enough
  omega

/-- Two transverse full rows whose deletion leaves an exact square with the
corresponding rank bounds in both directions. -/
theorem exists_two_line_square {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (hr : 5≤r) (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c) :
    ∃ (i j : Fin r) (C D : Finset V), i≠j ∧ (colorGraph c i).IsNClique r C ∧
      (colorGraph c j).IsNClique r D ∧ (C∩D).card=1 ∧
      (C∪D)ᶜ.card=(r-1)^2+1 ∧ rankOn (colorGraph c i) (C∪D)ᶜ≤r-1 ∧
      rankOn (colorGraph c j) (C∪D)ᶜ≤r-1 := by
  classical
  obtain ⟨Q,hQ,total,cross⟩ := exists_transversal_full_rows hr hn c hb
  let T := univ.filter fun k => (Q k).Nonempty
  have two : 1<T.card := by
    by_contra! few
    have large := sum_le_sum (s:=T) (g:=fun _ => r) fun k _ => Nat.le_of_add_left_le (hQ k).residual
    have small := sum_le_sum (s:=Tᶜ) (g:=fun _ => 0) (f:=fun k => (Q k).card) fun k hk => by
      by_contra! positive
      exact (mem_compl.mp hk) (mem_filter.mpr ⟨mem_univ _,card_pos.mp positive⟩)
    have split := sum_add_sum_compl T (fun k => (Q k).card)
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_zero] at large small
    have := Nat.mul_le_mul_right r few
    omega
  obtain ⟨i,hi,j,hj,ne⟩ := one_lt_card.mp two
  obtain ⟨C,hC⟩ := (mem_filter.mp hi).2
  obtain ⟨D,hD⟩ := (mem_filter.mp hj).2
  have geom := row_square_restriction ne ((hQ i).subfamily (singleton_subset_iff.mpr hC))
    ((hQ j).subfamily (singleton_subset_iff.mpr hD)) (card_singleton C) (card_singleton D) hn
  have eq : (univ \ C) ∩ (univ \ D)=(C∪D)ᶜ := by ext; simp
  simp only [Finset.singleton_biUnion,id_eq,eq] at geom
  exact ⟨i,j,C,D,ne,(hQ i).full C hC,(hQ j).full D hD,cross i j ne C hC D hD,geom⟩

end Erdos617
