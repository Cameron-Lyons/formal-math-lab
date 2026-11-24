import Erdos617.RowDescent
import Erdos617.QuadraticObstruction

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ} {c : Sym2 V → Fin r}

/-- Every subfamily of rank-one partition atoms can be deleted simultaneously. -/
theorem rank_one_rows_removable (G : SimpleGraph V) (P : Finset (Finset V))
    (hu : P.biUnion id=univ) (dis : (↑P : Set (Finset V)).PairwiseDisjoint id)
    (cap : (∑ B∈P,rankOn G B)≤r) :
    let Q := P.filter fun B => rankOn G B=1
    (↑Q : Set (Finset V)).PairwiseDisjoint id ∧ (∀ B∈Q,G.IsClique (B : Set V)) ∧
      ∀ R⊆Q, rankOn G (univ \ R.biUnion id)+R.card≤r := by
  classical
  intro Q
  have qsub : Q⊆P := filter_subset ..
  have qrank {R : Finset (Finset V)} (sub : R⊆Q) : (∑ B∈R,rankOn G B)=R.card := by
    calc
      _ = ∑ _∈R,1 := sum_congr rfl (fun B hB => (mem_filter.mp (sub hB)).2)
      _ = R.card := by simp
  refine ⟨fun _ ha _ hb ne => dis (qsub ha) (qsub hb) ne,
    fun B hB => rank_one_clique G (mem_filter.mp hB).2,?_⟩
  intro R sub
  have outside : univ \ R.biUnion id ⊆ (P\R).biUnion id := by
    intro x hx
    have hm := mem_univ x
    rw [←hu] at hm
    obtain ⟨B,hB,hxB⟩ := mem_biUnion.mp hm
    exact mem_biUnion.mpr ⟨B,mem_sdiff.mpr ⟨hB,fun hq => (mem_sdiff.mp hx).2
      (mem_biUnion.mpr ⟨B,hq,hxB⟩)⟩,hxB⟩
  have limit := (rankOn_mono G outside).trans (rankOn_biUnion_le G _)
  have sums := sum_sdiff (sub.trans qsub) (f:=rankOn G)
  rw [qrank sub] at sums
  have counts := cap
  change rankOn G (univ \ R.biUnion id)+R.card≤r
  omega

/-- The rank-one atoms of all colors. Every subfamily consists of disjoint cliques
and lowers the rank of its complement by its cardinality. -/
theorem rank_one_palette_count (hr : 3≤r) (hn : Fintype.card V=r^2+1) (hb : Balanced c)
    (g : ℕ) (hg : 4≤g)
    (no : ∀ (k : Fin r) (t : ℕ) (W : Finset V), MinimalObstruction c k t W → t<r → g≤t) :
    ∃ Q : Fin r → Finset (Finset V),
      (∀ k, (↑(Q k) : Set (Finset V)).PairwiseDisjoint id ∧
        (∀ B∈Q k,(colorGraph c k).IsClique (B : Set V)) ∧
        ∀ R⊆Q k, rankOn (colorGraph c k) (univ \ R.biUnion id)+R.card≤r) ∧
      r*(g-2) ≤ ∑ k,(Q k).card := by
  classical
  obtain ⟨k₀,t₀,W₀,_,ht₀,h₀⟩ := exists_minimalObstruction_ceil_half hr hn c hb
  have gr : g≤r := by have := no k₀ t₀ W₀ h₀ (by omega); omega
  let G := colorGraph c
  choose P hu dis atoms add using fun k : Fin r => exists_rank_partition (G k) univ
  let Q (k : Fin r) := (P k).filter fun B => rankOn (G k) B=1
  have cap (k : Fin r) : (∑ B∈P k,rankOn (G k) B)≤r :=
    (add k).le.trans ((rankOn_univ_eq_indepNum (G k)).le.trans (balanced_indepNum_le c hb k))
  refine ⟨Q,fun k => rank_one_rows_removable (G k) (P k) (hu k) (dis k) (cap k),?_⟩
  have atleast (k : Fin r) :
      2*(P k).card+g ≤ (Q k).card+r+2 := by
    have n := card_biUnion (dis k)
    simp only [id_eq,hu k,card_univ,hn] at n
    obtain ⟨A,ha,large⟩ : ∃ A∈P k, rankOn (G k) A*r<A.card := by
      by_contra! small
      have bound := sum_le_sum small
      rw [←n,←sum_mul,pow_two] at bound
      have := Nat.mul_le_mul_right r (cap k)
      omega
    have ra : g≤rankOn (G k) A := by
      by_cases full : r≤rankOn (G k) A
      · exact gr.trans full
      obtain ⟨W,hW,nW⟩ := exists_subset_card_eq (s:=A) (Nat.succ_le_of_lt large)
      have free (I : Finset V) (iw : I⊆W) (ind : (G k).IsNIndepSet (rankOn (G k) A+1) I) : False := by
        have sized := card_le_rankOn _ (iw.trans hW) ind.isIndepSet
        rw [ind.card_eq] at sized
        omega
      obtain ⟨t,T,le,_,h⟩ := minimalObstruction_of_failure (c:=c) (k:=k) nW free
      exact (no k t T h (by omega)).trans le
    let w (B : Finset V) := if rankOn (G k) B=1 then 1 else 0
    have pt (B : Finset V) (hB : B∈(P k).erase A) : 2 ≤ rankOn (G k) B+w B := by
      have low := (atoms k B (mem_of_mem_erase hB)).rank_pos
      dsimp [w]; split <;> omega
    have summed := sum_le_sum pt
    simp only [sum_const,sum_add_distrib,nsmul_eq_mul,Nat.cast_id,card_erase_of_mem ha] at summed
    have counts := sum_le_sum_of_subset_of_nonneg (erase_subset A (P k)) (f:=w) (by simp)
    have tot : (∑ B∈P k,w B)=(Q k).card := by simp [w,Q,sum_boole]
    rw [tot] at counts
    have cut := sum_erase_add (P k) (rankOn (G k)) ha
    have rtot := cap k
    omega
  have density (k : Fin r) : r*(r^2+1)≤(G k).edgeFinset.card+(r.choose 2+1)*r+(r-1)*(P k).card := by
    have d := rank_partition_density (G k) (P k) (dis k) (atoms k) r
    rw [hu k,card_univ,hn,blockEdges_univ] at d
    have := Nat.mul_le_mul_left (r.choose 2+1) (cap k)
    omega
  let p := ∑ k,(P k).card
  have pf : r*r≤2*p := by
    have flo := sum_le_sum (s:=univ) fun k _ => density k
    simp only [sum_add_distrib,sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin,Nat.cast_id,←mul_sum] at flo
    have e : (∑ k,(G k).edgeFinset.card)=(r^2+1).choose 2 := (sum_color_edges c).trans (by rw [hn])
    rw [e] at flo
    change _≤_+_+(r-1)*p at flo
    have ch := congrArg ((r*r)*·) (twice_choose_two r)
    have pair := twice_choose_two (r^2+1)
    have pred := congrArg ((r*r)*·) (Nat.sub_add_cancel (show 1≤r by omega))
    apply Nat.le_of_mul_le_mul_right (c:=r-1) _ (by omega)
    nlinarith only [flo,ch,pair,pred]
  have global := sum_le_sum (s:=univ) fun k _ => atleast k
  simp only [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin,Nat.cast_id] at global
  change 2*p+r*g≤((∑ k,(Q k).card)+r*r)+r*2 at global
  have sub := congrArg (r*·) (Nat.sub_add_cancel (show 2≤g by omega))
  rw [Nat.mul_add] at sub
  omega

/-- A global count of clique components forces simultaneous subfamilies of a given size. -/
theorem rank_one_families_of_count {m : ℕ} (hr : 0<r) (hm : 2≤m) (F : Fin r → Finset (Finset V))
    (rows : ∀ k, (↑(F k) : Set (Finset V)).PairwiseDisjoint id ∧
      (∀ B∈F k,(colorGraph c k).IsClique (B : Set V)) ∧
      ∀ R⊆F k, rankOn (colorGraph c k) (univ \ R.biUnion id)+R.card≤r)
    (count : r*m≤∑ k,(F k).card) :
    ∃ (i j : Fin r) (P Q : Finset (Finset V)), i≠j ∧ P.card=m ∧ Q.card=m ∧
      (↑P : Set (Finset V)).PairwiseDisjoint id ∧ (↑Q : Set (Finset V)).PairwiseDisjoint id ∧
      (∀ A∈P,(colorGraph c i).IsClique (A : Set V)) ∧ (∀ A∈Q,(colorGraph c j).IsClique (A : Set V)) ∧
      rankOn (colorGraph c i) (univ \ P.biUnion id) ≤ r-m ∧
      rankOn (colorGraph c j) (univ \ Q.biUnion id) ≤ r-m := by
  classical
  let T := univ.filter fun j => m≤(F j).card
  have many : 1<T.card := by
    by_contra! few
    have large := sum_le_sum (s:=T) (g:=fun _ => r) fun j _ =>
      Nat.le_of_add_left_le ((rows j).2.2 (F j) Subset.rfl)
    have small := sum_le_sum (s:=Tᶜ) (g:=fun _ => m-1) fun j hj => (by
      have notmem := mem_compl.mp hj
      change j∉univ.filter _ at notmem
      simp only [mem_filter,mem_univ,true_and,not_le] at notmem
      omega : (F j).card≤m-1)
    have split := sum_add_sum_compl T (fun j => (F j).card)
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at large small
    have card := card_add_card_compl T
    simp only [Fintype.card_fin] at card
    have pred : m=(m-1)+1 := by omega
    rw [pred,Nat.mul_add,Nat.mul_one] at count
    rcases show T.card=0 ∨ T.card=1 by omega with em|one
    · rw [em,zero_mul] at large
      have ratio := congrArg (·*(m-1)) (show Tᶜ.card=r by omega)
      omega
    · rw [one,one_mul] at large
      have ratio := congrArg (·*(m-1)) (show Tᶜ.card+1=r by omega)
      rw [Nat.add_mul,Nat.one_mul] at ratio
      omega
  obtain ⟨i,hi,j,hj,ne⟩ := one_lt_card.mp many
  obtain ⟨P,hP,np⟩ := exists_subset_card_eq (mem_filter.mp hi).2
  obtain ⟨Q,hQ,nq⟩ := exists_subset_card_eq (mem_filter.mp hj).2
  have ci := (rows i).2.2 P hP
  have cj := (rows j).2.2 Q hQ
  exact ⟨i,j,P,Q,ne,np,nq,fun _ ha _ hb ne => (rows i).1 (hP ha) (hP hb) ne,
    fun _ ha _ hb ne => (rows j).1 (hQ ha) (hQ hb) ne,
    fun A ha => (rows i).2.1 A (hP ha),fun A ha => (rows j).2.1 A (hQ ha),by omega,by omega⟩

/-- Two colors simultaneously have g−2 removable clique components each. -/
theorem exists_rank_one_families (hr : 3≤r) (hn : Fintype.card V=r^2+1) (hb : Balanced c)
    (g : ℕ) (hg : 4≤g)
    (no : ∀ (k : Fin r) (t : ℕ) (W : Finset V), MinimalObstruction c k t W → t<r → g≤t) :
    ∃ (i j : Fin r) (P Q : Finset (Finset V)), i≠j ∧ P.card=g-2 ∧ Q.card=g-2 ∧
      (↑P : Set (Finset V)).PairwiseDisjoint id ∧ (↑Q : Set (Finset V)).PairwiseDisjoint id ∧
      (∀ A∈P,(colorGraph c i).IsClique (A : Set V)) ∧ (∀ A∈Q,(colorGraph c j).IsClique (A : Set V)) ∧
      rankOn (colorGraph c i) (univ \ P.biUnion id) ≤ r-(g-2) ∧
      rankOn (colorGraph c j) (univ \ Q.biUnion id) ≤ r-(g-2) := by
  obtain ⟨F,rows,count⟩ := rank_one_palette_count hr hn hb g hg no
  exact rank_one_families_of_count (by omega) (by omega) F rows count

end Erdos617
