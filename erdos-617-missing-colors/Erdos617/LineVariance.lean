import Erdos617.RowDescent
import Erdos617.DeletionRank
import Mathlib.Tactic.Positivity

namespace Erdos617

open Finset SimpleGraph

/-- The variance about r times the rank pays for the number of small parts. -/
private theorem part_variance (a b r e : ℕ) (ha : 0<a)
    (en : 2*b^2≤a*(2*e+r*b)) (one : a=1 → b<r) (two : a=2 → b<2*r)
    (small : a≤4 → b≤a*r) :
    (9*r+8)*b+21 ≤ 6*e+(6*r^2+8*r+7)*a := by
  have ene : 2*(b:ℤ)^2≤(a:ℤ)*(2*(e:ℤ)+(r:ℤ)*b) := by exact_mod_cast en
  let z : ℤ := b-(r:ℤ)*a
  have var : 8*(a:ℤ)*z+21*a ≤ 6*z^2+7*(a:ℤ)^2 := by
    by_cases big : 5≤a
    · have pos : (0:ℤ)≤(a:ℤ)*(13*a-63) := mul_nonneg (by positivity) (by omega)
      nlinarith only [sq_nonneg (3*z-2*a),pos]
    have za : z≤0 := by
      have h := small (by omega)
      have z' : (b:ℤ)≤(a:ℤ)*r := by exact_mod_cast h
      dsimp [z]; nlinarith only [z']
    by_cases eq : a=1
    · have h := one eq
      have lo : z≤-1 := by dsimp [z]; rw [eq]; simp; omega
      have qq := mul_nonneg_of_nonpos_of_nonpos (show z+1≤0 by omega) (show z-1≤0 by omega)
      rw [eq]; norm_num; nlinarith only [qq,lo]
    by_cases eq2 : a=2
    · have h := two eq2
      have lo : z≤-1 := by dsimp [z]; rw [eq2]; simp; omega
      rw [eq2]; norm_num; nlinarith only [sq_nonneg z,lo]
    have hpos : (0:ℤ)≤(a:ℤ)*(a-3) := mul_nonneg (by positivity) (by omega)
    have hneg : (a:ℤ)*z ≤0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) za
    nlinarith only [hpos,hneg,sq_nonneg z]
  have positive : 0 < (a:ℤ) := by omega
  have times : (a:ℤ)*((9*(r:ℤ)+8)*b+21) ≤ a*(6*(e:ℤ)+(6*(r:ℤ)^2+8*r+7)*a) := by
    dsimp [z] at var
    nlinarith only [ene,var]
  exact_mod_cast (le_of_mul_le_mul_left times positive)

/-- Local clique energy on a rank part without an r-clique. -/
theorem no_full_part_energy {V : Type*} [DecidableEq V] {r p : ℕ} {c : Sym2 V → Fin p}
    {k : Fin p} (hr : 0<r) {B : Finset V} (clfree : ∀ C⊆B, ¬(colorGraph c k).IsNClique r C) :
    2*B.card^2≤rankOn (colorGraph c k) B*(2*blockEdges (colorGraph c k) B+r*B.card) := by
  classical
  let cp := fun e : Sym2 B => c (Sym2.map Subtype.val e)
  let G := colorGraph cp k
  have cap : G.indepNum≤rankOn (colorGraph c k) B := by
    obtain ⟨I,hi⟩ := G.exists_isNIndepSet_indepNum
    obtain ⟨J,sub,hJ⟩ := lift_independent_subset c k B ⟨I,hi⟩
    exact hJ.card_eq ▸ card_le_rankOn _ sub hJ.isIndepSet
  let incl := Function.Embedding.subtype (·∈B)
  have nc (C : Finset B) (hC : G.IsClique (C : Set B)) : C.card≤r-1 := by
    by_contra! high
    obtain ⟨D,sub,sz⟩ := exists_subset_card_eq (s:=C) (show r≤C.card by omega)
    apply clfree (D.map incl) (fun _ hx => D.property_of_mem_map_subtype hx)
    refine ⟨?_,(card_map ..).trans sz⟩
    intro x hx y hy ne
    obtain ⟨u,hu,rfl⟩ := mem_map.mp hx
    obtain ⟨v,hv,rfl⟩ := mem_map.mp hy
    exact ⟨ne,(hC (sub hu) (sub hv) (fun e => ne (congrArg incl e))).2⟩
  have bound := (card_square_le_local_clique_energy G (fun _ => r-1) (fun C hC _ _ => nc C hC)).trans
    (Nat.mul_le_mul_right _ cap)
  rw [G.sum_degrees_eq_twice_card_edges,sum_const,nsmul_eq_mul,card_univ,Fintype.card_coe] at bound
  have id : B.card+B.card*(r-1)=r*B.card := by rw [Nat.add_comm,←Nat.mul_succ,show (r-1).succ=r by omega,Nat.mul_comm]
  rw [color_blockEdges_eq]
  change 2*B.card^2≤rankOn (colorGraph c k) B*(2*G.edgeFinset.card+r*B.card)
  simpa only [Nat.cast_id,Nat.add_assoc,id] using bound

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ} {c : Sym2 V → Fin r} {k : Fin r}

/-- The full-clique rows of a specific rank partition. -/
private theorem rows_from_partition (P : Finset (Finset V)) (hu : P.biUnion id=univ)
    (hd : (↑P : Set (Finset V)).PairwiseDisjoint id)
    (hi : ∀ B∈P,RankInseparable (colorGraph c k) B)
    (ranks : ∑ B∈P,rankOn (colorGraph c k) B≤r) :
    FullCliqueRows c k (P.filter fun B => (colorGraph c k).IsNClique r B) := by
  classical
  let G := colorGraph c k
  let Q := P.filter fun B => G.IsNClique r B
  have sub : Q⊆P := filter_subset ..
  have rankQ : ∑ B∈Q,rankOn G B=Q.card := by
    calc
      _ = ∑ _∈Q,1 := sum_congr rfl (fun B hB => le_antisymm
        (rank_clique_le_one G (show G.IsNClique r B from (mem_filter.mp hB).2).isClique) (hi B (sub hB)).rank_pos)
      _ = _ := by simp
  have outside : univ \ Q.biUnion id ⊆ (P\Q).biUnion id := by
    intro x hx
    have hm := mem_univ x
    rw [←hu] at hm
    obtain ⟨B,hB,hxB⟩ := mem_biUnion.mp hm
    exact mem_biUnion.mpr ⟨B,mem_sdiff.mpr ⟨hB,fun hq => (mem_sdiff.mp hx).2
      (mem_biUnion.mpr ⟨B,hq,hxB⟩)⟩,hxB⟩
  have cap := (rankOn_mono G outside).trans (rankOn_biUnion_le G _)
  have sum := sum_sdiff sub (f:=rankOn G)
  rw [rankQ] at sum
  refine ⟨fun _ ha _ hb ne => hd (sub ha) (sub hb) ne,fun _ hb => (mem_filter.mp hb).2,?_⟩
  change rankOn G (univ \ Q.biUnion id)+Q.card≤r
  change ∑ B∈P,rankOn G B≤r at ranks
  omega

private theorem atom_line_budget (hr : 9≤r) (hb : Balanced c)
    (B : Finset V) (hi : RankInseparable (colorGraph c k) B) (rank : rankOn (colorGraph c k) B<r) :
    (9*r+8)*B.card+21 ≤ 6*blockEdges (colorGraph c k) B+(6*r^2+8*r+7)*rankOn (colorGraph c k) B+
      (if (colorGraph c k).IsNClique r B then 3*r+14 else 0) := by
  classical
  let G := colorGraph c k
  by_cases full : G.IsNClique r B
  · have a : rankOn G B=1 := le_antisymm (rank_clique_le_one G full.isClique) hi.rank_pos
    have e : blockEdges G B=r.choose 2 := by
      unfold blockEdges
      have top := G.induce_eq_top.mpr full.isClique
      have hh : (G.induce (B : Set V)).edgeFinset=(⊤ : SimpleGraph B).edgeFinset := by
        ext e; rw [mem_edgeFinset,mem_edgeFinset,top]; rfl
      rw [hh,card_edgeFinset_top_eq_card_choose_two,Fintype.card_coe,full.card_eq]
    change (9*r+8)*B.card+21≤6*blockEdges G B+(6*r^2+8*r+7)*rankOn G B+(if G.IsNClique r B then 3*r+14 else 0)
    simp only [full,ite_true,full.card_eq,a,e]
    nlinarith only [twice_choose_two r]
  have no (C : Finset V) (sub : C⊆B) : ¬G.IsNClique r C := by
    intro cl
    by_cases one : rankOn G B=1
    · have clique := rank_one_clique G one
      have bound := balanced_clique_cap c hb k (by omega) clique
      exact full ⟨clique,le_antisymm bound (cl.card_eq ▸ card_le_card sub)⟩
    exact hi.no_full_clique hb (by change 1<rankOn G B; have := hi.rank_pos; change 0<rankOn G B at this; omega) rank sub cl
  have one (eq : rankOn G B=1) : B.card<r := by
    have clique := rank_one_clique G eq
    exact lt_of_le_of_ne (balanced_clique_cap c hb k (by omega) clique) (fun equal => full ⟨clique,equal⟩)
  have two (eq : rankOn G B=2) : B.card<2*r :=
    rank_two_clique_free_card_lt hb (by omega) no eq.le
  have small (lim : rankOn G B≤4) : B.card≤rankOn G B*r :=
    local_rank_cap (s:=4) (fun a ha S h => by have le := h.five_le_of_nine_le hb hr (by omega); omega) B lim
  change (9*r+8)*B.card+21≤6*blockEdges G B+(6*r^2+8*r+7)*rankOn G B+(if G.IsNClique r B then 3*r+14 else 0)
  simp only [full,ite_false,Nat.add_zero]
  exact part_variance _ _ _ _ hi.rank_pos (no_full_part_energy (by omega) no) one two small

/-- Separate contributions from the number of rank components and their full cliques. -/
private theorem line_partition_estimates (hr : 9≤r) (hn : Fintype.card V=r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r) :
    ∃ (p : ℕ) (Q : Finset (Finset V)), FullCliqueRows c k Q ∧
      r*Fintype.card V ≤ (colorGraph c k).edgeFinset.card+(r.choose 2+1)*r+(r-1)*p ∧
      (9*r+8)*Fintype.card V+21*p ≤ 6*(colorGraph c k).edgeFinset.card+(6*r^2+8*r+7)*r+(3*r+14)*Q.card := by
  classical
  let G := colorGraph c k
  let D := 6*r^2+8*r+7
  obtain ⟨P,hu,hd,hi,hs⟩ := exists_rank_partition G univ
  have rks : (∑ B∈P,rankOn G B)≤r := hs.le.trans ((rankOn_univ_eq_indepNum G).le.trans (balanced_indepNum_le c hb k))
  have den := rank_partition_density G P hd hi r
  rw [hu,card_univ,blockEdges_univ] at den
  have floor : r*Fintype.card V≤G.edgeFinset.card+(r.choose 2+1)*r+(r-1)*P.card := by
    have := Nat.mul_le_mul_left (r.choose 2+1) rks
    omega
  by_cases many : 2≤P.card
  · let Q := P.filter (fun B => G.IsNClique r B)
    have rk (B : Finset V) (hB : B∈P) : rankOn G B<r := by
      have lb := sum_le_sum (s:=P.erase B) (f:=fun _ => 1) fun A hA => (hi A (mem_of_mem_erase hA)).rank_pos
      have plus := sum_erase_add P (rankOn G) hB
      simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,card_erase_of_mem hB] at lb
      omega
    have per (B : Finset V) (hB : B∈P) : (9*r+8)*B.card+21 ≤ 6*blockEdges G B+D*rankOn G B+
        (if G.IsNClique r B then 3*r+14 else 0) := atom_line_budget hr hb B (hi B hB) (rk B hB)
    have all := sum_le_sum per
    have ic : (∑ B∈P,if G.IsNClique r B then 3*r+14 else 0)=Q.card*(3*r+14) := by
      rw [←sum_filter]; simp [Q]
    have n := card_biUnion hd
    simp only [id_eq,hu,card_univ] at n
    simp only [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,Nat.cast_id,ic,←n] at all
    have bs := boundary_edge_count G univ P hu.le hd
    rw [blockEdges_univ] at bs
    have total := Nat.mul_le_mul_left D rks
    refine ⟨P.card,Q,rows_from_partition P hu hd hi rks,floor,?_⟩
    change _≤6*G.edgeFinset.card+D*r+(3*r+14)*Q.card
    rw [Nat.mul_comm (3*r+14),Nat.mul_comm 21]
    omega
  · refine ⟨P.card,∅,⟨by simp,by simp,by simpa [hs] using hs ▸ rks⟩,floor,?_⟩
    have up := Nat.mul_le_mul_left (r-1) (show P.card≤1 by omega)
    rw [Nat.mul_one] at up
    have sz := Nat.mul_le_mul_left 21 (show P.card≤1 by omega)
    have ch := congrArg (r*·) (twice_choose_two r)
    change (9*r+8)*Fintype.card V+21*P.card≤6*G.edgeFinset.card+D*r+(3*r+14)*(∅:Finset (Finset V)).card
    rw [card_empty,Nat.mul_zero,Nat.add_zero,hn] at *
    dsimp [D]
    have re : 8*r≤r*r := Nat.mul_le_mul_right r (by omega)
    nlinarith only [floor,up,sz,ch,re,hr,Nat.sub_le r 1]

private theorem averaged_line_arithmetic (r e p q m : ℕ) (hr : 2≤r)
    (floor : m*(r*(r^2+1))≤e+m*((r.choose 2+1)*r)+(r-1)*p)
    (variance : m*((9*r+8)*(r^2+1))+21*p ≤ 6*e+m*((6*r^2+8*r+7)*r)+(3*r+14)*q)
    (edges : 2*e≤m*(r*(r^2+1))) : m*(19*r+16)≤(6*r+28)*q := by
  have ch := congrArg ((m*r)*·) (twice_choose_two r)
  have pr := congrArg ((m*r)*·) (Nat.sub_add_cancel (show 1≤r by omega))
  have id : m*(r*(r^2+1))=2*(m*((r.choose 2+1)*r))+(m*r)*(r-1) := by nlinarith only [ch,pr]
  have mp : m*r ≤ 2*p := by
    apply Nat.le_of_mul_le_mul_right (c:=r-1) _ (by omega)
    nlinarith only [floor,edges,id]
  nlinarith only [variance,edges,mp]

/-- Across all colors, the disjoint full-clique families obey a uniform
line count stronger than three lines per color for r≥69. -/
theorem transversal_full_row_count (hr : 9≤r) (hn : Fintype.card V=r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) :
    ∃ Q : Fin r → Finset (Finset V), (∀ k, FullCliqueRows c k (Q k)) ∧
      r*(19*r+16)≤(6*r+28)*(∑ k,(Q k).card) := by
  classical
  choose p Q rows floor variance using line_partition_estimates hr hn c hb
  have fa := sum_le_sum (s:=univ) fun j _ => floor j
  have va := sum_le_sum (s:=univ) fun j _ => variance j
  simp only [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin,
    Nat.cast_id,hn,sum_color_edges] at fa va
  have edges : 2*(r^2+1).choose 2≤r*(r*(r^2+1)) := by
    nlinarith only [twice_choose_two (r^2+1)]
  exact ⟨Q,rows,averaged_line_arithmetic r ((r^2+1).choose 2) (∑ k,p k) (∑ k,(Q k).card) r (by omega)
    (by nlinarith only [fa]) (by nlinarith only [va]) edges⟩

/-- Every average-sparse color has at least four disjoint full cliques once
there are 69 or more colors. -/
theorem four_sparse_full_rows (hr : 69≤r) (hn : Fintype.card V=r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r)
    (he : 2*(colorGraph c k).edgeFinset.card≤r*(r^2+1)) :
    ∃ Q : Finset (Finset V), 4≤Q.card ∧ FullCliqueRows c k Q := by
  obtain ⟨p,Q,rows,floor,var⟩ := line_partition_estimates (by omega) hn c hb k
  rw [hn] at floor var
  have bound := averaged_line_arithmetic r _ p Q.card 1 (by omega)
    (by simpa only [Nat.one_mul] using floor) (by simpa only [Nat.one_mul] using var)
    (by simpa only [Nat.one_mul] using he)
  refine ⟨Q,?_,rows⟩
  by_contra! small
  have := Nat.mul_le_mul_left (6*r+28) (show Q.card≤3 by omega)
  omega

/-- The residual part of each full row family already contains a first
obstruction, so at least five units of rank remain. -/
theorem FullCliqueRows.five_more (hr : 9≤r) (hn : Fintype.card V=r^2+1) (hb : Balanced c)
    {Q : Finset (Finset V)} (rows : FullCliqueRows c k Q) : Q.card+5≤r := by
  classical
  let A := univ \ Q.biUnion id
  have count := card_biUnion rows.disjoint
  simp only [id_eq,sum_congr rfl (fun C hC => (rows.full C hC).card_eq),
    sum_const,nsmul_eq_mul,Nat.cast_id] at count
  have size := card_sdiff_add_card_eq_card (subset_univ (Q.biUnion id))
  change A.card+(Q.biUnion id).card=(univ : Finset V).card at size
  rw [count,card_univ,hn] at size
  have cap := rows.residual
  change rankOn (colorGraph c k) A+Q.card≤r at cap
  by_contra! few
  have low : rankOn (colorGraph c k) A≤4 := by omega
  have smaller := local_rank_cap (c:=c) (k:=k) (s:=4) (fun a ha S h => by
    have := h.five_le_of_nine_le hb hr (by omega); omega) A low
  have tot := Nat.mul_le_mul_right r cap
  rw [Nat.add_mul] at tot
  rw [pow_two] at size
  omega

/-- Every putative counterexample contains a square three colors smaller,
where two distinct original colors already satisfy the smaller balance test. -/
theorem exists_three_row_square (hr : 9≤r) (hn : Fintype.card V=r^2+1) (hb : Balanced c) :
    ∃ (i j : Fin r) (U : Finset V), i≠j ∧ U.card=(r-3)^2+1 ∧
      rankOn (colorGraph c i) U≤r-3 ∧ rankOn (colorGraph c j) U≤r-3 := by
  classical
  obtain ⟨Q,rows,bound⟩ := transversal_full_row_count hr hn c hb
  let T := univ.filter fun j => 3≤(Q j).card
  have two : 1<T.card := by
    by_contra! few
    have large := sum_le_sum (s:=T) (g:=fun _ => r-5) fun j _ =>
      (show (Q j).card≤r-5 by have := (rows j).five_more hr hn hb; omega)
    have small := sum_le_sum (s:=Tᶜ) (g:=fun _ => 2) fun j hj => (by
      have notmem := mem_compl.mp hj
      change j∉univ.filter _ at notmem
      simp only [mem_filter,mem_univ,true_and,not_le] at notmem
      omega : (Q j).card≤2)
    have split := sum_add_sum_compl T (fun j => (Q j).card)
    have n := card_add_card_compl T
    simp only [Fintype.card_fin] at n
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at large small
    have hi : (∑ j,(Q j).card)+7≤3*r := by
      rcases show T.card=0 ∨ T.card=1 by omega with em|one
      · rw [em,zero_mul] at large; omega
      · rw [one,one_mul] at large; omega
    have times := Nat.mul_le_mul_left (6*r+28) hi
    have sq := sq_nonneg ((r:ℤ)-13)
    have ar : (r:ℤ)*(19*r+16)>(6*r+28)*(3*r-7) := by nlinarith only [sq]
    have bb : (r:ℤ)*(19*r+16)≤(6*r+28)*(∑ j,(Q j).card:ℕ) := by exact_mod_cast bound
    have tt : (6*(r:ℤ)+28)*((∑ j,(Q j).card:ℕ)+7)≤(6*r+28)*(3*r) := by exact_mod_cast times
    linarith
  obtain ⟨i,hi,j,hj,ne⟩ := one_lt_card.mp two
  obtain ⟨P,hP,cp⟩ := exists_subset_card_eq (mem_filter.mp hi).2
  obtain ⟨R,hR,cr⟩ := exists_subset_card_eq (mem_filter.mp hj).2
  exact ⟨i,j,_,ne,row_square_restriction ne ((rows i).subfamily hP) ((rows j).subfamily hR) cp cr hn⟩

end Erdos617
