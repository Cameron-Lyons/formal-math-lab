module

public import Erdos617.LineVariance
public import Erdos617.RankOneSquare

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

/-- Energy of a component of rank at least two, with a freely chosen slope. -/
private theorem component_variance (a b r e L C : ℕ) (ha : 2≤a) (sl : 4*L≤C)
    (en : 2*b^2≤a*(2*e+r*b)) (two : a=2 → b<2*r)
    (heavy : 3≤a → r*a<b → 4*L+2*C+2*L^2*a≤C*a) :
    (3*r+4*L)*b+(4*L+2*C) ≤ 2*e+(2*r^2+4*L*r+C)*a := by
  have ene : 2*(b:ℤ)^2≤(a:ℤ)*(2*(e:ℤ)+(r:ℤ)*b) := by exact_mod_cast en
  let z : ℤ := b-(r:ℤ)*a
  have var : (a:ℤ)*(4*(L:ℤ)+2*C)+4*L*a*z ≤ 2*z^2+(C:ℤ)*(a:ℤ)^2 := by
    by_cases eq : a=2
    · have small := two eq
      have zz : z+1≤0 := by dsimp [z]; rw [eq]; simp; omega
      have neg := mul_nonpos_of_nonneg_of_nonpos (show (0:ℤ)≤L by positivity) zz
      rw [eq]; norm_num; nlinarith only [sq_nonneg z,neg]
    · by_cases small : b≤r*a
      · have neg : z≤0 := by
          have nat : (b:ℤ)≤(r:ℤ)*a := by exact_mod_cast small
          dsimp [z]; omega
        have prod : (L:ℤ)*a*z≤0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) neg
        have cs := Nat.mul_le_mul_right a sl
        have wide := Nat.mul_le_mul_left (C*a) (show 3≤a by omega)
        zify at cs wide
        nlinarith only [cs,wide,prod,sq_nonneg z]
      · have big := Nat.mul_le_mul_right a (heavy (by omega) (by omega))
        zify at big
        nlinarith only [sq_nonneg (z-(L:ℤ)*a),big]
  have times : (a:ℤ)*((3*(r:ℤ)+4*L)*b+(4*L+2*(C:ℤ))) ≤
      a*(2*(e:ℤ)+(2*(r:ℤ)^2+4*L*r+C)*a) := by
    dsimp [z] at var
    nlinarith only [ene,var]
  exact_mod_cast le_of_mul_le_mul_left times (show 0<(a:ℤ) by omega)

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ} {c : Sym2 V → Fin r} {k : Fin r}

private theorem rank_one_variance_atom (hr : 9≤r) (hb : Balanced c) (L C : ℕ) (sl : 4*L≤C)
    (coeff : ∀ a, 3≤a → ∀ (j : Fin r) t (S : Finset V), t≤a → a<r →
      MinimalObstruction c j t S → 4*L+2*C+2*L^2*a≤C*a)
    (B : Finset V) (hi : RankInseparable (colorGraph c k) B) (rank : rankOn (colorGraph c k) B<r) :
    (3*r+4*L)*B.card+(4*L+2*C) ≤ 2*blockEdges (colorGraph c k) B+
      (2*r^2+4*L*r+C)*rankOn (colorGraph c k) B+
      (if rankOn (colorGraph c k) B=1 ∧ (C≤r+4*L+6 → r≤B.card+1) then r+4*L+C else 0) := by
  classical
  let G := colorGraph c k
  by_cases one : rankOn G B=1
  · have cl := rank_one_clique G one
    have bound := balanced_clique_cap c hb k (by omega) cl
    have en : blockEdges G B=B.card.choose 2 := by
      unfold blockEdges
      have top := G.induce_eq_top.mpr cl
      have hh : (G.induce (B : Set V)).edgeFinset=(⊤ : SimpleGraph B).edgeFinset := by
        ext e; rw [mem_edgeFinset,mem_edgeFinset,top]; rfl
      rw [hh,card_edgeFinset_top_eq_card_choose_two,Fintype.card_coe]
    change _≤2*blockEdges G B+_*rankOn G B+(if rankOn G B=1 ∧ (C≤r+4*L+6 → r≤B.card+1) then _ else _)
    simp only [one,true_and,Nat.mul_one,en]
    have ee := twice_choose_two B.card
    zify at ee
    split <;> rename_i near
    ·
      have pos : 0≤((r:ℤ)-B.card)*(2*r+4*(L:ℤ)+1-B.card) :=
        mul_nonneg (by omega) (by omega)
      zify
      nlinarith only [ee,pos]
    · push Not at near
      have pos : 0≤((r:ℤ)-B.card-2)*(2*r+4*(L:ℤ)+1-B.card) :=
        mul_nonneg (by omega) (by omega)
      zify at near ⊢
      nlinarith only [ee,pos,near.1,near.2]
  have ha : 2≤rankOn G B := by have := hi.rank_pos; change 0<rankOn G B at this; omega
  have free (C : Finset V) (sub : C⊆B) : ¬G.IsNClique r C := hi.no_full_clique hb ha rank sub
  have two (eq : rankOn G B=2) : B.card<2*r := rank_two_clique_free_card_lt hb (by omega) free eq.le
  change _≤2*blockEdges G B+_*rankOn G B+(if rankOn G B=1 ∧ (C≤r+4*L+6 → r≤B.card+1) then _ else _)
  simp only [one,false_and,ite_false,Nat.add_zero]
  apply component_variance _ _ _ _ _ _ ha sl (no_full_part_energy (by omega) free) two
  intro ge oversized
  by_contra! invalid
  have small := local_rank_cap (c:=c) (k:=k) (s:=rankOn G B)
    (fun t le S h => invalid.not_ge (coeff _ ge k t S le rank h)) B (Nat.le_refl _)
  change B.card≤rankOn G B*r at small
  rw [Nat.mul_comm] at small
  omega

private theorem rank_one_partition_estimates (hr : 9≤r) (hn : Fintype.card V=r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) (L C : ℕ) (sl : 4*L≤C)
    (coeff : ∀ a, 3≤a → ∀ (j : Fin r) t (S : Finset V), t≤a → a<r →
      MinimalObstruction c j t S → 4*L+2*C+2*L^2*a≤C*a) (k : Fin r) :
    ∃ (p : ℕ) (Q : Finset (Finset V)), ((↑Q : Set (Finset V)).PairwiseDisjoint id ∧
      (∀ B∈Q,(colorGraph c k).IsClique (B : Set V)) ∧
      ∀ R⊆Q, rankOn (colorGraph c k) (univ \ R.biUnion id)+R.card≤r) ∧
      (∀ B∈Q, C≤r+4*L+6 → r≤B.card+1) ∧
      r*Fintype.card V ≤ (colorGraph c k).edgeFinset.card+(r.choose 2+1)*r+(r-1)*p ∧
      (3*r+4*L)*Fintype.card V+(4*L+2*C)*p ≤ 2*(colorGraph c k).edgeFinset.card+
        (2*r^2+4*L*r+C)*r+(r+4*L+C)*Q.card := by
  classical
  let G := colorGraph c k
  let D := 2*r^2+4*L*r+C
  let Z := r+4*L+C
  obtain ⟨P,hu,hd,hi,hs⟩ := exists_rank_partition G univ
  have rks : (∑ B∈P,rankOn G B)≤r := hs.le.trans ((rankOn_univ_eq_indepNum G).le.trans (balanced_indepNum_le c hb k))
  let Q := P.filter (fun B => rankOn G B=1 ∧ (C≤r+4*L+6 → r≤B.card+1))
  let F := P.filter (fun B => rankOn G B=1)
  have sub : Q⊆F := fun B hB => mem_filter.mpr ⟨(mem_filter.mp hB).1,(mem_filter.mp hB).2.1⟩
  have rows := rank_one_rows_removable G P hu hd rks
  refine ⟨P.card,Q,⟨fun _ hA _ hB ne => rows.1 (sub hA) (sub hB) ne,
    fun B hB => rows.2.1 B (sub hB),fun R rs => rows.2.2 R (rs.trans sub)⟩,
    fun _ hB => (mem_filter.mp hB).2.2,?_⟩
  have den := rank_partition_density G P hd hi r
  rw [hu,card_univ,blockEdges_univ] at den
  have floor : r*Fintype.card V≤G.edgeFinset.card+(r.choose 2+1)*r+(r-1)*P.card := by
    have := Nat.mul_le_mul_left (r.choose 2+1) rks
    omega
  refine ⟨floor,?_⟩
  change _≤2*G.edgeFinset.card+D*r+Z*Q.card
  by_cases many : 2≤P.card
  · have rk (B : Finset V) (hB : B∈P) : rankOn G B<r := by
      have lb := sum_le_sum (s:=P.erase B) (f:=fun _ => 1) fun A hA => (hi A (mem_of_mem_erase hA)).rank_pos
      have plus := sum_erase_add P (rankOn G) hB
      simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,card_erase_of_mem hB] at lb
      omega
    have per (B : Finset V) (hB : B∈P) : (3*r+4*L)*B.card+(4*L+2*C) ≤ 2*blockEdges G B+D*rankOn G B+
        (if rankOn G B=1 ∧ (C≤r+4*L+6 → r≤B.card+1) then Z else 0) := rank_one_variance_atom hr hb L C sl coeff B (hi B hB) (rk B hB)
    have all := sum_le_sum per
    have ic : (∑ B∈P,if rankOn G B=1 ∧ (C≤r+4*L+6 → r≤B.card+1) then Z else 0)=Q.card*Z := by
      rw [←sum_filter]; simp [Q]
    have n := card_biUnion hd
    simp only [id_eq,hu,card_univ] at n
    simp only [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,Nat.cast_id,ic,←n] at all
    have bs := boundary_edge_count G univ P hu.le hd
    rw [blockEdges_univ] at bs
    have total := Nat.mul_le_mul_left D rks
    nlinarith only [all,bs,total]
  · have up := Nat.mul_le_mul_left (r-1) (show P.card≤1 by omega)
    rw [Nat.mul_one] at up
    have sz := Nat.mul_le_mul_left (4*L+2*C) (show P.card≤1 by omega)
    rw [Nat.mul_one] at sz
    have ch := congrArg (r*·) (twice_choose_two r)
    rw [hn] at floor ⊢
    have re : 5*r≤r*r := Nat.mul_le_mul_right r (by omega)
    have lo : r^3+3*r≤2*G.edgeFinset.card := by nlinarith only [floor,up,ch,re,Nat.sub_le r 1]
    have first := Nat.mul_le_mul_left C (show 4≤r by omega)
    apply Nat.le_add_right_of_le
    dsimp [D]
    nlinarith only [lo,first,sl,sz]

/-- A lower bound for the number of removable clique components in the palette.
The free parameter L trades the linear and quadratic contributions. -/
theorem rank_one_palette_variance_of_coefficients (hr : 9≤r) (hn : Fintype.card V=r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) (L C : ℕ) (sl : 4*L≤C)
    (coeff : ∀ a, 3≤a → ∀ (j : Fin r) t (S : Finset V), t≤a → a<r →
      MinimalObstruction c j t S → 4*L+2*C+2*L^2*a≤C*a) :
    ∃ Q : Fin r → Finset (Finset V),
      (∀ k, (↑(Q k) : Set (Finset V)).PairwiseDisjoint id ∧
        (∀ B∈Q k,(colorGraph c k).IsClique (B : Set V)) ∧
        ∀ R⊆Q k, rankOn (colorGraph c k) (univ \ R.biUnion id)+R.card≤r) ∧
      (∀ k B, B∈Q k → C≤r+4*L+6 → r≤B.card+1) ∧
      (2+2*L)*r^2+4*L*r ≤ (r+4*L+C)*(∑ k,(Q k).card) := by
  classical
  choose p Q rows near floor variance using rank_one_partition_estimates hr hn c hb L C sl coeff
  have fa := sum_le_sum (s:=univ) fun j _ => floor j
  have va := sum_le_sum (s:=univ) fun j _ => variance j
  simp only [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin,
    Nat.cast_id,hn,sum_color_edges] at fa va
  have ch := congrArg ((r*r)*·) (twice_choose_two r)
  have pair := twice_choose_two (r^2+1)
  have pred := congrArg ((r*r)*·) (Nat.sub_add_cancel (show 1≤r by omega))
  have parts : r*r≤2*∑ j,p j := by
    apply Nat.le_of_mul_le_mul_right (c:=r-1) _ (by omega)
    nlinarith only [fa,ch,pair,pred]
  have weighted := Nat.mul_le_mul_left (2*L+C) parts
  exact ⟨Q,rows,near,by nlinarith only [va,pair,weighted]⟩

/-- A lower bound for the number of removable clique components in the palette.
The free parameter L trades the linear and quadratic contributions. -/
theorem rank_one_palette_variance (hr : 9≤r) (hn : Fintype.card V=r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) (L : ℕ) :
    ∃ Q : Fin r → Finset (Finset V),
      (∀ k, (↑(Q k) : Set (Finset V)).PairwiseDisjoint id ∧
        (∀ B∈Q k,(colorGraph c k).IsClique (B : Set V)) ∧
        ∀ R⊆Q k, rankOn (colorGraph c k) (univ \ R.biUnion id)+R.card≤r) ∧
      (2+2*L)*r^2+4*L*r ≤ (r+8*L+6*L^2)*(∑ k,(Q k).card) := by
  obtain ⟨Q,rows,_,bound⟩ := rank_one_palette_variance_of_coefficients hr hn c hb L
    (4*L+6*L^2) (by omega) (fun a ge _ _ _ _ _ _ => by
      have := Nat.mul_le_mul_left (4*L+4*L^2) ge
      nlinarith only [this])
  exact ⟨Q,rows,by nlinarith only [bound]⟩

/-- The palette has at least r times m removable cliques whenever 6m²≤r. -/
theorem rank_one_count_of_six_square_le (hn : Fintype.card V=r^2+1) (hb : Balanced c)
    {m : ℕ} (hm : 2≤m) (gap : 6*m^2≤r) :
    ∃ Q : Fin r → Finset (Finset V),
      (∀ k, (↑(Q k) : Set (Finset V)).PairwiseDisjoint id ∧
        (∀ B∈Q k,(colorGraph c k).IsClique (B : Set V)) ∧
        ∀ R⊆Q k, rankOn (colorGraph c k) (univ \ R.biUnion id)+R.card≤r) ∧
      r*m≤∑ k,(Q k).card := by
  have ms : m≤m^2 := by nlinarith only [Nat.mul_le_mul_right m (by omega : 1≤m)]
  have hr : 9≤r := by omega
  obtain ⟨F,rows,bound⟩ := rank_one_palette_variance hr hn c hb m
  have cnt : r*m≤∑ k,(F k).card := by
    by_contra! few
    have upper := Nat.mul_le_mul_left (r+8*m+6*m^2) few.le
    have low := Nat.mul_le_mul_left (r*(m+2)) gap
    have pos := Nat.mul_pos (by omega : 0<r) (by omega : 0<m)
    nlinarith only [bound,upper,low,pos,Nat.zero_le (r*m^2)]
  exact ⟨F,rows,cnt⟩

/-- For every m from 2 through the integer square root of r/6, two colors
can simultaneously pass their smaller balance tests on (r−m)²+1 vertices. -/
theorem exists_square_of_six_square_le (hn : Fintype.card V=r^2+1)
    (hb : Balanced c) {m : ℕ} (hm : 2≤m) (gap : 6*m^2≤r) :
    ∃ (i j : Fin r) (U : Finset V), i≠j ∧ U.card=(r-m)^2+1 ∧
      rankOn (colorGraph c i) U≤r-m ∧ rankOn (colorGraph c j) U≤r-m := by
  have ms : m≤m^2 := by nlinarith only [Nat.mul_le_mul_right m (by omega : 1≤m)]
  obtain ⟨F,rows,cnt⟩ := rank_one_count_of_six_square_le hn hb hm gap
  obtain ⟨i,j,P,Q,ne,cp,cq,_,_,clP,clQ,ri,rj⟩ :=
    rank_one_families_of_count (by omega) hm F rows cnt
  obtain ⟨U,sz,ra,rb⟩ := exists_square_of_clique_rows hn hb ne (by omega : m≤r) P Q cp cq clP clQ ri rj
  exact ⟨i,j,U,ne,sz,ra,rb⟩

private theorem rank_one_count_of_coefficients (hr : 9≤r) (hn : Fintype.card V=r^2+1)
    (hb : Balanced c) (m C : ℕ) (hm : 2≤m) (sl : 4*m≤C)
    (near : C≤r+4*m+6) (budget : 4*m^2+m*C≤(m+2)*r+4*m)
    (coeff : ∀ a, 3≤a → ∀ (j : Fin r) t (S : Finset V), t≤a → a<r →
      MinimalObstruction c j t S → 4*m+2*C+2*m^2*a≤C*a) :
    ∃ Q : Fin r → Finset (Finset V),
      (∀ k, (↑(Q k) : Set (Finset V)).PairwiseDisjoint id ∧
        (∀ B∈Q k,(colorGraph c k).IsClique (B : Set V)) ∧
        ∀ R⊆Q k, rankOn (colorGraph c k) (univ \ R.biUnion id)+R.card≤r) ∧
      (∀ k B, B∈Q k → r≤B.card+1) ∧ r*m≤∑ k,(Q k).card := by
  obtain ⟨Q,rows,card,count⟩ := rank_one_palette_variance_of_coefficients hr hn c hb m C sl coeff
  refine ⟨Q,rows,fun k B hB => card k B hB near,?_⟩
  by_contra! few
  have upper := Nat.mul_lt_mul_of_pos_left few (show 0<r+4*m+C by omega)
  have left := Nat.mul_le_mul_left r budget
  have pos : 0<r*m := Nat.mul_pos (by omega) (by omega)
  nlinarith only [upper,count,left,pos]

/-- There are at least rm removable clique rows of size r or r−1 in the
sharp quadratic range. Within each color the rows are disjoint. -/
theorem near_full_row_count_sharp_square (hn : Fintype.card V=r^2+1) (hb : Balanced c)
    {m : ℕ} (hm : 2≤m) (gap : min (3*m^2) (2*m^2+140*m)≤r) :
    ∃ Q : Fin r → Finset (Finset V),
      (∀ k, (↑(Q k) : Set (Finset V)).PairwiseDisjoint id ∧
        (∀ B∈Q k,(colorGraph c k).IsClique (B : Set V)) ∧
        ∀ R⊆Q k, rankOn (colorGraph c k) (univ \ R.biUnion id)+R.card≤r) ∧
      (∀ k B, B∈Q k → r≤B.card+1) ∧ r*m≤∑ k,(Q k).card := by
  have ms : m≤m^2 := by nlinarith only [Nat.mul_le_mul_right m (by omega : 1≤m)]
  have exp : 4≤m^2 := by nlinarith only [Nat.mul_le_mul hm hm]
  rcases min_le_iff.mp gap with tight|asymp
  · by_cases hr : 33≤r
    · apply rank_one_count_of_coefficients (by omega) hn hb m (3*m^2+m) hm (by omega) (by omega)
      · have h := Nat.mul_le_mul_left (m+2) tight
        nlinarith only [h,Nat.zero_le (m^2)]
      · intro a _ k t S le lt ho
        have six := (ho.six_le_of_thirty_three_le hr hb (le.trans_lt lt)).trans le
        have pos := Nat.mul_le_mul_left (m^2+m) six
        nlinarith only [pos]
    · have low : m≤3 := by
        by_contra! big
        nlinarith only [Nat.mul_le_mul big big,hr,tight]
      have which : m=2 ∨ m=3 := by omega
      apply rank_one_count_of_coefficients (by omega) hn hb m (4*m^2) hm (by omega)
      · rcases which with e|e <;> subst m <;> omega
      · rcases which with e|e <;> subst m <;> omega
      · intro a _ k t S le lt ho
        have five := (ho.five_le_of_nine_le hb (by omega) (le.trans_lt lt)).trans le
        have pos := Nat.mul_le_mul_left (2*m^2) five
        have ms2 := Nat.mul_le_mul_right m hm
        nlinarith only [pos,ms2]
  · have hr : 33≤r := by omega
    apply rank_one_count_of_coefficients (by omega) hn hb m (2*m^2+140*m) hm (by omega) (by omega)
    · have h := Nat.mul_le_mul_left (m+2) asymp
      nlinarith only [h,Nat.zero_le m]
    · intro a _ k t S le lt ho
      have six := (ho.six_le_of_thirty_three_le hr hb (le.trans_lt lt)).trans le
      have large := (ho.quadratic_bound (by omega) hb (le.trans_lt lt)).trans
        (Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left le 2))
      have mag : m≤23*a := by
        by_contra! exceed
        have square := Nat.mul_le_mul exceed.le exceed.le
        nlinarith only [square,large,asymp,Nat.zero_le (a^2),hm]
      have pos := Nat.mul_le_mul_left m (show m+71≤35*a by omega)
      nlinarith only [pos]

/-- The quadratic count has leading coefficient 2 for large m, with an
alternative bound using coefficient 3 that takes effect at smaller m. -/
theorem rank_one_count_sharp_square (hn : Fintype.card V=r^2+1) (hb : Balanced c)
    {m : ℕ} (hm : 2≤m) (gap : min (3*m^2) (2*m^2+140*m)≤r) :
    ∃ Q : Fin r → Finset (Finset V),
      (∀ k, (↑(Q k) : Set (Finset V)).PairwiseDisjoint id ∧
        (∀ B∈Q k,(colorGraph c k).IsClique (B : Set V)) ∧
        ∀ R⊆Q k, rankOn (colorGraph c k) (univ \ R.biUnion id)+R.card≤r) ∧
      r*m≤∑ k,(Q k).card := by
  obtain ⟨Q,rows,_,count⟩ := near_full_row_count_sharp_square hn hb hm gap
  exact ⟨Q,rows,count⟩

/-- Every balanced coloring at the conjectured order has a two-direction
square restriction whenever 3m² or 2m²+140m is at most r. -/
theorem exists_square_of_sharp_quadratic_gap (hn : Fintype.card V=r^2+1)
    (hb : Balanced c) {m : ℕ} (hm : 2≤m) (gap : min (3*m^2) (2*m^2+140*m)≤r) :
    ∃ (i j : Fin r) (U : Finset V), i≠j ∧ U.card=(r-m)^2+1 ∧
      rankOn (colorGraph c i) U≤r-m ∧ rankOn (colorGraph c j) U≤r-m := by
  have ms : m≤m^2 := by nlinarith only [Nat.mul_le_mul_right m (by omega : 1≤m)]
  have mr : m≤r := by rcases min_le_iff.mp gap with h|h <;> omega
  obtain ⟨F,rows,cnt⟩ := rank_one_count_sharp_square hn hb hm gap
  obtain ⟨i,j,P,Q,ne,cp,cq,_,_,clP,clQ,ri,rj⟩ :=
    rank_one_families_of_count (by omega) hm F rows cnt
  obtain ⟨U,sz,ra,rb⟩ := exists_square_of_clique_rows hn hb ne mr P Q cp cq clP clQ ri rj
  exact ⟨i,j,U,ne,sz,ra,rb⟩

/-- An unbounded number of directions can participate in the square reduction.
Every pair from the same family admits its own smaller square. -/
theorem many_square_directions (hn : Fintype.card V=r^2+1) (hb : Balanced c)
    {m : ℕ} (hm : 2≤m) (gap : min (12*m^2) (8*m^2+280*m)≤r) :
    ∃ T : Finset (Fin r), m<T.card ∧
      ∀ i∈T, ∀ j∈T, i≠j → ∃ U : Finset V, U.card=(r-m)^2+1 ∧
        rankOn (colorGraph c i) U≤r-m ∧ rankOn (colorGraph c j) U≤r-m := by
  classical
  have scaled : min (3*(2*m)^2) (2*(2*m)^2+140*(2*m))≤r := by
    convert gap using 2 <;> ring
  obtain ⟨F,rows,cnt⟩ := rank_one_count_sharp_square hn hb (by omega : 2≤2*m) scaled
  let T := univ.filter fun i => m≤(F i).card
  refine ⟨T,?_,?_⟩
  · by_contra! few
    have large := sum_le_sum (s:=T) (g:=fun _ => r) fun k _ => Nat.le_of_add_left_le ((rows k).2.2 (F k) Subset.rfl)
    have small := sum_le_sum (s:=Tᶜ) (f:=fun k => (F k).card) (g:=fun _ => m-1) fun k hk => by
      have h := mem_compl.mp hk
      change k∉univ.filter _ at h
      simp only [mem_filter,mem_univ,true_and,not_le] at h
      omega
    have split := sum_add_sum_compl T (fun k => (F k).card)
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at large small
    have lim : Tᶜ.card≤r := by simpa using Tᶜ.card_le_univ
    have hi := Nat.mul_le_mul_right r few
    have lo := Nat.mul_le_mul_right (m-1) lim
    have pred := congrArg (r*·) (Nat.sub_add_cancel (show 1≤m by omega))
    have ms : 0<m^2 := by positivity
    have rp : 0<r := by rcases min_le_iff.mp gap with h|h <;> omega
    nlinarith only [split,large,small,cnt,hi,lo,pred,rp]
  · intro i hi j hj ne
    obtain ⟨P,pi,cp⟩ := exists_subset_card_eq (mem_filter.mp hi).2
    obtain ⟨Q,qj,cq⟩ := exists_subset_card_eq (mem_filter.mp hj).2
    have ri := (rows i).2.2 P pi
    have rj := (rows j).2.2 Q qj
    exact exists_square_of_clique_rows hn hb ne (by omega : m≤r) P Q cp cq
      (fun C hc => (rows i).2.1 C (pi hc)) (fun D hd => (rows j).2.1 D (qj hd)) (by omega) (by omega)

end Erdos617
