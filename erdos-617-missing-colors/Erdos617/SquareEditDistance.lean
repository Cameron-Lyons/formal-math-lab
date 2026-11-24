import Erdos617.DeepSquareBudget
import Erdos617.SquareTuran
import Erdos617.QuadraticObstruction
import Erdos617.SparseFullPacking

namespace Erdos617

open Finset SimpleGraph

/-- Unordered edges whose new color differs from the relabeled old color. -/
def changedPaletteEdges {V : Type*} [Fintype V] [DecidableEq V] {r s : ℕ}
    (c : Sym2 V → Fin r) (f : Fin r → Fin s) (d : Sym2 V → Fin s) : Finset (Sym2 V) :=
  (⊤ : SimpleGraph V).edgeFinset.filter fun e => f (c e)≠d e

private theorem colorEdge_mem_top {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    {c : Sym2 V → Fin r} {k : Fin r} {e : Sym2 V} (he : e∈(colorGraph c k).edgeFinset) :
    e∈(⊤ : SimpleGraph V).edgeFinset ∧ c e=k := by
  induction e using Sym2.inductionOn with
  | _ x y =>
    have ed := mem_edgeFinset.mp he
    exact ⟨mem_edgeFinset.mpr ed.1,ed.2⟩

/-- Across all palette relabelings, including those omitting a target label,
the number of exceptional edges is at least s−m minus the number of original
colors that already meet the smaller independence bound. -/
theorem square_edits_from_bad_colors {V : Type*} [Fintype V] [DecidableEq V] {s m : ℕ}
    (hs : 2≤s) (hn : Fintype.card V=s^2+1) (c : Sym2 V → Fin (s+m))
    (f : Fin (s+m) → Fin s) (d : Sym2 V → Fin s) (hd : Balanced d) :
    s≤m+(univ.filter fun k => (colorGraph c k).indepNum≤s).card+(changedPaletteEdges c f d).card := by
  classical
  let T := univ.filter fun k => (colorGraph c k).indepNum≤s
  let F (j : Fin s) := univ.filter fun k => f k=j
  let J (j : Fin s) := T.filter fun k => f k=j
  let E := changedPaletteEdges c f d
  let H (j : Fin s) := E.filter fun e => d e=j
  have cost (j : Fin s) (_ : j∈univ) : 2≤(F j).card+(J j).card+(H j).card := by
    by_cases large : 2≤(F j).card
    · omega
    by_cases empty : (F j).card=0
    · have fresh : ∀ k,f k≠j := by
        intro k eq
        have pos : 0<(F j).card := card_pos.mpr ⟨k,mem_filter.mpr ⟨mem_univ _,eq⟩⟩
        omega
      have sub : (colorGraph d j).edgeFinset⊆H j := by
        intro e he
        obtain ⟨top,eq⟩ := colorEdge_mem_top he
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨top,eq ▸ fresh (c e)⟩,eq⟩
      have min := color_edge_count_of_balanced (by omega : 0<s)
        (by simpa [pow_two] using hn : Fintype.card V=s*s+1) d hd j
      have le := card_le_card sub
      omega
    obtain ⟨k,eq⟩ := card_eq_one.mp (show (F j).card=1 by omega)
    have fk : f k=j := (mem_filter.mp (eq ▸ mem_singleton_self k : k∈F j)).2
    by_cases good : k∈T
    · have pos : 0<(J j).card := card_pos.mpr ⟨k,mem_filter.mpr ⟨good,fk⟩⟩
      omega
    by_contra! few
    have h0 : (H j).card=0 := by omega
    apply good
    apply mem_filter.mpr
    refine ⟨mem_univ _,(hitsPalette_singleton_iff_indepNum c s k).mp ?_⟩
    intro A sz
    obtain ⟨x,hx,y,hy,xy,col⟩ := hd A sz j
    refine ⟨x,hx,y,hy,xy,mem_singleton.mpr ?_⟩
    suffices f (c s(x,y))=j from mem_singleton.mp (eq ▸ (show c s(x,y)∈F j from mem_filter.mpr ⟨mem_univ _,this⟩))
    by_contra different
    have member : s(x,y)∈H j := mem_filter.mpr ⟨mem_filter.mpr ⟨mem_edgeFinset.mpr xy,col ▸ different⟩,col⟩
    exact (card_pos.mpr ⟨_,member⟩).not_ge h0.le
  have total := sum_le_sum cost
  simp only [sum_const,sum_add_distrib,nsmul_eq_mul,Nat.cast_id,card_univ,Fintype.card_fin] at total
  have fsum : ∑ j,(F j).card=s+m := by simp [F,sum_card_fiberwise_eq_card_filter]
  have jsum : ∑ j,(J j).card=T.card := by simp [J,sum_card_fiberwise_eq_card_filter]
  have hsum : ∑ j,(H j).card=E.card := by simp [H,sum_card_fiberwise_eq_card_filter]
  rw [fsum,jsum,hsum] at total
  change s≤m+T.card+E.card
  omega

/-- Some s−m target labels together use at most s−m of the original labels. -/
private theorem few_preimages {s m : ℕ} (hm : m≤s) (f : Fin (s+m) → Fin s) :
    ∃ J : Finset (Fin s), J.card=s-m ∧
      2*m≤(univ.filter fun k => f k∉J).card := by
  classical
  let F (j : Fin s) := univ.filter fun k => f k=j
  let small := univ.filter fun j => (F j).card≤1
  by_cases enough : s-m≤small.card
  · obtain ⟨J,sub,sz⟩ := exists_subset_card_eq enough
    refine ⟨J,sz,?_⟩
    have le := sum_le_sum (s:=J) (g:=fun _ => 1) fun j hj => (mem_filter.mp (sub hj)).2
    change ∑ j∈J,(F j).card≤_ at le
    simp only [F,sum_card_fiberwise_eq_card_filter,sum_const,nsmul_eq_mul,Nat.mul_one,Nat.cast_id,sz] at le
    have sizes := card_filter_add_card_filter_not (s:=univ) (fun i : Fin (s+m) => f i∈J)
    rw [card_univ,Fintype.card_fin] at sizes
    omega
  · have sc : small.card+smallᶜ.card=s := by simp
    obtain ⟨L,sub,sz⟩ := exists_subset_card_eq (s:=smallᶜ) (show m≤smallᶜ.card by omega)
    refine ⟨Lᶜ,by simp [card_compl,sz],?_⟩
    have le := sum_le_sum (s:=L) (f:=fun _ => 2) (g:=fun j => (F j).card)
      (fun j hj => by
        have miss := mem_compl.mp (sub hj)
        exact Nat.lt_of_not_ge (fun smallF => miss (mem_filter.mpr ⟨mem_univ _,smallF⟩)))
    simp [F,sum_card_fiberwise_eq_card_filter,sz,Nat.mul_comm m 2] at le
    simpa using le

private theorem color_edges_on {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (c : Sym2 V → Fin r) (J : Finset (Fin r)) :
    (∑ j∈J,(colorGraph c j).edgeFinset.card)=
      ((⊤ : SimpleGraph V).edgeFinset.filter fun e => c e∈J).card := by
  have eq (j : Fin r) : (colorGraph c j).edgeFinset=(⊤ : SimpleGraph V).edgeFinset.filter fun e => c e=j := by
    ext e
    induction e using Sym2.inductionOn with
    | _ x y => simp [mem_edgeFinset,mem_filter]
  simp_rw [eq,sum_card_fiberwise_eq_card_filter]

private theorem edit_edge_budget {V : Type*} [Fintype V] [DecidableEq V] {r s : ℕ}
    (c : Sym2 V → Fin r) (f : Fin r → Fin s) (d : Sym2 V → Fin s)
    (J : Finset (Fin s)) (M : Finset (Fin r)) (outside : ∀ k∈M,f k∉J) :
    (∑ j∈J,(colorGraph d j).edgeFinset.card)+(∑ k∈M,(colorGraph c k).edgeFinset.card)
      ≤(Fintype.card V).choose 2+(changedPaletteEdges c f d).card := by
  classical
  let all := (⊤ : SimpleGraph V).edgeFinset
  let P := all.filter fun e => d e∈J
  let Q := all.filter fun e => c e∈M
  have sub : P∩Q⊆changedPaletteEdges c f d := by
    intro e he
    obtain ⟨p,q⟩ := mem_inter.mp he
    obtain ⟨top,good⟩ := mem_filter.mp p
    exact mem_filter.mpr ⟨top,fun eq => outside _ (mem_filter.mp q).2 (eq ▸ good)⟩
  have u : P∪Q⊆all := union_subset (filter_subset ..) (filter_subset ..)
  have le := Nat.add_le_add (card_le_card u) (card_le_card sub)
  rw [card_union_add_card_inter] at le
  rw [color_edges_on,color_edges_on,←card_edgeFinset_top_eq_card_choose_two]
  exact le

/-- A balanced target on a reduced square needs enough edits to pay for
the extra edge counts of s−m target colors. This applies to every map f of
palettes, including maps with unused target labels. -/
theorem square_edit_budget {V : Type*} [Fintype V] [DecidableEq V] {s m : ℕ}
    (hs : 2≤s) (hm : m≤s) (hn : Fintype.card V=s^2+1) (c : Sym2 V → Fin (s+m))
    (hb : Balanced c) (f : Fin (s+m) → Fin s) (d : Sym2 V → Fin s) (hd : Balanced d) :
    (s-m)*(m*s^3+2*s^2+4*m*s) ≤ (s+m)*(s+m-1)*(s^2+1)+(s-m)*(s+m+1)+
      2*(s+m)*(changedPaletteEdges c f d).card := by
  classical
  let n := Fintype.card V
  let r := s+m
  let t := s-m
  let edits := (changedPaletteEdges c f d).card
  obtain ⟨J,size,other⟩ := few_preimages hm f
  obtain ⟨M,sub,msize⟩ := exists_subset_card_eq other
  let E (j : Fin s) := (colorGraph d j).edgeFinset.card
  let F (k : Fin (s+m)) := (colorGraph c k).edgeFinset.card
  have ec := edit_edge_budget c f d J M (fun k hk => (mem_filter.mp (sub hk)).2)
  change (∑ j∈J,E j)+(∑ k∈M,F k)≤n.choose 2+edits at ec
  have high (j : Fin s) (_ : j∈J) : r*(s^3+4*s)≤r*(2*E j+n)+r := by
    have free : (colorGraph d j).CliqueFree (s+1) := by
      intro A cl
      obtain ⟨i,hi⟩ : (univ.erase j).Nonempty := card_pos.mp (by simp; omega)
      obtain ⟨x,hx,y,hy,ne,eq⟩ := hd A cl.card_eq i
      exact (mem_erase.mp hi).1 (eq.symm.trans (cl.isClique hx hy ne).2)
    have rank := balanced_indepNum_le d hd j
    have le := edge_bound_of_clique_and_indep_caps (colorGraph d j) hs
      (by simpa [pow_two] using hn : Fintype.card V=s*s+1)
      (fun I ind => by have h := ind.isIndepSet.card_le_indepNum; rw [ind.card_eq] at h; omega)
      free
    have subone := Nat.sub_add_cancel (show 1≤s*s.choose 2+2*s by omega)
    change s*s.choose 2+2*s-1≤E j at le
    have num : s^3+4*s≤(2*E j+n)+1 := by
      change n=s^2+1 at hn
      nlinarith only [congrArg (s*·) (twice_choose_two s),le,subone,hn]
    simpa only [Nat.mul_add,Nat.mul_one] using Nat.mul_le_mul_left r num
  have low (k : Fin (s+m)) (_ : k∈M) : n^2≤r*(2*F k+n) :=
    turan_degree_floor _ (by dsimp [r]; omega) (balanced_indepNum_le c hb k)
  have highs := sum_le_sum high
  have lows := sum_le_sum low
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,sum_add_distrib,←mul_sum,size,msize] at highs lows
  change t*(r*(s^3+4*s))≤r*(2*(∑ j∈J,E j)+t*n)+t*r at highs
  have nt : t+2*m=r := by dsimp [t,r]; omega
  have total : t*(r*(s^3+4*s))+(2*m)*n^2 ≤ r*(2*n.choose 2+r*n)+t*r+2*r*edits := by
    nlinarith only [highs,lows,Nat.mul_le_mul_left (2*r) ec,congrArg (·*(r*n)) nt]
  have cancel := congrArg (·*n^2) nt
  have pairs := congrArg (r*·) (twice_choose_two n)
  change n=s^2+1 at hn
  change t*(m*s^3+2*s^2+4*m*s) ≤ r*(r-1)*(s^2+1)+t*(r+1)+2*r*edits
  have pred : r-1+1=r := by dsimp [r]; omega
  have mv := congrArg (r*n*·) pred
  rw [hn] at total cancel pairs mv
  dsimp [r] at total cancel pairs mv ⊢
  nlinarith only [total,cancel,pairs,mv]

/-- For every target size s≥13, depth-two descent requires changing
at least s³/4 unordered edges after any global relabeling. -/
theorem depth_two_quarter_cube_edits {V : Type*} [Fintype V] [DecidableEq V] {s : ℕ}
    (hs : 13≤s) (hn : Fintype.card V=s^2+1) (c : Sym2 V → Fin (s+2))
    (hb : Balanced c) (f : Fin (s+2) → Fin s) (d : Sym2 V → Fin s) (hd : Balanced d) :
    s^3≤4*(changedPaletteEdges c f d).card := by
  let e := (changedPaletteEdges c f d).card
  have le := square_edit_budget (by omega) (by omega) hn c hb f d hd
  change (s-2)*(2*s^3+2*s^2+4*2*s) ≤ (s+2)*(s+2-1)*(s^2+1)+(s-2)*(s+2+1)+2*(s+2)*e at le
  by_contra! few
  change 4*e<s^3 at few
  obtain ⟨z,eq⟩ := Nat.exists_eq_add_of_le hs
  zify [show 2≤s by omega,show 1≤s+2 by omega] at le few
  have prod := mul_lt_mul_of_pos_right few (show (0:ℤ)<s+2 by positivity)
  have gap : (s:ℤ)^4≥12*s^3+40*s-8 := by
    apply sub_nonneg.mp
    rw [eq]; push_cast; ring_nf; positivity
  nlinarith only [le,prod,gap]

/-- If rank-p sets all obey the local size bound, the whole square must
have a component of rank at least p+1 in every color. Its missing rank-one
components increase the global edge floor by (p−1)(s−1). -/
theorem full_square_color_edges_of_rank_cap {V : Type*} [Fintype V] [DecidableEq V] {s p : ℕ}
    (hs : 2≤s) (hn : Fintype.card V=s^2+1) (d : Sym2 V → Fin s) (hd : Balanced d)
    (j : Fin s) (localBound : ∀ A : Finset V,rankOn (colorGraph d j) A≤p → A.card≤rankOn (colorGraph d j) A*s) :
    s*s.choose 2+s+(s-1)*p≤(colorGraph d j).edgeFinset.card := by
  classical
  let G := colorGraph d j
  obtain ⟨Q,cover,dis,hpart,rks⟩ := exists_rank_partition G univ
  have upper : (∑ A∈Q,rankOn G A)≤s := rks.le.trans ((rankOn_univ_eq_indepNum G).le.trans (balanced_indepNum_le d hd j))
  have large : ∃ H∈Q,p<rankOn G H := by
    by_contra! small
    have cap := sum_le_sum (fun A hA => localBound A (small A hA))
    have size := card_biUnion dis
    simp only [id_eq,cover,card_univ,hn] at size
    rw [←sum_mul,←size] at cap
    change s^2+1≤(∑ A∈Q,rankOn G A)*s at cap
    have prod := Nat.mul_le_mul_right s upper
    nlinarith only [cap,prod]
  obtain ⟨H,hH,above⟩ := large
  have rest := sum_le_sum (s:=Q.erase H) (f:=fun _ => 1)
    (g:=rankOn G) (fun A hA => (hpart A (mem_of_mem_erase hA)).rank_pos)
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,card_erase_of_mem hH] at rest
  have plus := sum_erase_add Q (rankOn G) hH
  have rows : Q.card+p≤s := by omega
  have den := rank_partition_density G Q dis hpart s
  rw [cover,card_univ,blockEdges_univ,hn] at den
  have rk := Nat.mul_le_mul_left (s.choose 2+1) upper
  have cmp := Nat.mul_le_mul_left (s-1) rows
  have pred := congrArg (·*s) (show s-1+1=s by omega)
  nlinarith only [den,rk,cmp,pred,congrArg (s*·) (twice_choose_two s)]

/-- On a one-step square with a balanced original coloring, every balanced
target must change at least (p−1)(s−1)²−1 edges after relabeling, provided
the local size bound holds through rank p for all target colors. -/
theorem one_step_edits_from_local_rank {V : Type*} [Fintype V] [DecidableEq V] {s p : ℕ}
    (hs : 2≤s) (hp : 1≤p) (hn : Fintype.card V=s^2+1) (c : Sym2 V → Fin (s+1))
    (hb : Balanced c) (f : Fin (s+1) → Fin s) (d : Sym2 V → Fin s) (hd : Balanced d)
    (cap : ∀ j A,rankOn (colorGraph d j) A≤p → A.card≤rankOn (colorGraph d j) A*s) :
    (p-1)*(s-1)^2≤(changedPaletteEdges c f d).card+1 := by
  classical
  obtain ⟨J,size,others⟩ := few_preimages (by omega : 1≤s) f
  obtain ⟨M,sub,msize⟩ := exists_subset_card_eq others
  let G := s*s.choose 2+2*s-1
  let B := (s+1)*(s-1).choose 2+2*(s-1)
  have e := edit_edge_budget c f d J M (fun _ hk => (mem_filter.mp (sub hk)).2)
  rw [hn] at e
  have good := sum_le_sum (s:=J) (fun j _ => full_square_color_edges_of_rank_cap hs hn d hd j (cap j))
  have low (k : Fin (s+1)) (_ : k∈M) : B≤(colorGraph c k).edgeFinset.card := by
    have raw := square_turan_floor (colorGraph c k) (by omega : 3≤s+1)
      (by simpa using hn) (balanced_indepNum_le c hb k)
    simpa only [show s+1-2=s-1 by omega] using raw
  have bad := sum_le_sum low
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,size,msize,Nat.mul_one] at good bad
  have num : (s-1)*G+2*B+1=(s^2+1).choose 2 := square_budget_identity s (by omega)
  have defG : G+1=s*s.choose 2+2*s := Nat.sub_add_cancel (by omega)
  have id : s*s.choose 2+s+(s-1)*p=G+(s-1)*(p-1) := by
    have pplus := congrArg ((s-1)*·) (Nat.sub_add_cancel hp)
    nlinarith only [pplus,defG,Nat.sub_add_cancel (show 1≤s by omega)]
  rw [id] at good
  nlinarith only [num,e,good,bad]

/-- The one-step edit lower bound holds with p of order √s, using the
quadratic exclusion for local obstructions. -/
theorem one_step_edits_of_quadratic_palette {V : Type*} [Fintype V] [DecidableEq V] {s p : ℕ}
    (hs : 3≤s) (hp : 1≤p) (large : 1000*p^2<s) (hn : Fintype.card V=s^2+1)
    (c : Sym2 V → Fin (s+1)) (hb : Balanced c) (f : Fin (s+1) → Fin s)
    (d : Sym2 V → Fin s) (hd : Balanced d) :
    (p-1)*(s-1)^2≤(changedPaletteEdges c f d).card+1 := by
  apply one_step_edits_from_local_rank (by omega) hp hn c hb f d hd
  intro j A low
  by_contra! largeA
  obtain ⟨Z,sub,sz⟩ := exists_subset_card_eq (show rankOn (colorGraph d j) A*s+1≤A.card by omega)
  have sq := Nat.pow_le_pow_left low 2
  obtain ⟨I,inc,ind⟩ := independent_in_subset_of_quadratic_palette hs hd
    (show 1000*(rankOn (colorGraph d j) A)^2<s by omega) sz j
  have no := card_le_rankOn _ (inc.trans sub) ind.isIndepSet
  rw [ind.card_eq] at no
  omega

end Erdos617
