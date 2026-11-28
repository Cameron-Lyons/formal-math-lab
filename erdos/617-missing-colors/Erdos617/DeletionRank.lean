module

public import Erdos617.BinaryAnchor
public import Erdos617.TwoBlockBoundary

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] {r t : ℕ} {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V}

/-- Below the first full clique, a set of rank at most two has order below 2r. -/
theorem rank_two_clique_free_card_lt (hb : Balanced c) (hr : 6 ≤ r) {A : Finset V}
    (clfree : ∀ C⊆A, ¬(colorGraph c k).IsNClique r C) (rk : rankOn (colorGraph c k) A ≤ 2) :
    A.card < 2*r := by
  classical
  by_contra! hn
  obtain ⟨D,hD,sz⟩ := exists_subset_card_eq hn
  let incl := Function.Embedding.subtype (· ∈ D)
  let cD (e : Sym2 D) := c (Sym2.map incl e)
  have no : (colorGraph cD k)ᶜ.CliqueFree 3 := by
    intro Q hQ
    have ind := (colorGraph cD k).isNClique_compl.mp hQ
    have hi : (colorGraph c k).IsIndepSet ((Q.map incl : Finset V) : Set V) := by
      intro x hx y hy ne edge
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
      obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
      exact ind.isIndepSet ha hb (fun eq => ne (congrArg incl eq))
        ⟨fun eq => ne (congrArg incl eq), edge.2⟩
    have sub : Q.map incl ⊆ D := by
      intro x hx
      obtain ⟨a,_,rfl⟩ := mem_map.mp hx
      exact a.prop
    have low := (card_le_rankOn _ (sub.trans hD) hi).trans rk
    rw [card_map,ind.card_eq] at low
    omega
  obtain ⟨C,hC⟩ := clique_on_two_blocks_of_triangle_free r hr
    ((Fintype.card_coe D).trans sz) cD (balanced_pullback c hb incl) k no
  apply clfree (C.map incl) (by
    intro x hx
    obtain ⟨a,_,rfl⟩ := mem_map.mp hx
    exact hD a.prop)
  refine ⟨?_, (card_map _).trans hC.card_eq⟩
  intro x hx y hy hxy
  obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
  obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
  exact ⟨hxy,(hC.isClique ha hb (fun eq => hxy (congrArg incl eq))).2⟩

/-- A set of rank at most two inside a minimal obstruction of rank below r
has strictly fewer than 2r vertices. -/
theorem MinimalObstruction.rank_two_card_lt (h : MinimalObstruction c k t S)
    (hb : Balanced c) (hr : 6 ≤ r) (ht : t<r) {A : Finset V}
    (ha : A⊆S) (rk : rankOn (colorGraph c k) A ≤ 2) : A.card < 2*r :=
  rank_two_clique_free_card_lt hb hr (fun C sub => h.no_clique hb ht C (sub.trans ha)) rk

/-- A proper subset attaining its rank-times-r order has rank at least three. -/
theorem MinimalObstruction.three_le_tight_rank (h : MinimalObstruction c k t S)
    (hb : Balanced c) (hr : 6≤r) (ht : t<r) {A : Finset V}
    (ha : A⊆S) (pos : A.Nonempty) (sz : A.card=rankOn (colorGraph c k) A*r) :
    3 ≤ rankOn (colorGraph c k) A := by
  have hp := rankOn_pos (colorGraph c k) pos
  by_contra! hl
  rcases show rankOn (colorGraph c k) A = 1 ∨ rankOn (colorGraph c k) A=2 by omega with one | two
  · rw [one,Nat.one_mul] at sz
    exact h.no_clique hb ht A ha ⟨rank_one_clique _ one,sz⟩
  · rw [two] at sz
    exact (h.rank_two_card_lt hb hr ht ha (by omega)).ne sz

/-- If a vertex-deleted minimal obstruction admits a rank-additive bipartition,
both parts have rank at least three. -/
theorem MinimalObstruction.erase_split_ranks (h : MinimalObstruction c k t S)
    (hb : Balanced c) (hr : 6≤r) (ht : t<r) {v : V} (hv : v∈S) {A B : Finset V}
    (ha : A.Nonempty) (hb' : B.Nonempty) (hd : Disjoint A B) (hu : A∪B=S.erase v)
    (sum : rankOn (colorGraph c k) A+rankOn (colorGraph c k) B≤t) :
    3 ≤ rankOn (colorGraph c k) A ∧ 3 ≤ rankOn (colorGraph c k) B := by
  let G := colorGraph c k
  have supA : A ⊆ S.erase v := hu ▸ subset_union_left
  have supB : B ⊆ S.erase v := hu ▸ subset_union_right
  have bounds {D : Finset V} (hh : D⊆S.erase v) : D.card ≤ rankOn G D*r := by
    obtain ⟨J,hJ,ind,sz⟩ := h.proper_subset (by omega) D (hh.trans_ssubset (erase_ssubset hv))
    exact sz.trans (Nat.mul_le_mul_right _ (card_le_rankOn _ hJ ind))
  have tot := congrArg Finset.card hu
  rw [card_union_of_disjoint hd,card_erase_of_mem hv,h.card_eq,Nat.add_sub_cancel] at tot
  have max := Nat.mul_le_mul_right r sum
  rw [Nat.add_mul] at max
  change rankOn G A*r+rankOn G B*r ≤ t*r at max
  have a := bounds supA
  have b := bounds supB
  exact ⟨h.three_le_tight_rank hb hr ht (supA.trans (erase_subset ..)) ha (by
    change A.card=rankOn G A*r; omega), h.three_le_tight_rank hb hr ht (supB.trans (erase_subset ..)) hb' (by
    change B.card=rankOn G B*r; omega)⟩

/-- At ranks at most five, rank-inseparability persists after deleting any vertex. -/
theorem MinimalObstruction.erase_rank_inseparable (h : MinimalObstruction c k t S)
    (hb : Balanced c) (hr : 6≤r) (ht : t≤5) {v : V} (hv : v∈S) :
    RankInseparable (colorGraph c k) (S.erase v) := by
  have rpos : 0<r := by omega
  have tpos := h.pos
  have sz : 1<S.card := by rw [h.card_eq]; exact Nat.lt_add_one_of_le (Nat.mul_pos tpos rpos)
  have rk := (h.rank_inseparable rpos).rank_erase hv sz
  rw [h.rank_eq rpos] at rk
  refine ⟨card_pos.mp (by rw [card_erase_of_mem hv]; omega),?_⟩
  intro A B ha hb' hd hu
  rw [rk]
  by_contra! le
  obtain ⟨l,r⟩ := h.erase_split_ranks hb hr (by omega) hv ha hb' hd hu le
  omega

/-- The region supported by any pair of anchors has at most 2r−1 vertices. -/
theorem MinimalObstruction.two_anchor_card_lt (h : MinimalObstruction c k t S)
    (hb : Balanced c) (hr : 6 ≤ r) (ht : t<r) {I J T : Finset V} (hIS : I⊆S)
    (ind : (colorGraph c k).IsNIndepSet t I) (hJI : J⊆I) (sz : J.card=2)
    (hTS : T⊆S) (hits : ∀ x∈T, I.filter (fun u => x=u ∨ (colorGraph c k).Adj x u) ⊆ J) :
    T.card < 2*r :=
  h.rank_two_card_lt hb hr ht hTS ((h.anchor_rank_bound hIS ind J T hJI hTS hits).trans_eq sz)

/-- One vertex below the upper order endpoint, a tight rank bound still
forces a full clique when the rank is at least three and the slope at least five. -/
theorem exists_clique_of_saturated_rank_density_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (hi : RankInseparable G A) (d : ℕ) (hd : 5≤d)
    (hα : 3≤rankOn G A) (sz : A.card=d*rankOn G A)
    (he : d*A.card=blockEdges G A+(d.choose 2+1)*rankOn G A+(d-1)) :
    ∃ C ⊆ A, G.IsNClique d C := by
  classical
  have many : d*A.card<2*blockEdges G A := by
    obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hd
    obtain ⟨q,hq⟩ := Nat.exists_eq_add_of_le hα
    have eq := congrArg (fun x => x*rankOn G A) (twice_choose_two d)
    rw [hm,hq,show 5+m-1=4+m by omega] at he
    rw [hm,hq] at eq sz
    rw [hm]
    nlinarith only [he,eq,sz,congrArg ((5+m)*·) sz,Nat.zero_le (m*q),Nat.zero_le m,Nat.zero_le q]
  obtain ⟨v,hv,high⟩ : ∃ v∈A, d < (A.filter (G.Adj v)).card := by
    by_contra! small
    have bound := sum_le_sum small
    rw [block_degree_sum] at bound
    simpa [Nat.mul_comm] using many.not_ge (by simpa [Nat.mul_comm] using bound)
  have big : 1<A.card := by
    have bound := Nat.mul_le_mul hd hα
    omega
  have rankeq := hi.rank_erase hv big
  obtain ⟨P,hu,hdis,hat,hs⟩ := exists_rank_partition G (A.erase v)
  have ppos : P.Nonempty := by
    by_contra! hz
    have hz' : A.erase v=∅ := by simpa [hz] using hu.symm
    have hc := card_erase_add_one hv
    rw [hz',card_empty] at hc
    omega
  obtain ⟨multi,tight,smaller⟩ := tight_augmented_parts G A hi d (by omega) he hv big high P hu hdis hat hs ppos
  have totals := card_biUnion hdis
  simp only [id_eq,hu] at totals
  have partsz : ∃ B∈P, B.card=d*rankOn G B := by
    by_contra! no
    have per (B : Finset V) (hB : B∈P) : B.card+1≤d*rankOn G B := lt_of_le_of_ne (smaller B hB) (no B hB)
    have tol := sum_le_sum per
    simp only [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,←mul_sum,←totals,hs,rankeq] at tol
    have esc := card_erase_add_one hv
    have hp := card_pos.mpr ppos
    omega
  obtain ⟨B,hB,ord⟩ := partsz
  have sub : B⊆A.erase v := biUnion_subset.mp hu.le B hB
  have nv : v∉B := fun h => notMem_erase v A (sub h)
  obtain ⟨K,_,hK,rk,edge,same⟩ := augment_inseparable_on (hat B hB) v nv
  have ordK : (insert v B).card=d*rankOn K (insert v B)+1 := by rw [card_insert_of_notMem nv,rk,ord]
  have eqK : d*(insert v B).card=blockEdges K (insert v B)+(d.choose 2+1)*rankOn K (insert v B)+(d-1) := by
    simpa only [card_insert_of_notMem nv,rk,edge] using tight B hB
  obtain ⟨C,subC,hC⟩ := exists_clique_avoiding_of_rank_density_eq K (insert v B) hK d (by omega) ordK eqK v
  rw [erase_insert nv] at subC
  refine ⟨C,subC.trans (sub.trans (erase_subset ..)),?_,hC.card_eq⟩
  intro x hx y hy xy
  exact (same x (subC hx) y (subC hy)).mp (hC.isClique hx hy xy)

/-- Each part in a rank-additive decomposition of a vertex deletion costs
at least one edge of slack in the original supporting inequality. -/
theorem MinimalObstruction.erase_partition_slack (h : MinimalObstruction c k t S)
    (hb : Balanced c) (hr : 3≤r) (ht : t<r) {v : V} (hv : v∈S)
    (P : Finset (Finset V)) (hu : P.biUnion id=S.erase v)
    (hd : (↑P : Set (Finset V)).PairwiseDisjoint id)
    (hi : ∀ A∈P, RankInseparable (colorGraph c k) A)
    (hs : ∑ A∈P, rankOn (colorGraph c k) A=rankOn (colorGraph c k) (S.erase v)) :
    r*S.card+P.card ≤ blockEdges (colorGraph c k) S+(r.choose 2+1)*t+(r-1) := by
  classical
  let G := colorGraph c k
  have ins := h.rank_inseparable (by omega)
  have sz : 1<S.card := by rw [h.card_eq]; exact Nat.lt_add_one_of_le (Nat.mul_pos h.pos (by omega))
  have rk := (ins.rank_erase hv sz).trans (h.rank_eq (by omega))
  have sizes := card_biUnion hd
  simp only [id_eq,hu] at sizes
  have sub (A : Finset V) (ha : A∈P) : A⊆S.erase v := biUnion_subset.mp hu.le A ha
  have le (A : Finset V) (ha : A∈P) : A.card≤r*rankOn G A := by
    obtain ⟨I,hI,ind,lim⟩ := h.proper_subset (by omega) A ((sub A ha).trans_ssubset (erase_ssubset hv))
    rw [Nat.mul_comm]
    exact lim.trans (Nat.mul_le_mul_right _ (card_le_rankOn _ hI ind))
  have sumrank : ∑ A∈P, rankOn G A=t := hs.trans rk
  have order : ∀ A∈P, A.card=r*rankOn G A := by
    apply (sum_eq_sum_iff_of_le le).mp
    rw [←sizes,←mul_sum,sumrank,card_erase_of_mem hv,h.card_eq,Nat.add_sub_cancel,Nat.mul_comm]
  have ppos : P.Nonempty := by
    by_contra! empty
    have eq : S.erase v=∅ := by simpa [empty] using hu.symm
    have many := card_erase_add_one hv
    rw [eq,card_empty] at many
    omega
  have per (A : Finset V) (ha : A∈P) : r*(A.card+1)+1 ≤
      blockEdges G A+blockerSize G A+(r.choose 2+1)*rankOn G A+(r-1) := by
    have nv : v∉A := fun mem => notMem_erase v S (sub A ha mem)
    obtain ⟨K,_,hK,rkK,ed,same⟩ := augment_inseparable_on (hi A ha) v nv
    have lo := rank_density K (insert v A) hK r
    rw [card_insert_of_notMem nv,rkK,ed] at lo
    apply lt_of_le_of_ne lo
    intro equality
    have ordK : (insert v A).card=r*rankOn K (insert v A)+1 := by rw [card_insert_of_notMem nv,rkK,order A ha]
    obtain ⟨C,hC,hcl⟩ := exists_clique_avoiding_of_rank_density_eq K (insert v A) hK r hr ordK
      (by simpa only [card_insert_of_notMem nv,rkK,ed] using equality) v
    rw [erase_insert nv] at hC
    apply h.no_clique hb ht C (hC.trans ((sub A ha).trans (erase_subset ..)))
    exact ⟨fun x hx y hy xy => (same x (hC hx) y (hC hy)).mp (hcl.isClique hx hy xy),hcl.card_eq⟩
  have combined := sum_le_sum per
  simp only [Nat.mul_add,Nat.mul_one,sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,Nat.cast_id,
    Nat.mul_one,←sizes,sumrank] at combined
  have cut := rank_boundary G ins hv P ppos hu hd hi hs
  have card := congrArg (r*·) (card_erase_add_one hv)
  rw [Nat.mul_add,Nat.mul_one] at card
  have swap : P.card*(r-1)+P.card=P.card*r := by rw [←Nat.mul_succ]; congr 1; omega
  change r*S.card+P.card ≤ blockEdges G S+(r.choose 2+1)*t+(r-1)
  omega

/-- Every first obstruction with rank at least three and below r costs at least
two edges above the rank-density supporting line. -/
theorem MinimalObstruction.rank_edge_slack_two (h : MinimalObstruction c k t S)
    (hb : Balanced c) (hr : 6≤r) (ht : 3≤t) (thi : t<r) :
    r*S.card+2 ≤ blockEdges (colorGraph c k) S+(r.choose 2+1)*t+(r-1) := by
  classical
  let G := colorGraph c k
  have rk := h.rank_eq (by omega)
  have orig := h.rank_edge_bound (by omega)
  have hn := h.card_eq
  have many : r*S.card < 2*blockEdges G S := by
    have ch := congrArg (fun x => x*t) (twice_choose_two r)
    change r*(t*r+1) ≤ blockEdges G S+(r.choose 2+1)*t+(r-1) at orig
    generalize edge_count : blockEdges G S=e at orig ⊢
    obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hr
    obtain ⟨q,hq⟩ := Nat.exists_eq_add_of_le ht
    rw [hm,hq,show 6+m-1=5+m by omega] at orig
    rw [hm,hq] at ch hn
    rw [hm]
    nlinarith only [orig,ch,hn,congrArg ((6+m)*·) hn,Nat.zero_le (m*q),Nat.zero_le m,Nat.zero_le q]
  obtain ⟨v,hv,high⟩ : ∃ v∈S, r<(S.filter (G.Adj v)).card := by
    by_contra! small
    have bound := sum_le_sum small
    rw [block_degree_sum] at bound
    exact many.not_ge (by simpa [Nat.mul_comm] using bound)
  let A := S.erase v
  obtain ⟨P,hu,hd,hi,hs⟩ := exists_rank_partition G A
  by_cases multi : 2≤P.card
  · exact (Nat.add_le_add_left multi _).trans (h.erase_partition_slack hb (by omega) thi hv P hu hd hi hs)
  have nz : P.Nonempty := by
    by_contra! emp
    have zz : A=∅ := by simpa [emp] using hu.symm
    have cA := card_erase_add_one hv
    change A.card+1=S.card at cA
    rw [zz,card_empty] at cA
    have p := Nat.mul_pos h.pos (show 0<r by omega)
    omega
  have one : P.card=1 := by have := card_pos.mpr nz; omega
  obtain ⟨T,rfl⟩ := card_eq_one.mp one
  have ze : T=A := by simpa using hu
  have ins : RankInseparable G A := ze ▸ hi T (mem_singleton_self T)
  have eq : rankOn G A=t := ((h.rank_inseparable (by omega)).rank_erase hv (by
    rw [hn]; exact Nat.lt_add_one_of_le (Nat.mul_pos (by omega) (by omega)))).trans rk
  have sz : A.card=r*rankOn G A := by
    rw [eq,Nat.mul_comm]; exact (card_erase_of_mem hv).trans (by rw [hn,Nat.add_sub_cancel])
  have lo := rank_density G A ins r
  have strict : r*A.card<blockEdges G A+(r.choose 2+1)*rankOn G A+(r-1) := by
    refine lt_of_le_of_ne lo (fun tight => ?_)
    obtain ⟨C,sub,hC⟩ := exists_clique_of_saturated_rank_density_eq G A ins r (by omega) (by rw [eq]; omega) sz tight
    exact h.no_clique hb thi C (sub.trans (erase_subset ..)) hC
  rw [eq] at strict
  have edges := blockEdges_erase_add G S v hv
  change blockEdges G A + _ = blockEdges G S at edges
  have step := congrArg (r*·) (card_erase_add_one hv)
  change r*(A.card+1)=r*S.card at step
  rw [Nat.mul_add,Nat.mul_one] at step
  change r*S.card+2 ≤ blockEdges G S+(r.choose 2+1)*t+(r-1)
  omega

/-- With at least nine colors, every first obstruction of rank below r has rank at least five. -/
theorem MinimalObstruction.five_le_of_nine_le (h : MinimalObstruction c k t S)
    (hb : Balanced c) (hr : 9≤r) (ht : t<r) : 5≤t := by
  have bound := h.rank_parameter_bound (by omega) hb ht
  have two := h.two_le_parameter (by omega) hb ht
  by_contra! low
  rcases show t=2 ∨ t=3 ∨ t=4 by omega with ht2 | ht3 | ht4
  · subst t; norm_num at bound; omega
  · subst t; norm_num at bound; omega
  · subst t
    norm_num at bound
    have slack := h.rank_edge_slack_two hb (by omega) (by omega) (by omega)
    rw [h.card_eq,color_blockEdges_eq] at slack
    let cp : Sym2 S → Fin r := fun e => c (Sym2.map Subtype.val e)
    have total := sum_color_edges cp
    rw [←sum_erase_add _ _ (mem_univ k),Fintype.card_coe,h.card_eq] at total
    have foreign := h.foreign_edge_sum hb (by omega)
    change (r-1)*(r*Nat.choose 4 2+2*4-1) ≤ ∑ j∈univ.erase k, (colorGraph cp j).edgeFinset.card at foreign
    change r*(4*r+1)+2 ≤ (colorGraph cp k).edgeFinset.card+(Nat.choose r 2+1)*4+(r-1) at slack
    rcases show r=9 ∨ r=10 by omega with hr9 | hr10 <;> subst r <;> norm_num [Nat.choose] at slack total foreign <;> omega

end Erdos617
