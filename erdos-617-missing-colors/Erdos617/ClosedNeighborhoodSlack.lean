module

public import Erdos617.DeletionRank
public import Erdos617.BlockAccount
public import Erdos617.SevenPairs

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] {r t : ℕ} {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V}

/-- A saturated subset of rank at most five cannot be split rank-additively:
each part in such a split would have rank at least three. -/
theorem MinimalObstruction.saturated_inseparable (h : MinimalObstruction c k t S)
    (hb : Balanced c) (hr : 6≤r) (ht : t<r) {W : Finset V} (ws : W⊂S)
    (pos : W.Nonempty) (sat : W.card=rankOn (colorGraph c k) W*r)
    (cap : rankOn (colorGraph c k) W≤5) : RankInseparable (colorGraph c k) W := by
  let G := colorGraph c k
  have bound {A : Finset V} (sub : A⊆W) : A.card ≤ rankOn G A*r := by
    obtain ⟨I,hI,ind,lim⟩ := h.proper_subset (by omega) A (sub.trans_ssubset ws)
    exact lim.trans (Nat.mul_le_mul_right _ (card_le_rankOn _ hI ind))
  refine ⟨pos,?_⟩
  intro A B ha hB hd hu
  have subA : A⊆W := hu ▸ subset_union_left
  have subB : B⊆W := hu ▸ subset_union_right
  by_contra! small
  have eq := congrArg Finset.card hu
  rw [card_union_of_disjoint hd,sat] at eq
  have upper := Nat.mul_le_mul_right r small
  rw [Nat.add_mul] at upper
  change rankOn G A*r+rankOn G B*r ≤ rankOn G W*r at upper
  change A.card+B.card=rankOn G W*r at eq
  have a := bound subA
  have b := bound subB
  have ra := h.three_le_tight_rank hb hr ht (subA.trans ws.le) ha (by change A.card=rankOn G A*r; omega)
  have rb := h.three_le_tight_rank hb hr ht (subB.trans ws.le) hB (by change B.card=rankOn G B*r; omega)
  omega

/-- Two independent vertices outside a saturated rank-(t−1) set together
have at least r neighbor incidences into it. -/
theorem MinimalObstruction.outside_pair_cost (h : MinimalObstruction c k t S)
    (hr : 0<r) (ht : 2≤t) {W : Finset V} (ws : W⊂S) (sz : W.card=(t-1)*r)
    {a b : V} (ha : a∈S) (hb : b∈S) (na : a∉W) (nb : b∉W) (ab : a≠b)
    (non : ¬(colorGraph c k).Adj a b) :
    r ≤ (W.filter ((colorGraph c k).Adj a)).card+(W.filter ((colorGraph c k).Adj b)).card := by
  classical
  let G := colorGraph c k
  let D := W.filter (G.Adj a) ∪ W.filter (G.Adj b)
  let A := W \ D
  have ds : D⊆W := union_subset (filter_subset ..) (filter_subset ..)
  have szA := card_sdiff_add_card_eq_card ds
  change A.card+D.card=W.card at szA
  obtain ⟨I,hI,ind,eq⟩ := exists_max_indep G A
  have iw : I⊆W := hI.trans sdiff_subset
  have ia := independent_insert_of_nonadjacent G ind a (by
    intro w hw e
    exact (mem_sdiff.mp (hI hw)).2 (mem_union_left _ (mem_filter.mpr ⟨iw hw,e⟩)))
  have ib := independent_insert_of_nonadjacent G ia b (by
    intro w hw e
    rcases mem_insert.mp hw with rfl | hw
    · exact non e.symm
    · exact (mem_sdiff.mp (hI hw)).2 (mem_union_right _ (mem_filter.mpr ⟨iw hw,e⟩)))
  have ia' : a∉I := fun hw => na (iw hw)
  have ib' : b∉insert a I := by simp [Ne.symm ab,show b∉I from fun hw => nb (iw hw)]
  have rk := card_le_rankOn G (insert_subset hb (insert_subset ha (iw.trans ws.le))) ib
  rw [card_insert_of_notMem ib',card_insert_of_notMem ia',eq] at rk
  have rt : rankOn G S=t := h.rank_eq hr
  obtain ⟨J,hJ,indJ,small⟩ := h.proper_subset hr A ((sdiff_subset : A⊆W).trans_ssubset ws)
  have low := small.trans (Nat.mul_le_mul_right r (card_le_rankOn G hJ indJ))
  have cut : rankOn G A+1≤t-1 := by omega
  have mul := Nat.mul_le_mul_right r cut
  rw [Nat.add_mul,Nat.one_mul,←sz] at mul
  have dcap : D.card≤(W.filter (G.Adj a)).card+(W.filter (G.Adj b)).card := card_union_le _ _
  change r ≤ (W.filter (G.Adj a)).card+(W.filter (G.Adj b)).card
  omega

/-- Deleting the closed neighborhood of a degree-r vertex leaves a saturated
rank-(t−1) set inside the obstruction. -/
theorem MinimalObstruction.degree_eq_nonneighbor_data (h : MinimalObstruction c k t S)
    (hr : 0<r) (lo : 1≤t) {x : V} (hx : x∈S)
    (deg : (S.filter ((colorGraph c k).Adj x)).card=r) :
    let W := S \ insert x (S.filter ((colorGraph c k).Adj x))
    W⊂S ∧ W.card=(t-1)*r ∧ rankOn (colorGraph c k) W=t-1 := by
  classical
  dsimp only
  let G := colorGraph c k
  let B := insert x (S.filter (G.Adj x))
  let W := S \ B
  have sub : B⊆S := insert_subset hx (filter_subset ..)
  have sizeB : B.card=r+1 := by
    rw [show B=insert x (S.filter (G.Adj x)) from rfl,card_insert_of_notMem (by simp)]
    exact congrArg (·+1) deg
  have ws : W⊂S := (ssubset_iff_of_subset sdiff_subset).mpr ⟨x,hx,fun hw => (mem_sdiff.mp hw).2 (mem_insert_self ..)⟩
  have split := card_sdiff_add_card_eq_card sub
  change W.card+B.card=S.card at split
  have sumid : (t-1)*r+r=t*r := by rw [←Nat.succ_mul]; congr 1; omega
  have sz : W.card=(t-1)*r := by have := h.card_eq; omega
  have rk : rankOn G W=t-1 := by
    obtain ⟨I,hI,ind,eq⟩ := exists_max_indep G W
    have nI : x∉I := fun hm => (mem_sdiff.mp (hI hm)).2 (mem_insert_self ..)
    have add := independent_insert_of_nonadjacent G ind x (by
      intro v hv ev
      exact (mem_sdiff.mp (hI hv)).2 (mem_insert_of_mem (mem_filter.mpr ⟨ws.le (hI hv),ev⟩)))
    have cap := card_le_rankOn G (insert_subset hx (hI.trans ws.le)) add
    rw [card_insert_of_notMem nI,eq] at cap
    have rt : rankOn G S=t := h.rank_eq (by omega)
    obtain ⟨J,hJ,indJ,low⟩ := h.proper_subset (by omega) W ws
    have lr := low.trans (Nat.mul_le_mul_right r (card_le_rankOn G hJ indJ))
    rw [sz] at lr
    have := Nat.le_of_mul_le_mul_right lr (show 0<r by omega)
    omega
  exact ⟨ws,sz,rk⟩

/-- A degree-r vertex whose nonneighbors form an inseparable set costs at
least r−4 edges above the supporting rank-density inequality. -/
theorem MinimalObstruction.closed_neighborhood_slack (h : MinimalObstruction c k t S)
    (hb : Balanced c) (hr : 6≤r) (lo : 4≤t) (ht : t<r) {x : V} (hx : x∈S)
    (deg : (S.filter ((colorGraph c k).Adj x)).card=r)
    (ins : RankInseparable (colorGraph c k) (S \ insert x (S.filter ((colorGraph c k).Adj x)))) :
    r*S.card+(r-4) ≤ blockEdges (colorGraph c k) S+(r.choose 2+1)*t+(r-1) := by
  classical
  let G := colorGraph c k
  let B := insert x (S.filter (G.Adj x))
  let W := S \ B
  have sub : B⊆S := insert_subset hx (filter_subset ..)
  have sizeB : B.card=r+1 := by
    rw [show B=insert x (S.filter (G.Adj x)) from rfl,card_insert_of_notMem (by simp)]
    exact congrArg (·+1) deg
  have ws : W⊂S := (ssubset_iff_of_subset sdiff_subset).mpr ⟨x,hx,fun hw => (mem_sdiff.mp hw).2 (mem_insert_self ..)⟩
  have split := card_sdiff_add_card_eq_card sub
  change W.card+B.card=S.card at split
  have sumid : (t-1)*r+r=t*r := by rw [←Nat.succ_mul]; congr 1; omega
  have sz : W.card=(t-1)*r := by have := h.card_eq; omega
  have ⟨_,_,rk⟩ := h.degree_eq_nonneighbor_data (by omega) (by omega) hx deg
  change rankOn G W=t-1 at rk
  have density := rank_density G W ins r
  have strict : r*W.card < blockEdges G W+(r.choose 2+1)*rankOn G W+(r-1) := by
    refine lt_of_le_of_ne density fun equality => ?_
    obtain ⟨C,hC,cl⟩ := exists_clique_of_saturated_rank_density_eq G W ins r (by omega) (by omega)
      (by rw [sz,rk,Nat.mul_comm]) equality
    exact h.no_clique hb ht C (hC.trans ws.le) cl
  have uni : B∪W=S := union_sdiff_of_subset sub
  have dis : Disjoint B W := disjoint_sdiff
  have md (a : V) (ha : a∈B) : B.card≤((B∪W).filter (G.Adj a)).card+1 := by
    rw [uni,sizeB]; exact Nat.succ_le_succ (h.degree_ge a (sub ha))
  obtain ⟨cost,ledger,_,_,_,quartet⟩ := block_account_with_subsets G B W dis md
  obtain ⟨a,ha,b,hb',u,hu,v,hv,ab,uv,d,ab',uv'⟩ := two_missing_pairs_of_six_le hr hb sizeB
    (fun C hc => h.no_clique hb ht C (hc.trans sub))
  let out (w : V) := (W.filter (G.Adj w)).card
  have large {a b : V} (ha : a∈B) (hb : b∈B) (ne : a≠b) (non : ¬G.Adj a b) : r≤out a+out b :=
    h.outside_pair_cost (by omega) (by omega) ws sz (sub ha) (sub hb)
      (Finset.disjoint_left.mp dis ha) (Finset.disjoint_left.mp dis hb) ne non
  let A : Finset V := {a,b}
  let U : Finset V := {u,v}
  have aB : A⊆B := insert_subset ha (singleton_subset_iff.mpr hb')
  have uB : U⊆B := insert_subset hu (singleton_subset_iff.mpr hv)
  have lim := quartet (A∪U) (union_subset aB uB)
  rw [card_union_of_disjoint d,sum_union d,show A.card=2 from card_pair ab,
    show U.card=2 from card_pair uv] at lim
  simp only [sum_pair ab,sum_pair uv] at lim
  change out a+out b+(out u+out v)≤cost+6 at lim
  have la := large ha hb' ab ab'
  have lu := large hu hv uv uv'
  rw [uni,sizeB,Nat.choose_succ_succ' r 1,Nat.choose_one_right] at ledger
  rw [rk] at strict
  have nmod : W.card+r+1=S.card := by omega
  have cod := congrArg (r*·) nmod
  have prod := congrArg ((r.choose 2+1)*·) (show t-1+1=t by omega)
  have ch := twice_choose_two r
  change r*S.card+(r-4) ≤ blockEdges G S+(r.choose 2+1)*t+(r-1)
  nlinarith only [strict,ledger,lim,la,lu,cod,prod,ch,Nat.sub_add_cancel (show 4≤r by omega)]

/-- The degree-r slack bound is unconditional on the nonneighbors when
the obstruction rank is at most six. -/
theorem MinimalObstruction.closed_neighborhood_slack_of_rank_le_six
    (h : MinimalObstruction c k t S) (hb : Balanced c) (hr : 6≤r) (lo : 4≤t) (high : t≤6)
    (ht : t<r) {x : V} (hx : x∈S) (deg : (S.filter ((colorGraph c k).Adj x)).card=r) :
    r*S.card+(r-4) ≤ blockEdges (colorGraph c k) S+(r.choose 2+1)*t+(r-1) := by
  let W := S \ insert x (S.filter ((colorGraph c k).Adj x))
  have ⟨ws,sz,rk⟩ := h.degree_eq_nonneighbor_data (by omega) (by omega) hx deg
  change W⊂S at ws
  change W.card=(t-1)*r at sz
  change rankOn (colorGraph c k) W=t-1 at rk
  exact h.closed_neighborhood_slack hb hr lo ht hx deg (h.saturated_inseparable hb hr ht ws
    (card_pos.mp (by rw [sz]; exact Nat.mul_pos (by omega) (by omega))) (by rw [rk,sz])
    (by rw [rk]; omega))

/-- A sparse rank-five obstruction at nine colors cannot exist. -/
theorem MinimalObstruction.not_nine_five_of_edges {c : Sym2 V → Fin 9} {k : Fin 9}
    (h : MinimalObstruction c k 5 S) (hb : Balanced c) (bound : blockEdges (colorGraph c k) S≤225) :
    False := by
  classical
  let G := colorGraph c k
  have sz : S.card=46 := h.card_eq
  obtain ⟨x,hx,deg⟩ : ∃ x∈S, (S.filter (G.Adj x)).card=9 := by
    by_contra! no
    have d := sum_le_sum (s:=S) (f:=fun _ => 10) (g:=fun y => (S.filter (G.Adj y)).card)
      (fun y hy => by have lo := h.degree_ge y hy; change 9≤(S.filter (G.Adj y)).card at lo; have := no y hy; omega)
    rw [block_degree_sum,sum_const,nsmul_eq_mul,sz] at d
    change blockEdges G S≤225 at bound
    omega
  have elim := h.closed_neighborhood_slack_of_rank_le_six hb (by decide) (by decide) (by decide) (by decide) hx deg
  rw [sz] at elim
  norm_num [Nat.choose] at elim
  omega

end Erdos617
