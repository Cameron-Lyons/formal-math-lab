import Erdos617.ClosedNeighborhoodSlack

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {r s : ℕ}
variable {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V}

/-- If an odd-endpoint core is sparse, every vertex of minimum possible degree
leaves a rank-additively decomposable set after deleting its closed neighborhood.
There are at least r+1 vertices with this property. -/
theorem odd_sparse_residual_split (hs : 4≤s) (hr : r=2*s+1) (hb : Balanced c)
    (hk : 2*(colorGraph c k).edgeFinset.card ≤ r*(r^2+1))
    (h : MinimalObstruction c k (s+1) S) (P : Finset (Finset V)) (np : P.card=s)
    (uni : P.biUnion id=univ \ S) (hd : (↑P : Set (Finset V)).PairwiseDisjoint id)
    (hc : ∀ T∈P,(colorGraph c k).IsNClique r T) :
    let G := colorGraph c k
    let L := S.filter (fun x => (S.filter (G.Adj x)).card=r)
    r+1≤L.card ∧ ∀ x∈L, let W := S \ insert x (S.filter (G.Adj x))
      W.card=s*r ∧ rankOn G W=s ∧
      ∃ A B : Finset V, A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ A∪B=W ∧
        rankOn G A + rankOn G B=s ∧ A.card=rankOn G A*r ∧ B.card=rankOn G B*r ∧
        3≤rankOn G A ∧ 3≤rankOn G B := by
  classical
  intro G L
  let delta (x : V) := (S.filter (G.Adj x)).card-r
  have bound := odd_core_excess (by omega) hr hk h P np uni hd hc
  change ∑ x∈S,delta x ≤ s*r at bound
  have size := h.card_eq
  have sx : S.card=s*r+r+1 := by simpa [Nat.succ_mul] using size
  have rest : ∀ x∈S \ L, 1≤delta x := by
    intro x hx
    have hs := (mem_sdiff.mp hx).1
    have lower := h.degree_ge x hs
    have ne : (S.filter (G.Adj x)).card≠r := fun eq => (mem_sdiff.mp hx).2 (mem_filter.mpr ⟨hs,eq⟩)
    change r≤(S.filter (G.Adj x)).card at lower
    dsimp [delta]; omega
  have positive := sum_le_sum rest
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at positive
  have all := sum_le_sum_of_subset (f:=delta) (sdiff_subset : S\L⊆S)
  have split := card_sdiff_add_card_eq_card (filter_subset (fun x => (S.filter (G.Adj x)).card=r) S)
  change (S\L).card+L.card=S.card at split
  refine ⟨by omega,?_⟩
  intro x hx W
  have ⟨mem,deg⟩ := mem_filter.mp hx
  have ⟨ws,sz,rk⟩ := h.degree_eq_nonneighbor_data (by omega) (by omega) mem deg
  simp only [Nat.add_sub_cancel] at sz rk
  change W⊂S at ws
  change W.card=s*r at sz
  change rankOn G W=s at rk
  refine ⟨sz,rk,?_⟩
  have eq : (∑ x∈S,delta x)+S.card*r=2*blockEdges G S := by
    rw [←block_degree_sum,show S.card*r=∑ _∈S,r by simp,←sum_add_distrib]
    exact sum_congr rfl fun x hx => Nat.sub_add_cancel (h.degree_ge x hx)
  have small : ¬RankInseparable G W := by
    intro inseparable
    have sl := h.closed_neighborhood_slack hb (by omega) (by omega) (by omega) mem deg inseparable
    change r*S.card+(r-4) ≤ blockEdges G S+(r.choose 2+1)*(s+1)+(r-1) at sl
    have ch := congrArg (fun z => z*(s+1)) (twice_choose_two r)
    have prod := congrArg (r*·) size
    have pred := Nat.sub_add_cancel (show 4≤r by omega)
    have pred' := Nat.sub_add_cancel (show 1≤r by omega)
    have degBound := Nat.add_le_add_right bound (S.card*r)
    rw [eq] at degBound
    nlinarith only [sl,degBound,ch,prod,pred,pred',hr,hs]
  have nz : W.Nonempty := card_pos.mp (by rw [sz]; exact Nat.mul_pos (by omega) (by omega))
  have notAll : ¬ ∀ {A B : Finset V}, A.Nonempty → B.Nonempty → Disjoint A B →
      A∪B=W → rankOn G W<rankOn G A+rankOn G B := fun yes => small ⟨nz,yes⟩
  push Not at notAll
  obtain ⟨A,B,ha,hb',dis,un,low⟩ := notAll
  have subA : A⊆W := un ▸ subset_union_left
  have subB : B⊆W := un ▸ subset_union_right
  have upper := rankOn_union_le G A B
  rw [un,rk] at upper
  rw [rk] at low
  have exactSum := le_antisymm low upper
  have limit {A : Finset V} (sub : A⊆W) : A.card≤rankOn G A*r := by
    obtain ⟨J,hJ,ind,sm⟩ := h.proper_subset (by omega) A (sub.trans_ssubset ws)
    exact sm.trans (Nat.mul_le_mul_right _ (card_le_rankOn G hJ ind))
  have count := congrArg card un
  rw [card_union_of_disjoint dis,sz] at count
  have count' := congrArg (·*r) exactSum
  rw [Nat.add_mul] at count'
  have limA := limit subA
  have limB := limit subB
  have eqA : A.card=rankOn G A*r := by omega
  have eqB : B.card=rankOn G B*r := by omega
  exact ⟨A,B,ha,hb',dis,un,exactSum,eqA,eqB,
    h.three_le_tight_rank hb (by omega) (by omega) (subA.trans ws.le) ha eqA,
    h.three_le_tight_rank hb (by omega) (by omega) (subB.trans ws.le) hb' eqB⟩

/-- For the first two odd parameters where the split applies, an obstruction
already occurs strictly below the odd half-range endpoint. -/
theorem exists_obstruction_below_small_odd_endpoint (hs : 4≤s) (sc : s≤5) (hr : r=2*s+1)
    (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c) :
    ∃ (k : Fin r) (t : ℕ) (S : Finset V), 5≤t ∧ t≤s ∧ MinimalObstruction c k t S := by
  classical
  by_contra! absent
  have none (k : Fin r) (t : ℕ) (le : t≤s) (S : Finset V) (h : MinimalObstruction c k t S) : False :=
    absent k t S (h.five_le_of_nine_le hb (by omega) (by omega)) le h
  obtain ⟨k,_,_,hk,_⟩ := odd_endpoint_two_sparse (by omega) hr hn c hb none
  obtain ⟨S,P,h,hp,hu,hd,hc⟩ := odd_endpoint_of_sparse_color (by omega) hr hn c hb k hk (none k)
  obtain ⟨many,split⟩ := odd_sparse_residual_split hs hr hb hk h P hp hu hd hc
  have pos := card_pos.mp (lt_of_lt_of_le (Nat.zero_lt_succ r) many)
  obtain ⟨x,hx⟩ := pos
  obtain ⟨_,_,A,B,_,_,_,_,ranks,_,_,a,b⟩ := split x hx
  omega

/-- Any balanced eleven-coloring on 122 vertices has a first obstruction of rank five. -/
theorem exists_rank_five_eleven {V : Type*} [Fintype V] [DecidableEq V]
    (hn : Fintype.card V=11^2+1) (c : Sym2 V → Fin 11) (hb : Balanced c) :
    ∃ (k : Fin 11) (S : Finset V), MinimalObstruction c k 5 S := by
  obtain ⟨k,t,S,lo,hi,h⟩ := exists_obstruction_below_small_odd_endpoint (s:=5)
    (by decide) (by decide) (by decide) hn c hb
  have e : t=5 := by omega
  exact ⟨k,S,e ▸ h⟩

end Erdos617
