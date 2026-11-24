import Erdos617.OddEndpoint
import Erdos617.RankIntersection

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] {r s : ℕ} {c : Sym2 V → Fin r} {k : Fin r}

/-- Above the rank-s threshold, removing extra vertices reduces the number
of edges by at least r per vertex, down to a first obstruction of order sr+1. -/
theorem extract_minimal_with_edge_slope (hs : 0<s)
    (none : ∀ a<s, ∀ T : Finset V, ¬MinimalObstruction c k a T)
    (A : Finset V) (rk : rankOn (colorGraph c k) A≤s) (large : s*r+1≤A.card) :
    ∃ W⊆A, MinimalObstruction c k s W ∧
      blockEdges (colorGraph c k) W+r*A.card≤blockEdges (colorGraph c k) A+r*W.card := by
  classical
  let G := colorGraph c k
  have small (D : Finset V) (cap : rankOn G D<s) : D.card≤(s-1)*r :=
    (local_rank_cap (s:=s-1) (fun u hu => none u (by omega)) D (by change rankOn G D≤s-1; omega)).trans
      (Nat.mul_le_mul_right r (by change rankOn G D≤s-1; omega))
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    by_cases eq : A.card=s*r+1
    · refine ⟨A,Subset.rfl,⟨eq,?_,?_⟩,le_rfl⟩
      · intro I sub ind
        have cap := (card_le_rankOn _ sub ind.isIndepSet).trans rk
        rw [ind.card_eq] at cap
        omega
      · intro a ha D _ sz
        by_contra! no
        obtain ⟨b,T,le,_,h⟩ := minimalObstruction_of_failure sz no
        exact none b (by omega) T h
    obtain ⟨x,hx⟩ := card_pos.mp (show 0<A.card by omega)
    have sub := erase_ssubset hx
    obtain ⟨W,iw,h,bound⟩ := ih _ sub ((rankOn_mono G sub.le).trans rk) (by rw [card_erase_of_mem hx]; omega)
    let D := (A.erase x).filter fun y => ¬G.Adj x y
    have cap : rankOn G D<s := by
      obtain ⟨I,hI,ind,ord⟩ := exists_max_indep G D
      have inside : D⊆A.erase x := filter_subset ..
      have xx : x∉I := fun mem => notMem_erase x A (inside (hI mem))
      have plus := independent_insert_of_nonadjacent G ind x (fun _ hi => (mem_filter.mp (hI hi)).2)
      have lim := (card_le_rankOn G (insert_subset hx ((hI.trans inside).trans sub.le)) plus).trans rk
      rwa [card_insert_of_notMem xx,ord] at lim
    have dBound := small D cap
    have count := card_filter_add_card_filter_not (s:=A.erase x) (G.Adj x)
    change ((A.erase x).filter (G.Adj x)).card+D.card=(A.erase x).card at count
    have d := card_le_card (filter_subset_filter (G.Adj x) sub.le)
    have calcRank : (s-1)*r+r=s*r := by rw [←Nat.succ_mul]; congr 1; omega
    have ed := blockEdges_erase_add G A x hx
    have count' := card_erase_add_one hx
    have total := congrArg (r*·) count'
    rw [Nat.mul_add,Nat.mul_one] at total
    refine ⟨W,iw.trans sub.le,h,?_⟩
    change blockEdges G W+r*(A.erase x).card≤blockEdges G (A.erase x)+r*W.card at bound
    change blockEdges G W+r*A.card≤blockEdges G A+r*W.card
    omega

/-- At the even half-range endpoint each average-sparse color has a rank-s
minimal obstruction whose edge slack is at most r−1. -/
theorem even_endpoint_sparse_core [Fintype V] (hs : 2≤s) (ev : 2*s=r)
    (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r)
    (sparse : 2*(colorGraph c k).edgeFinset.card≤r*(r^2+1))
    (none : ∀ a<s, ∀ T : Finset V, ¬MinimalObstruction c k a T) :
    ∃ W : Finset V, MinimalObstruction c k s W ∧
      blockEdges (colorGraph c k) W+(r.choose 2+1)*s≤r*W.card := by
  classical
  let G := colorGraph c k
  let H := r.choose 2+1
  have α : rankOn G univ≤r := by
    obtain ⟨I,_,ind,eq⟩ := exists_max_indep G univ
    by_contra! high
    obtain ⟨J,sub,sz⟩ := exists_subset_card_eq (s:=I) (show r+1≤I.card by omega)
    obtain ⟨a,ha,b,hb',ne,col⟩ := hb J sz k
    exact ind (sub ha) (sub hb') ne ⟨ne,col⟩
  obtain ⟨P,hu,hd,hi,ss⟩ := exists_rank_partition G univ
  have nParts := card_biUnion hd
  simp only [id_eq,hu,card_univ,hn] at nParts
  have dens := rank_partition_density G P hd hi r
  rw [hu,card_univ,hn,blockEdges_univ,ss] at dens
  have mulRank := Nat.mul_le_mul_left H α
  have minParts := rank_parts_of_edge_budget (by omega) sparse (show
    r*(r^2+1)≤G.edgeFinset.card+H*r+(r-1)*P.card by change _≤G.edgeFinset.card+H*rankOn G univ+_ at dens; omega)
  obtain ⟨A,ha,large⟩ : ∃ A∈P, rankOn G A*r<A.card := by
    by_contra! small
    have le := sum_le_sum small
    rw [←nParts,←sum_mul,ss,pow_two] at le
    have := Nat.mul_le_mul_right r α
    omega
  have lower : s≤rankOn G A := by
    by_contra! less
    have cap := local_rank_cap (s:=s-1) (fun a ha => none a (by omega)) A
      (show rankOn G A≤s-1 by omega)
    exact large.not_ge cap
  have ranks := sum_erase_add P (rankOn G) ha
  rw [ss] at ranks
  have cnt := card_erase_of_mem ha
  have otherRank := sum_le_sum (s:=P.erase A) (f:=fun _ => 1) fun B hB => (hi B (mem_of_mem_erase hB)).rank_pos
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at otherRank
  have rhi : rankOn G A<r := by omega
  have npos := card_pos.mpr (show P.Nonempty from ⟨A,ha⟩)
  have sizes := sum_erase_add P card ha
  rw [←nParts] at sizes
  have edges := sum_erase_add P (blockEdges G) ha
  have border := boundary_edge_count G univ P hu.le hd
  rw [blockEdges_univ] at border
  have all := sum_le_sum (s:=P.erase A) fun B hB => rank_density G B (hi B (mem_of_mem_erase hB)) r
  simp only [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,Nat.cast_id] at all
  have total := matching_budget (by omega) sparse ev
  change G.edgeFinset.card+H*r+(r-1)*s ≤ r*(r^2+1) at total
  change r*(∑ B∈P.erase A,B.card) ≤ (∑ B∈P.erase A,blockEdges G B)+H*(∑ B∈P.erase A,rankOn G B)+
    (P.erase A).card*(r-1) at all
  have sizesR := congrArg (r*·) sizes
  have rankR := congrArg (H*·) ranks
  rw [Nat.mul_add] at sizesR rankR
  by_cases eq : rankOn G A=s
  · obtain ⟨W,_,h,sub⟩ := extract_minimal_with_edge_slope (by omega) none A eq.le (by simpa [eq] using large)
    have part := Nat.mul_le_mul_right (r-1) (show (P.erase A).card≤s by omega)
    rw [Nat.mul_comm s (r-1)] at part
    rw [eq] at rankR
    refine ⟨W,h,?_⟩
    change blockEdges G W+r*A.card≤blockEdges G A+r*W.card at sub
    change blockEdges G W+H*s≤r*W.card
    omega
  · have strict : r*A.card<blockEdges G A+H*rankOn G A+(r-1) := by
      refine lt_of_le_of_ne (rank_density G A (hi A ha) r) (fun tight => ?_)
      have endpt := rank_density_order_cap G A (hi A ha) (by omega : 1≤r) tight
      rw [Nat.mul_comm (rankOn G A) r] at large
      obtain ⟨C,hC,cl⟩ := exists_clique_of_rank_density_eq G A (hi A ha) r (by omega) (by omega) tight
      exact (hi A ha).no_full_clique hb (by change 1<rankOn G A; omega) rhi hC cl
    have part := Nat.mul_le_mul_right (r-1) (show (P.erase A).card+1≤s by omega)
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm s (r-1)] at part
    omega

end Erdos617
