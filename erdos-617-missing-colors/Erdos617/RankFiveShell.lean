import Erdos617.ThreePairCosts
import Erdos617.DeletionRank
import Erdos617.BlockAccount

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] {r t : ℕ} {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V}

/-- Minimum-degree elimination records the edge cost and the total weight
of any set of endpoints used to bound that cost. -/
theorem rank_shell_account (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (pos : A.Nonempty) :
    ∃ d W cost B, W⊂A ∧ W.card+d+1=A.card ∧ rankOn G W+1≤rankOn G A ∧
      blockEdges G A=(d+1).choose 2+cost+blockEdges G W ∧ A.card*d≤2*blockEdges G A ∧
      B⊆A ∧ B.card=d+1 ∧
      ∀ L, (∀ D⊆W, rankOn G D+2≤rankOn G A → D.card+L≤W.card) →
        ∃ w : V → ℕ, (∀ a∈B, ∀ b∈B, a≠b → ¬G.Adj a b → L≤w a+w b) ∧
          ∀ U⊆B, (∑ u∈U,w u) ≤ cost+U.card.choose 2 := by
  classical
  let deg (z : V) := (A.filter (G.Adj z)).card
  obtain ⟨x,hx,min⟩ := A.exists_min_image deg pos
  let B := insert x (A.filter (G.Adj x))
  let W := A \ B
  have ba : B⊆A := insert_subset hx (filter_subset ..)
  have sz : B.card=deg x+1 := card_insert_of_notMem (by simp)
  have ws : W⊂A := (ssubset_iff_of_subset sdiff_subset).mpr ⟨x,hx,fun h => (mem_sdiff.mp h).2 (mem_insert_self ..)⟩
  have n := card_sdiff_add_card_eq_card ba
  change W.card+B.card=A.card at n
  have dis : Disjoint B W := disjoint_sdiff
  have uni : B∪W=A := union_sdiff_of_subset ba
  have mind (z : V) (hz : z∈B) : B.card≤((B∪W).filter (G.Adj z)).card+1 := by
    rw [uni,sz]; exact Nat.succ_le_succ (min z (ba hz))
  obtain ⟨cost,eq,_,_,_,budget⟩ := block_account_with_subsets G B W dis mind
  rw [uni,sz] at eq
  refine ⟨deg x,W,cost,B,ws,by omega,?_,eq,?_,ba,sz,?_⟩
  · obtain ⟨I,hi,ind,ei⟩ := exists_max_indep G W
    have xi : x∉I := fun hy => (mem_sdiff.mp (hi hy)).2 (mem_insert_self ..)
    have ind' := independent_insert_of_nonadjacent G ind x (by
      intro z hz e
      exact (mem_sdiff.mp (hi hz)).2 (mem_insert_of_mem (mem_filter.mpr ⟨ws.le (hi hz),e⟩)))
    have bound := card_le_rankOn G (insert_subset hx (hi.trans ws.le)) ind'
    rwa [card_insert_of_notMem xi,ei] at bound
  · have tot := sum_le_sum min
    rw [←block_degree_sum]
    simpa [deg] using tot
  · intro L lim
    let w (a : V) := (W.filter (G.Adj a)).card
    have cover (a : V) (ha : a∈B) (b : V) (hb' : b∈B) (ab : a≠b) (non : ¬G.Adj a b) : L≤w a+w b := by
      let N := W.filter (G.Adj a) ∪ W.filter (G.Adj b)
      let D := W \ N
      have inside : N⊆W := union_subset (filter_subset ..) (filter_subset ..)
      have count := card_sdiff_add_card_eq_card inside
      change D.card+N.card=W.card at count
      obtain ⟨I,hi,ind,eq⟩ := exists_max_indep G D
      have iw : I⊆W := hi.trans sdiff_subset
      have na : a∉W := Finset.disjoint_left.mp dis ha
      have nb : b∉W := Finset.disjoint_left.mp dis hb'
      have ia := independent_insert_of_nonadjacent G ind a (by
        intro z hz e; exact (mem_sdiff.mp (hi hz)).2 (mem_union_left _ (mem_filter.mpr ⟨iw hz,e⟩)))
      have ib := independent_insert_of_nonadjacent G ia b (by
        intro z hz e
        rcases mem_insert.mp hz with rfl|hz
        · exact non e.symm
        · exact (mem_sdiff.mp (hi hz)).2 (mem_union_right _ (mem_filter.mpr ⟨iw hz,e⟩)))
      have bni : b∉insert a I := by simp [Ne.symm ab,show b∉I from fun h => nb (iw h)]
      have rk := card_le_rankOn G (insert_subset (ba hb') (insert_subset (ba ha) (iw.trans ws.le))) ib
      rw [card_insert_of_notMem bni,card_insert_of_notMem (fun h => na (iw h)),eq] at rk
      have bound := lim D sdiff_subset rk
      have count' : N.card≤w a+w b := card_union_le ..
      omega
    exact ⟨w,cover,budget⟩

/-- Minimum-degree elimination with an edge lower bound coming from the
maximum order of a common nonneighborhood of an independent pair. -/
theorem MinimalObstruction.rank_shell (h : MinimalObstruction c k t S)
    (hb : Balanced c) (hr : 10≤r) (ht : t<r) {A : Finset V} (sub : A⊆S) (pos : A.Nonempty) :
    let G := colorGraph c k
    ∃ d W cost, W⊂A ∧ W.card+d+1=A.card ∧ rankOn G W+1≤rankOn G A ∧
      blockEdges G A=(d+1).choose 2+cost+blockEdges G W ∧ A.card*d≤2*blockEdges G A ∧
      (∀ L, (∀ D⊆W, rankOn G D+2≤rankOn G A → D.card+L≤W.card) →
        (d+1=r → L≤cost+1) ∧ (d=r → 2*L≤cost+6) ∧ (d=r+1 → 3*L≤cost+15)) := by
  intro G
  obtain ⟨d,W,cost,B,ws,card,rank,eq,avg,ba,sz,data⟩ := rank_shell_account G A pos
  refine ⟨d,W,cost,ws,card,rank,eq,avg,?_⟩
  intro L lim
  obtain ⟨w,cover,budget⟩ := data L lim
  obtain ⟨one,two,three⟩ := missing_edge_endpoint_cost hr hb
    (fun T hT => h.no_clique hb ht T (hT.trans (ba.trans sub))) w cover budget
  exact ⟨fun eq => one (by omega),fun eq => two (by omega),fun eq => three (by omega)⟩

end Erdos617
