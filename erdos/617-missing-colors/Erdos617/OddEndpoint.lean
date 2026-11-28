module

public import Erdos617.HalfRange
public import Erdos617.RankEquality

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] {r s : ℕ} {c : Sym2 V → Fin r} {k : Fin r}

omit [DecidableEq V] in
theorem local_rank_cap
    (hsmall : ∀ (a : ℕ), a ≤ s → ∀ W : Finset V, ¬MinimalObstruction c k a W)
    (X : Finset V) (hX : rankOn (colorGraph c k) X ≤ s) :
    X.card ≤ rankOn (colorGraph c k) X*r := by
  by_contra! hn
  obtain ⟨W,hW,hc⟩ := exists_subset_card_eq (s := X) (Nat.succ_le_of_lt hn)
  have no (I : Finset V) (hi : I ⊆ W) (hr : (colorGraph c k).IsNIndepSet
      (rankOn (colorGraph c k) X+1) I) : False := by
    have hh := card_le_rankOn _ (hi.trans hW) hr.isIndepSet
    rw [hr.card_eq] at hh
    omega
  obtain ⟨a,A,ha,_,hm⟩ := minimalObstruction_of_failure hc no
  exact hsmall a (ha.trans hX) A hm

private theorem degree_on_large_part (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (ha : rankOn G A=s+1)
    (hsmall : ∀ X : Finset V, rankOn G X ≤ s → X.card ≤ rankOn G X*r)
    (d : ℕ) (hn : A.card=(s+1)*r+2+d) :
    (r+1+d)*A.card ≤ 2*blockEdges G A := by
  classical
  have per (x : V) (hx : x ∈ A) : r+1+d ≤ (A.filter (G.Adj x)).card := by
    let W := (A.erase x).filter fun y => ¬G.Adj x y
    obtain ⟨I,hI,hi,hnI⟩ := exists_max_indep G W
    have hxI : x ∉ I := fun he => (mem_erase.mp (mem_filter.mp (hI he)).1).1 rfl
    have hi' := independent_insert_of_nonadjacent G hi x (fun y hy => (mem_filter.mp (hI hy)).2)
    have big := card_le_rankOn G (insert_subset hx (hI.trans ((filter_subset ..).trans (erase_subset ..)))) hi'
    rw [card_insert_of_notMem hxI,hnI,ha] at big
    have small := (hsmall W (by omega)).trans (Nat.mul_le_mul_right r (show rankOn G W≤s by omega))
    have split := card_filter_add_card_filter_not (s := A.erase x) (G.Adj x)
    have adj := card_le_card (filter_subset_filter (G.Adj x) (erase_subset x A))
    change ((A.erase x).filter (G.Adj x)).card+W.card=(A.erase x).card at split
    rw [card_erase_of_mem hx,hn,Nat.succ_mul] at split
    omega
  have sum := sum_le_sum per
  simpa [block_degree_sum,Nat.mul_comm] using sum

/-- On a part of rank s+1, exceeding the nominal order by even one extra vertex
costs at least s+1 edges above the supporting rank-density inequality. -/
private theorem extra_vertex_cost {r s n e d : ℕ} (hr : r=2*s+1) (hn : n=(s+1)*r+2+d)
    (he : (r+1+d)*n ≤ 2*e) : r*n+(s+1) ≤ e+(r.choose 2+1)*(s+1)+(r-1) := by
  have ch := congrArg (fun z => z*(s+1)) (twice_choose_two r)
  subst r
  subst n
  simp only [Nat.add_sub_cancel] at *
  nlinarith only [he,ch,Nat.zero_le (d*d),Nat.zero_le (s*s*d),Nat.zero_le (s*d),Nat.zero_le d]

private theorem sparse_budget_short {r s e : ℕ} (hr : r=2*s+1) (he : 2*e ≤ r*(r^2+1)) :
    e+(r.choose 2+1)*r+(r-1)*(s+1) < r*(r^2+1)+(s+1) := by
  have ch := congrArg (fun z => z*r) (twice_choose_two r)
  subst r
  simp only [Nat.add_sub_cancel]
  nlinarith only [he,ch]

/-- At the odd endpoint, the complement of a first obstruction in any
below-average color is partitioned by s full monochromatic cliques. -/
theorem odd_endpoint_of_sparse_color [Fintype V] (hs : 1 ≤ s) (hr : r=2*s+1)
    (hV : Fintype.card V = r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r)
    (hk : 2*(colorGraph c k).edgeFinset.card ≤ r*(r^2+1))
    (hsmall : ∀ (a : ℕ), a ≤ s → ∀ W : Finset V, ¬MinimalObstruction c k a W) :
    ∃ (A : Finset V) (Q : Finset (Finset V)), MinimalObstruction c k (s+1) A ∧
      Q.card=s ∧ Q.biUnion id=univ \ A ∧ (↑Q : Set (Finset V)).PairwiseDisjoint id ∧
      ∀ C ∈ Q, (colorGraph c k).IsNClique r C := by
  classical
  let G := colorGraph c k
  have low (X : Finset V) (hX : rankOn G X ≤ s) : X.card ≤ rankOn G X*r :=
    local_rank_cap hsmall X hX
  have α : rankOn G univ ≤ r := by
    obtain ⟨I,_,hi,hn⟩ := exists_max_indep G univ
    by_contra! hh
    obtain ⟨B,hB,hcard⟩ := exists_subset_card_eq (s:=I) (show r+1≤I.card by omega)
    obtain ⟨x,hx,y,hy,hxy,he⟩ := hb B hcard k
    exact hi (hB hx) (hB hy) hxy ⟨hxy,he⟩
  obtain ⟨P,hu,hd,hat,ha⟩ := exists_rank_partition G univ
  have hsum := card_biUnion hd
  simp only [id_eq,hu,card_univ,hV] at hsum
  have hdens := rank_partition_density G P hd hat r
  rw [hu,card_univ,hV,blockEdges_univ,ha] at hdens
  have α' := Nat.mul_le_mul_left (r.choose 2+1) α
  change 2*G.edgeFinset.card ≤ r*(r^2+1) at hk
  have hp := rank_parts_of_edge_budget (by omega : 3≤r) hk
    (show r*(r^2+1) ≤ G.edgeFinset.card+(r.choose 2+1)*r+(r-1)*P.card by omega)
  obtain ⟨A,hA,large⟩ : ∃ A ∈ P, rankOn G A*r < A.card := by
    by_contra! bounds
    have hh := sum_le_sum bounds
    rw [←sum_mul,ha,←hsum] at hh
    have := Nat.mul_le_mul_right r α
    rw [pow_two] at hh
    omega
  have ranklarge : s < rankOn G A := by
    by_contra! hh
    exact large.not_ge (low A hh)
  let Q := P.erase A
  have qcard : Q.card=P.card-1 := card_erase_of_mem hA
  have qrank := sum_erase_add P (rankOn G) hA
  change (∑ C ∈ Q, rankOn G C)+rankOn G A=_ at qrank
  rw [ha] at qrank
  have pos (C : Finset V) (hC : C∈Q) : 1≤rankOn G C := (hat C (mem_of_mem_erase hC)).rank_pos
  have hnum := sum_le_sum pos
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at hnum
  have qc : Q.card=s := by omega
  have ra : rankOn G A=s+1 := by omega
  have rs : (∑ C ∈ Q,rankOn G C)=s := by omega
  have one (C : Finset V) (hC : C∈Q) : rankOn G C=1 := by
    apply Eq.symm
    apply (sum_eq_sum_iff_of_le pos).mp _ C hC
    simp [rs,qc]
  have cap (C : Finset V) (hC : C ∈ Q) : C.card≤r := by
    have hh := low C (by rw [one C hC]; exact hs)
    simpa only [one C hC,Nat.one_mul] using hh
  have qsize := sum_erase_add P card hA
  change (∑ C ∈ Q,C.card)+A.card=_ at qsize
  rw [←hsum] at qsize
  have qa := sum_erase_add P (blockEdges G) hA
  change (∑ C ∈ Q,blockEdges G C)+blockEdges G A=_ at qa
  have be := boundary_edge_count G univ P hu.le hd
  rw [blockEdges_univ] at be
  have ac : A.card=(s+1)*r+1 := by
    rw [ra] at large
    by_contra neq
    obtain ⟨d,nd⟩ : ∃ d, A.card=(s+1)*r+2+d := ⟨A.card-((s+1)*r+2),by omega⟩
    have deg := degree_on_large_part G A ra low d nd
    have extra := extra_vertex_cost hr nd deg
    have row := sum_le_sum (s:=Q) (fun C hC => rank_density G C (hat C (mem_of_mem_erase hC)) r)
    simp only [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,Nat.cast_id,qc,rs] at row
    have total := congrArg (r*·) qsize
    rw [Nat.mul_add] at total
    have split := congrArg (fun z => (r.choose 2+1)*z) (show s+(s+1)=r by omega)
    rw [Nat.mul_add] at split
    have pred : s*(r-1)+(r-1) = (r-1)*(s+1) := by ring
    have short := sparse_budget_short hr hk
    omega
  have sc : (∑ C ∈ Q,C.card)=s*r := by
    rw [ac] at qsize
    have id : s*r+(s+1)*r=r^2 := by rw [←Nat.add_mul,pow_two,show s+(s+1)=r by omega]
    omega
  have allfull (C : Finset V) (hC : C∈Q) : C.card=r := by
    apply (sum_eq_sum_iff_of_le cap).mp _ C hC
    simp [qc,sc]
  have disQ : (↑Q : Set (Finset V)).PairwiseDisjoint id :=
    fun _ hC _ hD hCD => hd (mem_of_mem_erase hC) (mem_of_mem_erase hD) hCD
  have full : A ∪ Q.biUnion id=univ := by
    calc
      _ = (insert A (P.erase A)).biUnion id := by simp only [biUnion_insert,id_eq,Q]
      _ = _ := by rw [insert_erase hA,hu]
  have cover : Q.biUnion id=univ \ A := by
    ext x
    constructor
    · intro hx
      obtain ⟨B,hB,hx⟩ := mem_biUnion.mp hx
      exact mem_sdiff.mpr ⟨mem_univ _,fun h => disjoint_left.mp
        (hd (mem_of_mem_erase hB) hA (mem_erase.mp hB).1) hx h⟩
    · intro hx
      have := mem_univ x
      rw [←full,mem_union] at this
      exact this.resolve_left (mem_sdiff.mp hx).2
  refine ⟨A,Q,⟨ac,?_,?_⟩,qc,cover,disQ,fun C hC => ⟨rank_one_clique G (one C hC),allfull C hC⟩⟩
  · intro I hI hi
    have hα := card_le_rankOn G hI hi.isIndepSet
    rw [hi.card_eq,ra] at hα
    omega
  · intro a small W _ hn
    by_contra! absent
    obtain ⟨v,T,hv,_,hbad⟩ := minimalObstruction_of_failure hn absent
    exact hsmall v (by omega) T hbad

/-- In an odd palette, either a smaller obstruction exists or a sparse color
has a first obstruction and s disjoint full cliques covering its complement. -/
theorem odd_endpoint_dichotomy [Fintype V] (hs : 1 ≤ s) (hr : r=2*s+1)
    (hV : Fintype.card V = r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c) :
    (∃ (k : Fin r) (a : ℕ) (W : Finset V), a ≤ s ∧ MinimalObstruction c k a W) ∨
      ∃ (k : Fin r) (A : Finset V) (Q : Finset (Finset V)),
        2*(colorGraph c k).edgeFinset.card ≤ r*(r^2+1) ∧ MinimalObstruction c k (s+1) A ∧
        Q.card=s ∧ Q.biUnion id=univ \ A ∧ (↑Q : Set (Finset V)).PairwiseDisjoint id ∧
        ∀ C ∈ Q, (colorGraph c k).IsNClique r C := by
  classical
  by_cases smaller : ∃ (k : Fin r) (a : ℕ) (W : Finset V), a ≤ s ∧ MinimalObstruction c k a W
  · exact Or.inl smaller
  right
  obtain ⟨k,hk⟩ := exists_color_edge_budget (by omega) hV c
  obtain ⟨A,Q,hA,hq,hu,hd,hfull⟩ := odd_endpoint_of_sparse_color hs hr hV c hb k hk
    (fun a ha W hm => smaller ⟨k,a,W,ha,hm⟩)
  exact ⟨k,A,Q,hk,hA,hq,hu,hd,hfull⟩

end Erdos617
