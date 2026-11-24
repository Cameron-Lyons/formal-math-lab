import Erdos617.BlockEdgeBound
import Erdos617.BlockAccount
import Erdos617.GlobalCliqueEnergy

namespace Erdos617

open Finset SimpleGraph

/-- Sum the edges inside the full rows and the lower bounds between them. -/
theorem parallel_family_induced_floor {V : Type*} [Fintype V] [DecidableEq V]
    {r m : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (R : Fin m → Finset V)
    (full : ∀ i,G.IsNClique r (R i)) (dis : Pairwise fun i j => Disjoint (R i) (R j))
    (matchCost : ∀ i j,i≠j → m-1≤∑ u∈R i,((R j).filter (G.Adj u)).card) :
    m*(r*(r-1)+(m-1)*(m-1)) ≤ 2*blockEdges G (univ.biUnion R) := by
  classical
  let Y := univ.biUnion R
  let deg (u : V) (j : Fin m) := ((R j).filter (G.Adj u)).card
  have split (u : V) : (Y.filter (G.Adj u)).card=∑ j,deg u j := by
    dsimp only [Y,deg]
    rw [filter_biUnion,card_biUnion]
    intro i _ j _ ne
    exact (dis ne).mono (filter_subset ..) (filter_subset ..)
  have own (i : Fin m) (u : V) (hu : u∈R i) : deg u i=r-1 := by
    have eq : (R i).filter (G.Adj u)=(R i).erase u := by
      ext z
      constructor
      · intro h
        exact mem_erase.mpr ⟨(mem_filter.mp h).2.ne.symm,(mem_filter.mp h).1⟩
      · intro h
        exact mem_filter.mpr ⟨(mem_erase.mp h).2,(full i).isClique hu (mem_erase.mp h).2 (mem_erase.mp h).1.symm⟩
    simp [deg,eq,card_erase_of_mem hu,(full i).card_eq]
  have per (i : Fin m) : r*(r-1)+(m-1)*(m-1)≤∑u∈R i,(Y.filter (G.Adj u)).card := by
    simp_rw [split]
    rw [sum_comm]
    have cross := sum_le_sum (s:=univ.erase i) fun j hj => matchCost i j (mem_erase.mp hj).1.symm
    simp only [sum_const,card_erase_of_mem (mem_univ _),card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at cross
    have diag := sum_congr (s₁:=R i) rfl (own i)
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id,(full i).card_eq] at diag
    rw [←sum_erase_add _ _ (mem_univ i),diag]
    change (m-1)*(m-1)≤∑ j∈univ.erase i,∑u∈R i,deg u j at cross
    omega
  have all := sum_le_sum (s:=univ) fun i _ => per i
  rw [←sum_biUnion (fun _ _ _ _ ne => dis ne)] at all
  change _≤∑u∈Y,(Y.filter (G.Adj u)).card at all
  rw [block_degree_sum] at all
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at all
  exact all

/-- Count every within-row edge, every forced cross-row matching, and the
edges from the last vertex into the rows. -/
theorem parallel_row_edge_floor {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (R : Fin r → Finset V)
    (full : ∀ i,G.IsNClique r (R i)) (dis : Pairwise fun i j => Disjoint (R i) (R j))
    (x : V) (outside : ∀ i,x∉R i) (cover : {x}∪univ.biUnion R=univ)
    (spokes : ∀ i,((R i).filter (G.Adj x)).card=1)
    (matchCost : ∀ i j,i≠j → r-1≤∑ u∈R i,((R j).filter (G.Adj u)).card) :
    r*(r*(r-1)+(r-1)*(r-1))+2*r ≤ 2*G.edgeFinset.card := by
  classical
  let Y := univ.biUnion R
  have all := parallel_family_induced_floor G R full dis matchCost
  change _ ≤ 2*blockEdges G Y at all
  have ex : (Y.filter (G.Adj x)).card=r := by
    dsimp only [Y]
    rw [filter_biUnion,card_biUnion]
    · simp [spokes]
    · intro i _ j _ ne
      exact (dis ne).mono (filter_subset ..) (filter_subset ..)
  have dx : Disjoint {x} Y := disjoint_singleton_left.mpr (by
    intro h
    obtain ⟨i,_,m⟩ := mem_biUnion.mp h
    exact outside i m)
  have total := blockEdges_union G dx
  change {x}∪Y=univ at cover
  rw [cover,blockEdges_univ,sum_singleton,ex] at total
  omega

/-- Add a per-vertex degree bound on the complement of a row family to the
edges already forced by that family. Cross edges contribute at both ends. -/
theorem parallel_rows_with_tail_floor {V : Type*} [Fintype V] [DecidableEq V]
    {r m : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (R : Fin m → Finset V)
    (full : ∀ i,G.IsNClique r (R i)) (dis : Pairwise fun i j => Disjoint (R i) (R j))
    (matchCost : ∀ i j,i≠j → m-1≤∑u∈R i,((R j).filter (G.Adj u)).card)
    (T : Finset V) (apart : Disjoint T (univ.biUnion R)) (cover : T∪univ.biUnion R=univ)
    (per : ∀ v∈T,r≤(T.filter (G.Adj v)).card+2*((univ.biUnion R).filter (G.Adj v)).card) :
    m*(r*(r-1)+(m-1)*(m-1))+r*T.card≤2*G.edgeFinset.card := by
  have low := parallel_family_induced_floor G R full dis matchCost
  have tail := sum_le_sum per
  rw [sum_const,nsmul_eq_mul,Nat.cast_id,sum_add_distrib,←mul_sum,block_degree_sum] at tail
  have all := blockEdges_union G apart
  rw [cover,blockEdges_univ] at all
  rw [Nat.mul_comm r T.card]
  omega

/-- The ordinary refined Turán floors in the other r−1 colors are
incompatible with the simultaneous matching cost in one color. -/
theorem parallel_row_budget_impossible {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (hr : 3≤r) (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r)
    (heavy : r*(r*(r-1)+(r-1)*(r-1))+2*r≤2*(colorGraph c k).edgeFinset.card) : False := by
  classical
  let E (j : Fin r) := (colorGraph c j).edgeFinset.card
  have per (j : Fin r) (hj : j∈univ.erase k) : r*r.choose 2+2*r-1≤E j := by
    apply edge_bound_of_clique_and_indep_caps _ (by omega : 2≤r) (by simpa [pow_two] using hn)
    · intro T hT
      have a := hT.isIndepSet.card_le_indepNum.trans (balanced_indepNum_le c hb j)
      rw [hT.card_eq] at a
      omega
    · intro T cl
      obtain ⟨a,ha,b,hb',ab,edge⟩ := hb T cl.card_eq k
      exact (mem_erase.mp hj).1 ((cl.isClique ha hb' ab).2.symm.trans edge)
  have total := sum_le_sum per
  simp only [sum_const,card_erase_of_mem (mem_univ k),card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at total
  have split := sum_erase_add univ E (mem_univ k)
  have edges : ∑j,E j=(r^2+1).choose 2 := (sum_color_edges c).trans (by rw [hn])
  rw [edges] at split
  change _≤2*E k at heavy
  obtain ⟨a,rfl⟩ : ∃ a,r=a+3 := ⟨r-3,by omega⟩
  have floor : (a+3)*(a+3).choose 2+2*(a+3)-1=(a+3)*(a+3).choose 2+2*a+5 := by omega
  rw [floor,show a+3-1=a+2 by omega] at total
  rw [show a+3-1=a+2 by omega] at heavy
  nlinarith only [total,split,heavy,twice_choose_two ((a+3)^2+1),
    congrArg ((a+2)*(a+3)*·) (twice_choose_two (a+3)),Nat.zero_le (a*a),Nat.zero_le a]

end Erdos617
