module

public import Erdos617.OddIntersection
public import Erdos617.PrivateBlocks
public import Erdos617.FullCliquePropagation

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {r s : ℕ}
variable {c : Sym2 V → Fin r} {k j : Fin r} {S : Finset V}

/-- The full cliques outside an odd-endpoint core pay for most of the sparse
color's edges. The total degree excess remaining inside the core is at most sr. -/
theorem odd_core_excess (_hs : 1 ≤ s) (hr : r=2*s+1)
    (hk : 2*(colorGraph c k).edgeFinset.card ≤ r*(r^2+1))
    (h : MinimalObstruction c k (s+1) S) (P : Finset (Finset V)) (hN : P.card=s)
    (hu : P.biUnion id=univ \ S) (hd : (↑P : Set (Finset V)).PairwiseDisjoint id)
    (hcl : ∀ T∈P,(colorGraph c k).IsNClique r T) :
    (∑ x ∈ S, ((S.filter ((colorGraph c k).Adj x)).card-r)) ≤ s*r := by
  classical
  let G := colorGraph c k
  have dis (T : Finset V) (hT : T∈P) : Disjoint S T :=
    disjoint_sdiff.mono_right (biUnion_subset.mp hu.le T hT)
  have hnot : S∉P := by
    intro hS
    obtain ⟨x,hx⟩ := card_pos.mp (show 0<S.card by rw [h.card_eq]; omega)
    exact disjoint_left.mp (dis S hS) hx hx
  have allD : (↑(insert S P) : Set (Finset V)).PairwiseDisjoint id := by
    rw [coe_insert]
    exact hd.insert fun T hT _ => dis T hT
  have bound := boundary_edge_count G univ (insert S P) (subset_univ _) allD
  have cliqueEdges (C : Finset V) (hC : C∈P) : blockEdges G C=r.choose 2 := by
    let H := G.induce (C : Set V)
    have eq : H=⊤ := G.induce_eq_top.mpr (hcl C hC).isClique
    have eqq : H.edgeFinset=(⊤ : SimpleGraph C).edgeFinset := by
      ext e
      rw [mem_edgeFinset,mem_edgeFinset,eq]
      rfl
    change H.edgeFinset.card=r.choose 2
    rw [eqq,card_edgeFinset_top_eq_card_choose_two,Fintype.card_coe,(hcl C hC).card_eq]
  rw [sum_insert hnot,sum_congr rfl cliqueEdges,sum_const,hN,nsmul_eq_mul,Nat.cast_id,
    blockEdges_univ] at bound
  let e := ∑ x∈S, ((S.filter (G.Adj x)).card-r)
  have cost : e+S.card*r=2*blockEdges G S := by
    rw [← block_degree_sum,show S.card*r = ∑ _ ∈ S,r by simp, ← sum_add_distrib]
    exact sum_congr rfl fun x hx => Nat.sub_add_cancel (h.degree_ge x hx)
  rw [h.card_eq] at cost
  have hc := congrArg (s*·) (twice_choose_two r)
  change e ≤ s*r
  change 2*G.edgeFinset.card ≤ r*(r^2+1) at hk
  have poly := congrArg (r*r*·) hr
  nlinarith only [cost,hk,hc,bound,poly,Nat.zero_le (inducedEdgeSet G univ \ (insert S P).biUnion (inducedEdgeSet G)).card]

/-- On a full j-clique, an outside vertex has at most two spokes of any
specified foreign color k. -/
theorem other_clique_spokes_le_two (hb : Balanced c) (hkj : k ≠ j) {C : Finset V}
    (hC : (colorGraph c j).IsNClique r C) {x : V} (hx : x∉C) :
    (C.filter ((colorGraph c k).Adj x)).card ≤ 2 := by
  classical
  let N (l : Fin r) := C.filter ((colorGraph c l).Adj x)
  have positive (l : Fin r) (hl : l ∈ (univ.erase j).erase k) : 1≤(N l).card := by
    have im := full_clique_maximum_in_other_color c hb (mem_erase.mp (mem_of_mem_erase hl)).1 hC
    by_contra! hz
    have ind := independent_insert_of_nonadjacent _ im.isIndepSet x (by
      intro y hy he
      have : 0<(N l).card := card_pos.mpr ⟨y,mem_filter.mpr ⟨hy,he⟩⟩
      omega)
    have bound := im.maximum _ ind
    rw [card_insert_of_notMem hx] at bound
    omega
  have equal (l : Fin r) : N l=C.filter (fun i => c s(x,i)=l) := by
    ext i
    by_cases hi : i∈C
    · have ne : x≠i := fun h => hx (h ▸ hi)
      simp [N,hi,ne]
    · simp [N,hi]
  have all : ∑ l,(N l).card=r := by
    simp only [equal,sum_card_fiberwise_eq_card_filter,filter_true_of_mem (fun _ _ => mem_univ _),hC.card_eq]
  have hku : k∈univ.erase j := mem_erase.mpr ⟨hkj,mem_univ _⟩
  have cut := sum_erase_add (univ.erase j) (fun l => (N l).card) hku
  have cut' := sum_erase_add univ (fun l => (N l).card) (mem_univ j)
  have low := sum_le_sum positive
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,card_erase_of_mem hku,
    card_erase_of_mem (mem_univ _),card_univ,Fintype.card_fin] at low
  change (N k).card ≤ 2
  omega

/-- A second sparse color supplies a maximum independent set in the core
with total excess at most r. Each outside vertex has at most two neighbors
in this independent set. -/
theorem odd_endpoint_cheap_anchor (hs : 1 ≤ s) (hr : r=2*s+1) (hb : Balanced c)
    (hkj : k≠j) (hk : 2*(colorGraph c k).edgeFinset.card ≤ r*(r^2+1))
    (h : MinimalObstruction c k (s+1) S) (P Q : Finset (Finset V)) (hp : P.card=s)
    (hpu : P.biUnion id=univ \ S) (hpd : (↑P : Set (Finset V)).PairwiseDisjoint id)
    (hpc : ∀ C∈P,(colorGraph c k).IsNClique r C)
    (hq : Q.card=s) (hqd : (↑Q : Set (Finset V)).PairwiseDisjoint id)
    (hqc : ∀ C∈Q,(colorGraph c j).IsNClique r C) :
    ∃ C ∈ Q, let I := C ∩ S
      (colorGraph c k).IsNIndepSet (s+1) I ∧
      (∑ x∈I,(S.filter ((colorGraph c k).Adj x)).card) ≤ (s+1)*r+r ∧
      ∀ x∈S \ I,(I.filter ((colorGraph c k).Adj x)).card ≤ 2 := by
  classical
  let G := colorGraph c k
  let e (x : V) := (S.filter (G.Adj x)).card-r
  have dis : (↑Q : Set (Finset V)).PairwiseDisjoint (fun C => C∩S) :=
    fun _ hC _ hD hCD => (hqd hC hD hCD).mono inter_subset_left inter_subset_left
  have inc : Q.biUnion (fun C => C∩S) ⊆ S := biUnion_subset.mpr fun _ _ => inter_subset_right
  have low := odd_core_excess hs hr hk h P hp hpu hpd hpc
  change (∑ x∈S,e x) ≤ s*r at low
  have cap := (sum_le_sum_of_subset (f:=e) inc).trans low
  rw [sum_biUnion dis] at cap
  obtain ⟨C,hC,small⟩ : ∃ C∈Q, (∑ x∈C∩S,e x) ≤ r := by
    by_contra! big
    have nQ := card_pos.mp (show 0<Q.card by omega)
    have z := sum_lt_sum_of_nonempty nQ big
    simp only [sum_const,hq,nsmul_eq_mul,Nat.cast_id] at z
    omega
  let I := C∩S
  have sz : I.card=s+1 := (full_clique_intersections hkj.symm hr h hp hpu ⟨hpd,hpc⟩ (hqc _ hC)).1
  have ind : G.IsIndepSet (I : Set V) := fun _ hx _ hy hxy ha =>
    hkj (ha.2.symm.trans ((hqc C hC).isClique (mem_inter.mp hx).1 (mem_inter.mp hy).1 hxy).2)
  refine ⟨C,hC,⟨ind,sz⟩,?_,?_⟩
  · have counts : (∑ x∈I,e x)+(s+1)*r = ∑ x∈I,(S.filter (G.Adj x)).card := by
      rw [←sz,show I.card*r=∑ _∈I,r by simp, ←sum_add_distrib]
      exact sum_congr rfl fun x hx => Nat.sub_add_cancel (h.degree_ge x (mem_inter.mp hx).2)
    change (∑ x∈I,e x) ≤ r at small
    change (∑ x∈I,(S.filter (G.Adj x)).card) ≤ _
    omega
  · intro x hx
    have hxC : x∉C := fun hxC => (mem_sdiff.mp hx).2 (mem_inter.mpr ⟨hxC,(mem_sdiff.mp hx).1⟩)
    exact (card_le_card (filter_subset_filter _ inter_subset_left)).trans
      (other_clique_spokes_le_two hb hkj (hqc _ hC) hxC)

/-- Near-full, disjoint private cliques inside a sparse odd-endpoint core.
All vertices left over meet precisely two anchors, and the sum of the row
deficits from order r is at most 3s. -/
theorem odd_endpoint_private_rows (hs : 1 ≤ s) (hr : r=2*s+1) (hb : Balanced c)
    (hkj : k≠j) (hk : 2*(colorGraph c k).edgeFinset.card ≤ r*(r^2+1))
    (h : MinimalObstruction c k (s+1) S) (P Q : Finset (Finset V)) (hp : P.card=s)
    (hpu : P.biUnion id=univ \ S) (hpd : (↑P : Set (Finset V)).PairwiseDisjoint id)
    (hpc : ∀ C∈P,(colorGraph c k).IsNClique r C)
    (hq : Q.card=s) (hqd : (↑Q : Set (Finset V)).PairwiseDisjoint id)
    (hqc : ∀ C∈Q,(colorGraph c j).IsNClique r C) :
    ∃ (C : Finset V) (_ : C∈Q),
    let I := C∩S
    ∃ (B : I → Finset V) (X : Finset V),
      (colorGraph c k).IsNIndepSet (s+1) I ∧
      Pairwise (fun a b => Disjoint (B a) (B b)) ∧
      (∀ a, B a ⊆ S ∧ (colorGraph c k).IsClique (B a : Set V) ∧ (B a).card < r) ∧
      (∀ a, B a = S.filter (fun x => I.filter (fun y => x=y ∨ (colorGraph c k).Adj x y)={a.val})) ∧
      X=S \ univ.biUnion B ∧ (∀ x∈X, (I.filter ((colorGraph c k).Adj x)).card=2) ∧
      (∑ a, (r-(B a).card))+1=X.card ∧ X.card≤3*s+1 ∧
      ∃ a, r-2≤(B a).card := by
  classical
  obtain ⟨C,hC,hi,hcost,htwo⟩ := odd_endpoint_cheap_anchor hs hr hb hkj hk h P Q hp hpu hpd hpc hq hqd hqc
  let I := C∩S
  let G := colorGraph c k
  obtain ⟨B,X,hdis,hrow,xeq,xsize,eqB⟩ :=
    h.private_blocks_with_hits (show I⊆S from inter_subset_right) hi hcost
  have isz : Fintype.card I=s+1 := (Fintype.card_coe I).trans hi.card_eq
  have cap (a : I) : (B a).card < r := by
    by_contra! large
    obtain ⟨D,hD,szD⟩ := exists_subset_card_eq large
    exact h.no_clique hb (by omega) D (hD.trans (hrow a).1) ⟨(hrow a).2.subset hD,szD⟩
  let N (x : V) := I.filter (fun y => x=y ∨ G.Adj x y)
  have Nself (x : V) (hx : x ∈ I) : N x={x} := by
    ext y
    simp only [N,mem_filter,mem_singleton]
    constructor
    · rintro ⟨hy,h | h⟩
      · exact h.symm
      · exact (hi.isIndepSet hx hy h.ne h).elim
    · rintro rfl
      exact ⟨hx, Or.inl rfl⟩
  have single (x y : V) (hx : x ∈ S) (he : N x={y}) : x∈univ.biUnion B := by
    have hy : y∈I := (mem_filter.mp (show y∈N x from he ▸ mem_singleton_self _)).1
    have hb' := eqB (⟨y,hy⟩ : I)
    exact mem_biUnion.mpr ⟨⟨y,hy⟩,mem_univ _,hb' ▸ mem_filter.mpr ⟨hx,he⟩⟩
  have double (x : V) (hx : x ∈ X) : (I.filter (G.Adj x)).card=2 := by
    obtain ⟨hxS,hxout⟩ := mem_sdiff.mp (xeq ▸ hx : x∈S \ univ.biUnion B)
    have hxI : x∉I := fun hm => hxout (single x x hxS (Nself x hm))
    have upper := htwo x (mem_sdiff.mpr ⟨hxS,hxI⟩)
    have ne : N x = I.filter (G.Adj x) := by
      ext y
      by_cases h : y∈I
      · simp [N,h,show x≠y from fun eq => hxI (eq ▸ h)]
      · simp [N,h]
    by_contra fail
    have max1 : (N x).card≤1 := by rw [ne]; change (I.filter (G.Adj x)).card≤2 at upper; omega
    rcases Nat.eq_zero_or_pos (N x).card with hz | hz
    · have ind := independent_insert_of_nonadjacent G hi.isIndepSet x (by
        intro y hy he
        have pos : 0<(N x).card := card_pos.mpr ⟨y, mem_filter.mpr ⟨hy,Or.inr he⟩⟩
        omega)
      exact h.free (insert x I) (insert_subset hxS inter_subset_right)
        ⟨ind,by rw [card_insert_of_notMem hxI,hi.card_eq]⟩
    · obtain ⟨y,hy⟩ := card_eq_one.mp (show (N x).card=1 by omega)
      exact hxout (single x y hxS hy)
  have unionSize := card_biUnion (s:=univ) (t:=B) (fun a _ b _ hne => hdis hne)
  have total := card_sdiff_add_card_eq_card
    (show univ.biUnion B ⊆ S from biUnion_subset.mpr fun i _ => (hrow i).1)
  rw [←xeq,unionSize,h.card_eq] at total
  have cancel := sum_congr (s₁:=univ) (g:=fun _ => r) rfl (fun i _ => Nat.sub_add_cancel (cap i).le)
  rw [sum_add_distrib,sum_const,card_univ,isz,nsmul_eq_mul] at cancel
  simp only [Nat.cast_id] at cancel
  have δ : (∑ i,(r-(B i).card))+1=X.card := by omega
  refine ⟨C,hC,B,X,hi,hdis,fun i => ⟨(hrow i).1,(hrow i).2,cap i⟩,eqB,xeq,double,δ,by omega,?_⟩
  by_contra! small
  have all := sum_le_sum (s:=univ) (f:=fun _ => 3) (g:= fun i => r-(B i).card)
    (fun i _ => by have := small i; omega)
  simp only [sum_const,card_univ,isz,nsmul_eq_mul,Nat.cast_id] at all
  omega

/-- Unless there is a smaller obstruction, the core of a sparse color
contains a clique of size r−2, in addition to its s full outside cliques. -/
theorem odd_endpoint_near_full_clique (hs : 1 ≤ s) (hr : r=2*s+1)
    (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c)
    (hsmall : ∀ (k : Fin r) (a : ℕ), a ≤ s → ∀ W : Finset V, ¬MinimalObstruction c k a W) :
    ∃ (k : Fin r) (S D : Finset V), MinimalObstruction c k (s+1) S ∧ D⊆S ∧
      (colorGraph c k).IsNClique (r-2) D := by
  classical
  obtain ⟨k,j,hkj,hk,hj⟩ := odd_endpoint_two_sparse hs hr hn c hb hsmall
  obtain ⟨S,P,h,hp,hpu,hpd,hpc⟩ := odd_endpoint_of_sparse_color hs hr hn c hb k hk (hsmall k)
  obtain ⟨_,Q,_,hq,_,hqd,hqc⟩ := odd_endpoint_of_sparse_color hs hr hn c hb j hj (hsmall j)
  obtain ⟨_,_,B,_,_,_,rows,_,_,_,_,_,i,large⟩ :=
    odd_endpoint_private_rows hs hr hb hkj hk h P Q hp hpu hpd hpc hq hqd hqc
  obtain ⟨D,hD,sz⟩ := exists_subset_card_eq large
  exact ⟨k,S,D,h,hD.trans (rows i).1,⟨(rows i).2.1.subset hD,sz⟩⟩

end Erdos617
