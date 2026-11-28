module

public import Erdos617.OddIntersection

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- Keep precisely the edges internal to one of the given parts. -/
def withinParts (G : SimpleGraph V) (P : Finset (Finset V)) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ∃ B ∈ P, x ∈ B ∧ y ∈ B
  symm.symm _ _ h := ⟨h.1.symm, by obtain ⟨B,hB,hx,hy⟩ := h.2; exact ⟨B,hB,hy,hx⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

private theorem part_eq_of_common {P : Finset (Finset V)}
    (hd : (↑P : Set (Finset V)).PairwiseDisjoint id) {A B : Finset V}
    (ha : A ∈ P) (hb : B ∈ P) {x : V} (hx : x ∈ A) (hy : x ∈ B) : A=B := by
  by_contra ne
  exact disjoint_left.mp (hd ha hb ne) hx hy

/-- Restricting the union of disjoint graphs to any set adds the independence
numbers of its restrictions to the parts. -/
theorem rankOn_withinParts (G : SimpleGraph V) (P : Finset (Finset V))
    (hd : (↑P : Set (Finset V)).PairwiseDisjoint id) (U : Finset V) (hu : U ⊆ P.biUnion id) :
    rankOn (withinParts G P) U = ∑ B ∈ P, rankOn G (U∩B) := by
  classical
  apply le_antisymm
  · obtain ⟨I,hi,hind,hn⟩ := exists_max_indep (withinParts G P) U
    have dis : (↑P : Set (Finset V)).PairwiseDisjoint (fun B => I ∩ B) :=
      fun _ ha _ hb ne => (hd ha hb ne).mono inter_subset_right inter_subset_right
    have all : P.biUnion (fun B => I∩B)=I := by
      change P.biUnion (fun B => I ∩ id B) = I
      rw [← inter_biUnion, inter_eq_left.mpr (hi.trans hu)]
    have size := card_biUnion dis
    rw [all,hn] at size
    rw [size]
    refine sum_le_sum (fun B hB => card_le_rankOn _ (inter_subset_inter hi (Subset.rfl : B ⊆ B)) ?_)
    intro x hx y hy ne he
    exact hind (mem_inter.mp hx).1 (mem_inter.mp hy).1 ne
      ⟨he,B,hB,(mem_inter.mp hx).2,(mem_inter.mp hy).2⟩
  · choose I hI hind hr using fun B : Finset V => exists_max_indep G (U ∩ B)
    have sub (B : Finset V) : I B ⊆ B := (hI B).trans inter_subset_right
    have dis : (↑P : Set (Finset V)).PairwiseDisjoint I :=
      fun A ha B hb ne => (hd ha hb ne).mono (sub A) (sub B)
    have count := card_biUnion dis
    simp only [sum_congr rfl (fun B _ => hr B)] at count
    rw [←count]
    apply card_le_rankOn _ (biUnion_subset.mpr fun B _ => (hI B).trans inter_subset_left)
    intro x hx y hy ne he
    obtain ⟨A,hA,hx⟩ := mem_biUnion.mp hx
    obtain ⟨B,hB,hy⟩ := mem_biUnion.mp hy
    obtain ⟨edge,C,hC,hxC,hyC⟩ := he
    obtain rfl := part_eq_of_common hd hA hC (sub A hx) hxC
    obtain rfl := part_eq_of_common hd hB hA (sub B hy) hyC
    exact hind B hx hy ne edge

variable [Fintype V] {r : ℕ}

/-- Different selected colors can be thinned simultaneously, placing the
discarded edges into a chosen color. Balance survives if each retained graph
still has independence number at most r. -/
theorem balanced_thin_colors (c : Sym2 V → Fin r) (hb : Balanced c) (T : Finset (Fin r))
    (q : Fin r) (H : T → SimpleGraph V)
    (hsub : ∀ k, H k ≤ colorGraph c k.val)
    (hcap : ∀ k, rankOn (H k) univ ≤ r) :
    ∃ d : Sym2 V → Fin r, Balanced d ∧ (∀ k : T, k.val ≠ q → colorGraph d k.val = H k) ∧
      (∀ j ∉ T, j ≠ q → colorGraph d j = colorGraph c j) ∧ colorGraph c q ≤ colorGraph d q := by
  classical
  let d (e : Sym2 V) := if h : c e ∈ T then if e∈(H ⟨c e,h⟩).edgeSet then c e else q else c e
  have selected (k : T) (hk : k.val≠q) : colorGraph d k.val=H k := by
    ext x y
    by_cases eq : c s(x,y)=k.val
    · simp only [colorGraph_adj,d,mem_edgeSet,eq]
      by_cases hxy : (H k).Adj x y
      · simp [hxy,hxy.ne]
      · simp [hxy,hk.symm]
    · have no : ¬ (H k).Adj x y := fun hxy => eq ((hsub k hxy).2)
      simp only [colorGraph_adj,d,no,iff_false]
      split <;> (try split) <;> simp_all [Ne.symm hk]
  have other (j : Fin r) (hj : j ∉ T) (hjq : j ≠ q) : colorGraph d j = colorGraph c j := by
    ext x y
    by_cases he : c s(x,y) ∈ T
    · have ne : c s(x,y) ≠ j := fun eq => hj (eq ▸ he)
      simp only [colorGraph_adj,d,dite_eq_left he]; split <;> simp [ne,hjq.symm]
    · simp [colorGraph_adj,d,he]
  have kept : colorGraph c q ≤ colorGraph d q := by
    intro x y he
    refine ⟨he.1,?_⟩
    have eq := he.2
    simp [d,eq]
  refine ⟨d,?_,selected,other,kept⟩
  intro S hn k
  by_cases hkq : k=q
  · subst k
    obtain ⟨x,hx,y,hy,hxy,he⟩ := hb S hn q
    exact ⟨x,hx,y,hy,hxy,(kept (show (colorGraph c q).Adj x y from ⟨hxy,he⟩)).2⟩
  by_cases hk : k∈T
  · by_contra! none
    have ind : (H ⟨k,hk⟩).IsIndepSet (S : Set V) := by
      rw [←selected ⟨k,hk⟩ hkq]
      intro x hx y hy hxy he
      exact none x hx y hy hxy he.2
    have := (card_le_rankOn _ (subset_univ S) ind).trans (hcap ⟨k,hk⟩)
    omega
  · obtain ⟨x,hx,y,hy,hxy,he⟩ := hb S hn k
    have old : (colorGraph c k).Adj x y := ⟨hxy,he⟩
    rw [←other k hk hkq] at old
    exact ⟨x,hx,y,hy,hxy,old.2⟩

/-- The rank formula for a core and a family of cliques after the crossing
edges are removed. Only the number of nonempty clique intersections matters. -/
theorem rankOn_cliques_and_core (G : SimpleGraph V) (A : Finset V) (ha : A.Nonempty)
    (P : Finset (Finset V)) (hu : P.biUnion id=univ \ A)
    (hd : (↑P : Set (Finset V)).PairwiseDisjoint id) (hc : ∀ B∈P, G.IsClique (B : Set V))
    (U : Finset V) :
    rankOn (withinParts G (insert A P)) U =
      rankOn G (U∩A) + (P.filter fun B => (U∩B).Nonempty).card := by
  classical
  have disA (B : Finset V) (hB : B∈P) : Disjoint A B :=
    disjoint_sdiff.mono_right (biUnion_subset.mp hu.le B hB)
  have hA : A ∉ P := fun h => ha.ne_empty (disjoint_self.mp (disA A h))
  have dis : (↑(insert A P) : Set (Finset V)).PairwiseDisjoint id := by
    rw [coe_insert]
    exact hd.insert fun B hB _ => disA B hB
  have cover : U ⊆ (insert A P).biUnion id := by
    rw [biUnion_insert,show id A=A from rfl,hu,union_sdiff_self_eq_union]
    exact (subset_univ U).trans subset_union_right
  have unit (B : Finset V) (hB : B∈P) :
      rankOn G (U∩B) = if (U∩B).Nonempty then 1 else 0 := by
    split
    · exact le_antisymm (rank_clique_le_one G ((hc B hB).subset inter_subset_right)) (rankOn_pos G ‹_›)
    · have empty : U∩B=∅ := not_nonempty_iff_eq_empty.mp ‹_›
      rw [empty,rankOn_empty]
  rw [rankOn_withinParts G _ dis U cover,sum_insert hA,sum_congr rfl unit,sum_boole]
  rfl

omit [Fintype V] in
/-- Any full clique of a third color meets the intersection of two endpoint
cores. Each of the two individual intersections contains a strict majority
of the clique. -/
private theorem core_pair_meets_row {A B C : Finset V} {s : ℕ}
    (hc : C.card=2*s+1) (ha : (C∩A).card=s+1) (hb : (C∩B).card=s+1) :
    ((A∩B)∩C).Nonempty := by
  by_contra he
  have dis : Disjoint (C∩A) (C∩B) := disjoint_left.mpr (fun x hx hy =>
    he ⟨x,mem_inter.mpr ⟨mem_inter.mpr ⟨(mem_inter.mp hx).2,(mem_inter.mp hy).2⟩,(mem_inter.mp hx).1⟩⟩)
  have le := card_le_card (union_subset (inter_subset_left : C∩A ⊆ C) (inter_subset_left : C∩B ⊆ C))
  rw [card_union_of_disjoint dis,ha,hb,hc] at le
  omega

/-- On the intersection of two odd-endpoint cores, every other normalized
sparse color has its s isolated clique contributions and at least two more
independent vertices in the common core. -/
theorem odd_endpoint_normalization {s : ℕ} (hs : 1 ≤ s) (hr : r=2*s+1)
    (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c) (q : Fin r)
    (hsmall : ∀ (k : Fin r) (a : ℕ), a ≤ s → ∀ W : Finset V, ¬MinimalObstruction c k a W) :
    let T := univ.filter fun i => 2*(colorGraph c i).edgeFinset.card ≤ r*(r^2+1)
    ∃ (d : Sym2 V → Fin r) (A : T → Finset V) (P : T → Finset (Finset V)),
      Balanced d ∧ 3 ≤ T.card ∧
      (∀ i, MinimalObstruction c i.val (s+1) (A i) ∧ (P i).card=s ∧
        (P i).biUnion id=univ \ A i ∧ (↑(P i) : Set (Finset V)).PairwiseDisjoint id ∧
        ∀ C∈P i,(colorGraph c i.val).IsNClique r C) ∧
      (∀ i : T, i.val ≠ q → ∀ U, rankOn (colorGraph d i.val) U =
        rankOn (colorGraph c i.val) (U∩A i) + ((P i).filter fun B => (U∩B).Nonempty).card) ∧
      ∀ i j : T, i ≠ j → i.val ≠ q → j.val ≠ q →
        let U := A i∩A j
        U.card=(s+1)^2+1 ∧
        rankOn (colorGraph d i.val) U ≤ s+1 ∧ rankOn (colorGraph d j.val) U ≤ s+1 ∧
        ∀ l : T, l ≠ i → l ≠ j → l.val ≠ q →
          rankOn (colorGraph d l.val) U=s+rankOn (colorGraph c l.val) (U∩A l) ∧
          s+2 ≤ rankOn (colorGraph d l.val) U := by
  classical
  intro T
  obtain ⟨many,A,P,grid,pairs⟩ := odd_endpoint_grids hs hr hn c hb hsmall
  let G (i : T) := colorGraph c i.val
  let H (i : T) := withinParts (G i) (insert (A i) (P i))
  have row (i : T) (C : Finset V) (hC : C∈P i) : (G i).IsNClique r C :=
    ((grid i).2.2.2.2.1 C).mpr hC
  have whole (i : T) (U : Finset V) : rankOn (H i) U =
      rankOn (G i) (U∩A i) + ((P i).filter fun B => (U∩B).Nonempty).card := by
    apply rankOn_cliques_and_core
    · exact card_pos.mp (by rw [(grid i).1.card_eq]; omega)
    · exact (grid i).2.2.1
    · exact (grid i).2.2.2.1
    · exact fun B hB => (row i B hB).isClique
  have caps (i : T) : rankOn (H i) univ ≤ r := by
    rw [whole,univ_inter,(grid i).1.rank_eq (by omega)]
    have le := (card_filter_le (s:=P i) (p:=fun C => (univ∩C).Nonempty)).trans_eq (grid i).2.1
    omega
  obtain ⟨d,bd,defn,_⟩ := balanced_thin_colors c hb T q H (fun _ _ _ he => he.1) caps
  have exactRank (i : T) (hi : i.val≠q) (U : Finset V) := (defn i hi) ▸ whole i U
  refine ⟨d,A,P,bd,many,fun i => ⟨(grid i).1,(grid i).2.1,(grid i).2.2.1,(grid i).2.2.2.1,row i⟩, exactRank,?_⟩
  intro i j hij hi hj U
  have inside (k : T) (hk : k.val≠q) (hU : U ⊆ A k) : rankOn (colorGraph d k.val) U ≤ s+1 := by
    have empty : (P k).filter (fun B => (U∩B).Nonempty) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro C hC
      obtain ⟨hC,x,hx⟩ := mem_filter.mp hC
      exact (mem_sdiff.mp (biUnion_subset.mp (grid k).2.2.1.le C hC (mem_inter.mp hx).2)).2
        (hU (mem_inter.mp hx).1)
    rw [exactRank k hk U,inter_eq_left.mpr hU,empty,card_empty,Nat.add_zero]
    exact (rankOn_mono _ hU).trans_eq ((grid k).1.rank_eq (by omega))
  refine ⟨(pairs i j hij).2.1,inside i hi inter_subset_left,inside j hj inter_subset_right,?_⟩
  intro l hli hlj hlq
  have hit (k : T) (hlk : l≠k) (C : Finset V) (hC : C∈P l) : (C∩A k).card=s+1 :=
    (full_clique_intersections (fun eq => hlk (Subtype.ext eq)) hr (grid k).1 (grid k).2.1 (grid k).2.2.1
      ⟨(grid k).2.2.2.1,row k⟩ (row l C hC)).1
  have filterAll : (P l).filter (fun B => (U∩B).Nonempty)=P l := by
    apply filter_eq_self.mpr
    intro C hC
    exact core_pair_meets_row ((row l C hC).card_eq.trans hr) (hit i hli C hC) (hit j hlj C hC)
  have formula : rankOn (colorGraph d l.val) U = s+rankOn (G l) (U∩A l) := by
    rw [exactRank l hlq U,filterAll,(grid l).2.1,Nat.add_comm]
  have slices := sum_le_sum (s:=P l) (g:=fun _ => s+1) (fun C hC =>
    calc
      (U∩C).card ≤ (A i∩C).card := card_le_card (inter_subset_inter inter_subset_left (Subset.rfl : C⊆C))
      _ = s+1 := (congrArg card (inter_comm _ _)).trans (hit i hli C hC))
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,(grid l).2.1] at slices
  have split := card_inter_complement_sum (A l) U (P l) (grid l).2.2.1 (grid l).2.2.2.1
  change (∑ C ∈ P l,(U∩C).card)+(U∩A l).card=(A i∩A j).card at split
  rw [(pairs i j hij).2.1] at split
  have size : s+1 < (U∩A l).card := by nlinarith only [slices,split]
  have two : 2 ≤ rankOn (G l) (U∩A l) := by
    by_contra! small
    have hn' : (U∩A l).Nonempty := card_pos.mp (by omega)
    have pos := rankOn_pos (G l) hn'
    have clique := rank_one_clique (G l) (show rankOn (G l) (U∩A l)=1 by omega)
    have ind : (G i).IsIndepSet (↑(U∩A l) : Set V) := by
      intro x hx y hy hxy he
      exact hli (Subtype.ext ((clique hx hy hxy).2.symm.trans he.2))
    have cap := card_le_rankOn (G i) (inter_subset_left.trans (inter_subset_left : U ⊆ A i)) ind
    rw [(grid i).1.rank_eq (by omega)] at cap
    exact size.not_ge cap
  exact ⟨formula,formula ▸ Nat.add_le_add_left two s⟩

end Erdos617
