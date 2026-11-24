import Erdos617.StrictHalfRange

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem rank_clique_le_one (G : SimpleGraph V) {C : Finset V}
    (hC : G.IsClique (C : Set V)) : rankOn G C ≤ 1 := by
  obtain ⟨I,hI,hi,hr⟩ := exists_max_indep G C
  by_contra! hn
  obtain ⟨x,hx,y,hy,hn⟩ := one_lt_card.mp (hr ▸ hn)
  exact hi hx hy hn (hC (hI hx) (hI hy) hn)

/-- In a balanced coloring, a full clique and the remaining vertices form
an additive rank partition whenever the enclosing set has rank less than r. -/
theorem RankInseparable.no_full_clique {r : ℕ} {c : Sym2 V → Fin r} {k : Fin r}
    {A : Finset V} (h : RankInseparable (colorGraph c k) A) (hb : Balanced c)
    (ha : 1 < rankOn (colorGraph c k) A) (hlt : rankOn (colorGraph c k) A < r)
    {C : Finset V} (hCA : C ⊆ A) : ¬ (colorGraph c k).IsNClique r C := by
  intro hc
  let G := colorGraph c k
  change 1 < rankOn G A at ha
  have hcone := rank_clique_le_one G hc.isClique
  have rest : (A \ C).Nonempty := by
    by_contra! hn
    have eq : C=A := by simpa [hn] using union_sdiff_of_subset hCA
    subst C
    omega
  obtain ⟨I,hI,hi,hcard⟩ := exists_max_indep G (A \ C)
  have hlow := rankOn_mono G (sdiff_subset : A \ C ⊆ A)
  obtain ⟨J,hJ,hind⟩ := extend_across_clique_within G C I hc ⟨hi,hcard⟩
    (disjoint_sdiff.mono_right hI) (hlow.trans_lt hlt)
    (fun x hx _ hy _ hz => exterior_clique_neighbor_unique c hb k C hc x hx hy hz)
  have hbig := card_le_rankOn G (hJ.trans (union_subset hCA (hI.trans sdiff_subset))) hind.isIndepSet
  have hs := h.lt_of_partition (card_pos.mp (hc.card_eq ▸ (by omega : 0<r))) rest
    disjoint_sdiff (union_sdiff_of_subset hCA)
  rw [hind.card_eq] at hbig
  change rankOn G A < rankOn G C + rankOn G (A \ C) at hs
  omega

variable [Fintype V]

private structure Cover (G : SimpleGraph V) where
  parts : Finset (Finset V)
  cover : parts.biUnion id = univ
  disj : (↑parts : Set (Finset V)).PairwiseDisjoint id
  atom : ∀ A ∈ parts, RankInseparable G A
  ranks : (∑ A ∈ parts, rankOn G A) = rankOn G univ

private theorem cover_exists (G : SimpleGraph V) : Nonempty (Cover G) := by
  obtain ⟨P,hu,hd,hi,hs⟩ := exists_rank_partition G univ
  exact ⟨⟨P,hu,hd,hi,hs⟩⟩

private theorem Cover.card_sum {G : SimpleGraph V} (P : Cover G) :
    (∑ A ∈ P.parts,A.card) = Fintype.card V := by
  simpa [P.cover] using (card_biUnion P.disj).symm

private theorem Cover.inter_sum {G : SimpleGraph V} (P : Cover G) (A : Finset V) :
    (∑ B ∈ P.parts,(A ∩ B).card) = A.card := by
  have hd : (↑P.parts : Set (Finset V)).PairwiseDisjoint (fun B => A ∩ B) :=
    fun _ hB _ hC hne => (P.disj hB hC hne).mono inter_subset_right inter_subset_right
  rw [← card_biUnion hd]
  change (P.parts.biUnion (fun B => A ∩ id B)).card = A.card
  rw [← inter_biUnion A P.parts id, P.cover,inter_univ]

private theorem Cover.part_cap {G : SimpleGraph V} (P : Cover G) {A : Finset V} (hA : A ∈ P.parts) :
    rankOn G A + P.parts.card ≤ rankOn G univ+1 := by
  have hl := sum_le_sum (s := P.parts.erase A) (f := fun _ => 1) fun B hB =>
    (P.atom B (mem_of_mem_erase hB)).rank_pos
  simp only [sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_one,card_erase_of_mem hA] at hl
  have hs := sum_erase_add P.parts (rankOn G) hA
  rw [P.ranks] at hs
  omega

omit [DecidableEq V] in
private theorem balanced_global_rank {r : ℕ} (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r) :
    rankOn (colorGraph c k) univ ≤ r := by
  by_contra! hbig
  obtain ⟨I,_,hi,hcard⟩ := exists_max_indep (colorGraph c k) univ
  obtain ⟨J,hJI,hJ⟩ := exists_subset_card_eq (s := I) (show r+1 ≤ I.card by omega)
  obtain ⟨x,hx,y,hy,hn,he⟩ := hb J hJ k
  exact hi (hJI hx) (hJI hy) hn ⟨hn,he⟩

private theorem density_summed {r : ℕ} (hr : 3 ≤ r) (hn : Fintype.card V = r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r) (P : Cover (colorGraph c k)) :
    r*(r^2+1) ≤ (colorGraph c k).edgeFinset.card + (r.choose 2+1)*r + (r-1)*P.parts.card ∧
    (2 ≤ P.parts.card → r*(r^2+1) <
      (colorGraph c k).edgeFinset.card + (r.choose 2+1)*r + (r-1)*P.parts.card) := by
  let G := colorGraph c k
  change Cover G at P
  have halpha := balanced_global_rank c hb k
  have hweak := rank_partition_density G P.parts P.disj P.atom r
  rw [P.cover, card_univ,hn,blockEdges_univ,P.ranks] at hweak
  have hprod := Nat.mul_le_mul_left (r.choose 2+1) halpha
  change rankOn G univ ≤ r at halpha
  change (r.choose 2+1)*rankOn G univ ≤ _ at hprod
  change r*(r^2+1) ≤ G.edgeFinset.card+(r.choose 2+1)*r+(r-1)*P.parts.card ∧ _
  constructor
  · omega
  change 2 ≤ P.parts.card → r*(r^2+1) < G.edgeFinset.card+(r.choose 2+1)*r+(r-1)*P.parts.card
  intro hparts
  have hsum := P.card_sum
  rw [hn] at hsum
  obtain ⟨A,hA,ha⟩ : ∃ A ∈ P.parts, r*rankOn G A < A.card := by
    by_contra! hu
    have hs := sum_le_sum hu
    rw [← mul_sum,P.ranks,hsum] at hs
    have := Nat.mul_le_mul_left r halpha
    rw [pow_two] at hs
    omega
  have hlarge : 1 < rankOn G A := by
    have hp := (P.atom A hA).rank_pos
    by_contra! hh
    have hone : rankOn G A = 1 := by omega
    have hc := rank_one_clique G hone
    rw [hone,Nat.mul_one] at ha
    obtain ⟨B,hB,hcard⟩ := exists_subset_card_eq (s := A) (Nat.succ_le_of_lt ha)
    obtain ⟨j,hjk⟩ : ∃ j : Fin r, j ≠ k := by
      have he : (univ.erase k).Nonempty := card_pos.mp (by simp; omega)
      exact he.imp fun _ hj => (mem_erase.mp hj).1
    obtain ⟨x,hx,y,hy,hxy,he⟩ := hb B hcard j
    exact hjk (he.symm.trans (hc (hB hx) (hB hy) hxy).2)
  have strict : r*A.card < blockEdges G A + (r.choose 2+1)*rankOn G A + (r-1) := by
    refine lt_of_le_of_ne (rank_density G _ (P.atom _ hA) r) ?_
    intro eq
    have hcap := rank_density_order_cap G _ (P.atom _ hA) (by omega : 1≤r) eq
    obtain ⟨C,hC,hcl⟩ := exists_clique_of_rank_density_eq G A (P.atom _ hA) r hr (by omega) eq
    have haCap := P.part_cap hA
    exact (P.atom _ hA).no_full_clique hb hlarge (by change rankOn G A < r; omega) hC hcl
  have hs := sum_lt_sum (f := fun B : Finset V => r*B.card)
    (g := fun B => blockEdges G B+(r.choose 2+1)*rankOn G B+(r-1))
    (fun B hB => rank_density G _ (P.atom _ hB) r) ⟨A,hA,strict⟩
  simp only [sum_add_distrib, ← mul_sum, hsum, P.ranks, sum_const, nsmul_eq_mul, Nat.cast_id] at hs
  have he := boundary_edge_count G univ P.parts P.cover.le P.disj
  rw [blockEdges_univ] at he
  rw [Nat.mul_comm P.parts.card] at hs
  omega

private theorem two_color_budget {r : ℕ} (hr : 3 ≤ r) (hn : Fintype.card V=r^2+1)
    (c : Sym2 V → Fin r) : ∃ i j : Fin r, i ≠ j ∧
      (colorGraph c i).edgeFinset.card+(colorGraph c j).edgeFinset.card ≤ r*(r^2+1) := by
  let E (k : Fin r) := (colorGraph c k).edgeFinset.card
  have hU : (univ : Finset (Fin r)).Nonempty := ⟨⟨0, by omega⟩,mem_univ _⟩
  obtain ⟨i,_,hm⟩ := univ.exists_min_image E hU
  have hF : (univ.erase i).Nonempty := card_pos.mp (by simp; omega)
  obtain ⟨j,hj,hjmin⟩ := (univ.erase i).exists_min_image E hF
  have hs := sum_le_sum hjmin
  simp only [sum_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_id] at hs
  have hsum := sum_color_edges c
  change ∑ j, E j = (Fintype.card V).choose 2 at hsum
  rw [←sum_erase_add _ _ (mem_univ i),hn] at hsum
  have hle := hm j (mem_univ _)
  have hp := Nat.mul_le_mul_left (r-2) hle
  have hi : (r-2)*E i+2*E i=r*E i := by rw [← Nat.add_mul]; congr 1; omega
  have hj' : (r-2)*E j+E j=(r-1)*E j := by rw [← Nat.succ_mul]; congr 1; omega
  refine ⟨i,j,(mem_erase.mp hj).1.symm,?_⟩
  change E i+E j ≤ r*(r^2+1)
  have hjr : (r-1)*E j+E j=r*E j := by rw [← Nat.succ_mul]; congr 1; omega
  refine Nat.le_of_mul_le_mul_left ?_ (by omega : 0 < r)
  nlinarith only [hs,hsum,hp,hi,hj',hjr,twice_choose_two (r^2+1)]

private theorem parts_numeric (r e f p q : ℕ) (hr : 3 ≤ r)
    (he : e+f ≤ r*(r^2+1))
    (hi : r*(r^2+1) ≤ e+(r.choose 2+1)*r+(r-1)*p)
    (hj : r*(r^2+1) ≤ f+(r.choose 2+1)*r+(r-1)*q)
    (hsi : 2 ≤ p → r*(r^2+1) < e+(r.choose 2+1)*r+(r-1)*p)
    (hsj : 2 ≤ q → r*(r^2+1) < f+(r.choose 2+1)*r+(r-1)*q) :
    r < p+q := by
  have hc := congrArg (fun n => r*n) (twice_choose_two r)
  have hm := congrArg (fun n => n*r) (show r-1+1=r by omega)
  have hp : (r-1)*r ≤ (r-1)*(p+q) := by nlinarith only [he,hi,hj,hc,hm]
  have hrest := Nat.le_of_mul_le_mul_left hp (by omega : 0<r-1)
  have strict : (r-1)*r < (r-1)*(p+q) := by
    rcases le_or_gt 2 p with h | h
    · nlinarith only [he,hsi h,hj,hc,hm]
    · nlinarith only [he,hi,hsj (by omega),hc,hm]
  exact Nat.lt_of_mul_lt_mul_left strict

omit [Fintype V] in
private theorem other_rank_on_clique {r : ℕ} (c : Sym2 V → Fin r) {i j : Fin r}
    (hij : i ≠ j) {A B : Finset V} (hrank : rankOn (colorGraph c i) A = 1) :
    (A ∩ B).card ≤ rankOn (colorGraph c j) B := by
  apply card_le_rankOn _ inter_subset_right
  intro x hx y hy hxy he
  have hc := rank_one_clique (colorGraph c i) hrank
  exact hij ((hc (mem_inter.mp hx).1 (mem_inter.mp hy).1 hxy).2.symm.trans he.2)

/-- A hypothetical balanced coloring has a set of ab+1 vertices with independence
number at most a in one color and at most b in another, where a+b ≤ r+1. -/
theorem exists_two_color_rank_intersection {r : ℕ} (hr : 3 ≤ r)
    (hn : Fintype.card V = r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c) :
    ∃ i j : Fin r, i ≠ j ∧ ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ a+b ≤ r+1 ∧
      ∃ W : Finset V, W.card=a*b+1 ∧ rankOn (colorGraph c i) W ≤ a ∧
        rankOn (colorGraph c j) W ≤ b := by
  classical
  obtain ⟨i,j,hij,he⟩ := two_color_budget hr hn c
  let G := colorGraph c i
  let H := colorGraph c j
  obtain ⟨P⟩ := cover_exists G
  obtain ⟨Q⟩ := cover_exists H
  obtain ⟨hp,hsp⟩ := density_summed hr hn c hb i P
  obtain ⟨hq,hsq⟩ := density_summed hr hn c hb j Q
  have hparts := parts_numeric r _ _ _ _ hr he hp hq hsp hsq
  have ha : rankOn G univ ≤ r := balanced_global_rank c hb i
  have hb' : rankOn H univ ≤ r := balanced_global_rank c hb j
  obtain ⟨A,hA,B,hB,hover⟩ :
      ∃ A ∈ P.parts, ∃ B ∈ Q.parts, rankOn G A*rankOn H B < (A ∩ B).card := by
    by_contra! hlow
    have per (A : Finset V) (hA : A ∈ P.parts) : A.card ≤ rankOn G A * rankOn H univ := by
      have hs := sum_le_sum (hlow A hA)
      rwa [Q.inter_sum A,← mul_sum,Q.ranks] at hs
    have hs := sum_le_sum per
    rw [P.card_sum,← sum_mul,P.ranks,hn] at hs
    have hh := Nat.mul_le_mul ha hb'
    rw [pow_two] at hs
    omega
  have hr2 {a b : ℕ} (hap : 0<a) (hnab : a*b < (A ∩ B).card)
      (hu : a=1 → (A ∩ B).card ≤ b) : 2 ≤ a := by
    by_contra! hlt
    have he : a=1 := by omega
    rw [he,Nat.one_mul] at hnab
    exact hnab.not_ge (hu he)
  have ia := hr2 (P.atom A hA).rank_pos hover (other_rank_on_clique c hij)
  have ib := hr2 (Q.atom B hB).rank_pos (Nat.mul_comm .. ▸ hover)
    (fun he => by simpa [inter_comm] using other_rank_on_clique (B:=A) c hij.symm he)
  have hpA := P.part_cap hA
  have hqB := Q.part_cap hB
  obtain ⟨W,hW,hcard⟩ := exists_subset_card_eq (s := A ∩ B) (Nat.succ_le_of_lt hover)
  exact ⟨i,j,hij,_,_,ia,ib,by omega,W,hcard,
    rankOn_mono G (hW.trans inter_subset_left),rankOn_mono H (hW.trans inter_subset_right)⟩

section Product

variable {U : Type*} [DecidableEq U]

/-- Minimality of a vertex set whose order exceeds the product of two independence numbers. -/
structure RankProductObstruction (G H : SimpleGraph U) (S : Finset U) : Prop where
  large : rankOn G S * rankOn H S < S.card
  smaller : ∀ A ⊂ S, A.card ≤ rankOn G A * rankOn H A

variable {G H : SimpleGraph U} {S : Finset U}

omit [DecidableEq U] in
theorem RankProductObstruction.symm (h : RankProductObstruction G H S) :
    RankProductObstruction H G S :=
  ⟨Nat.mul_comm .. ▸ h.large, fun A hA => Nat.mul_comm .. ▸ h.smaller A hA⟩

theorem RankProductObstruction.card_eq (h : RankProductObstruction G H S) :
    S.card = rankOn G S*rankOn H S+1 := by
  obtain ⟨v,hv⟩ := card_pos.mp (show 0 < S.card by have := h.large; omega)
  have upper := (h.smaller _ (erase_ssubset hv)).trans
    (Nat.mul_le_mul (rankOn_mono G (erase_subset v S)) (rankOn_mono H (erase_subset v S)))
  have := h.large
  have := card_erase_add_one hv
  omega

/-- A minimally oversized intersection is rank-inseparable in each of its two graphs. -/
theorem RankProductObstruction.inseparable (h : RankProductObstruction G H S) :
    RankInseparable G S := by
  refine ⟨card_pos.mp (by have := h.large; omega),?_⟩
  intro A B hA hB hd cover
  have ha : A ⊂ S := by
    rw [←cover]
    refine Finset.ssubset_iff_subset_ne.mpr ⟨subset_union_left,?_⟩
    obtain ⟨x,hx⟩ := hB
    exact fun eq => disjoint_left.mp hd (eq ▸ mem_union_right A hx) hx
  have hb : B ⊂ S := by
    rw [←cover]
    refine Finset.ssubset_iff_subset_ne.mpr ⟨subset_union_right,?_⟩
    obtain ⟨x,hx⟩ := hA
    exact fun eq => disjoint_left.mp hd hx (eq ▸ mem_union_left B hx)
  have ha' := (h.smaller _ ha).trans (Nat.mul_le_mul_left (rankOn G A) (rankOn_mono H ha.le))
  have hb' := (h.smaller _ hb).trans (Nat.mul_le_mul_left (rankOn G B) (rankOn_mono H hb.le))
  have total := Nat.add_le_add ha' hb'
  rw [←card_union_of_disjoint hd,cover,←Nat.add_mul] at total
  exact Nat.lt_of_mul_lt_mul_right (h.large.trans_le total)

/-- Every vertex has at least the other graph's independence number as its degree. -/
theorem RankProductObstruction.degree_ge [DecidableRel G.Adj]
    (h : RankProductObstruction G H S) (v : U) (hv : v ∈ S) :
    rankOn H S ≤ (S.filter (G.Adj v)).card := by
  let T := (S.erase v).filter fun x => ¬G.Adj v x
  have hsub : T ⊆ S.erase v := filter_subset ..
  have hlt := (h.smaller T (hsub.trans_ssubset (erase_ssubset hv))).trans
    (Nat.mul_le_mul_left (rankOn G T) (rankOn_mono H (hsub.trans (erase_subset ..))))
  obtain ⟨I,hIT,hi,hI⟩ := exists_max_indep G T
  have hvI : v ∉ I := fun h => notMem_erase v S (hsub (hIT h))
  have hnew := independent_insert_of_nonadjacent G hi v (fun x hx => (mem_filter.mp (hIT hx)).2)
  have cap := card_le_rankOn G (insert_subset hv (hIT.trans (hsub.trans (erase_subset ..)))) hnew
  rw [card_insert_of_notMem hvI,hI] at cap
  have hmul := Nat.mul_le_mul_right (rankOn H S) cap
  rw [Nat.add_mul,Nat.one_mul] at hmul
  have split := (S.erase v).card_filter_add_card_filter_not (G.Adj v)
  change ((S.erase v).filter (G.Adj v)).card + T.card = (S.erase v).card at split
  have hcard := card_erase_add_one hv
  have hm := card_le_card (filter_subset_filter (G.Adj v) (erase_subset v S))
  have := h.large
  omega

omit [DecidableEq U] in
theorem exists_product_obstruction (G H : SimpleGraph U) (A : Finset U)
    (hA : rankOn G A*rankOn H A < A.card) :
    ∃ S ⊆ A, RankProductObstruction G H S := by
  classical
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    by_cases h : ∃ W ⊂ A, rankOn G W*rankOn H W < W.card
    · obtain ⟨W,hW,hw⟩ := h
      obtain ⟨S,hS,hs⟩ := ih W hW hw
      exact ⟨S,hS.trans hW.le,hs⟩
    · refine ⟨A,Subset.rfl,hA,?_⟩
      intro W hW
      exact le_of_not_gt fun e => h ⟨W,hW,e⟩

/-- For two distinct colors a rank-one set in one color is independent in the other. -/
theorem RankProductObstruction.two_le_left {r : ℕ} {c : Sym2 U → Fin r} {i j : Fin r}
    (h : RankProductObstruction (colorGraph c i) (colorGraph c j) S) (hij : i ≠ j) :
    2 ≤ rankOn (colorGraph c i) S := by
  by_contra! hlow
  have aone : rankOn (colorGraph c i) S=1 := by have := h.inseparable.rank_pos; omega
  have hcap := other_rank_on_clique (B := S) c hij aone
  simp only [inter_self] at hcap
  have hsz := h.card_eq
  rw [aone,Nat.one_mul] at hsz
  omega

end Product

/-- The two simultaneous independence caps can be attained as actual
independence numbers on a single set, inseparable in both colors. -/
theorem exists_two_color_product_obstruction {r : ℕ} (hr : 3 ≤ r)
    (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c) :
    ∃ i j : Fin r, i ≠ j ∧ ∃ W : Finset V,
      RankProductObstruction (colorGraph c i) (colorGraph c j) W ∧
      rankOn (colorGraph c i) W + rankOn (colorGraph c j) W ≤ r+1 ∧
      2 ≤ rankOn (colorGraph c i) W ∧ 2 ≤ rankOn (colorGraph c j) W := by
  obtain ⟨i,j,hij,a,b,_,_,hs,W,hW,ha,hb'⟩ := exists_two_color_rank_intersection hr hn c hb
  let G := colorGraph c i
  let H := colorGraph c j
  have big : rankOn G W*rankOn H W<W.card := (Nat.mul_le_mul ha hb').trans_lt (by omega)
  obtain ⟨S,hSW,h⟩ := exists_product_obstruction G H W big
  have hg' := (rankOn_mono G hSW).trans ha
  have hh' := (rankOn_mono H hSW).trans hb'
  exact ⟨i,j,hij,S,h,(Nat.add_le_add hg' hh').trans hs,h.two_le_left hij,h.symm.two_le_left hij.symm⟩

end Erdos617
