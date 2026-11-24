import Erdos617.OddEndpoint
import Erdos617.RankObstruction
import Erdos617.RankIntersection

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {r s : ℕ}

/-- Unless a smaller obstruction exists, every color at the odd endpoint has
strictly fewer than s edges of shortfall from the average. -/
theorem odd_endpoint_edge_floor (hs : 1 ≤ s) (hr : r=2*s+1)
    (hn : Fintype.card V = r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r)
    (hsmall : ∀ a ≤ s, ∀ W : Finset V, ¬MinimalObstruction c k a W) :
    r*(r^2+1) < 2*(colorGraph c k).edgeFinset.card+2*s := by
  classical
  let G := colorGraph c k
  have cap : rankOn G univ ≤ r := by
    obtain ⟨I,_,hi,hI⟩ := exists_max_indep G univ
    by_contra! h
    obtain ⟨J,hJ,hc⟩ := exists_subset_card_eq (s:=I) (show r+1 ≤ I.card by omega)
    obtain ⟨x,hx,y,hy,hn,he⟩ := hb J hc k
    exact hi (hJ hx) (hJ hy) hn ⟨hn,he⟩
  obtain ⟨P,hu,hd,hat,ha⟩ := exists_rank_partition G univ
  have count := card_biUnion hd
  simp only [id_eq,hu,card_univ,hn] at count
  obtain ⟨A,hA,hlarge⟩ : ∃ A∈P, rankOn G A*r < A.card := by
    by_contra! hall
    have ub := sum_le_sum hall
    rw [←sum_mul,ha,←count] at ub
    have := Nat.mul_le_mul_right r cap
    rw [pow_two] at ub
    omega
  obtain ⟨W,hW,hw⟩ := exists_subset_card_eq (s:=A) (Nat.succ_le_of_lt hlarge)
  have big : s < rankOn G A := by
    by_contra! h
    have none (I : Finset V) (hI : I ⊆ W) (hi : G.IsNIndepSet (rankOn G A+1) I) : False := by
      have hc := card_le_rankOn G (hI.trans hW) hi.isIndepSet
      rw [hi.card_eq] at hc
      omega
    obtain ⟨a,T,ha,_,hm⟩ := minimalObstruction_of_failure (c:=c) (k:=k) hw none
    exact hsmall a (ha.trans h) T hm
  have per := sum_le_sum (s:=P.erase A) (f:=fun _ => 1) fun B hB =>
    (hat B (mem_of_mem_erase hB)).rank_pos
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,card_erase_of_mem hA] at per
  have parts := sum_erase_add P (rankOn G) hA
  rw [ha] at parts
  have lim : P.card ≤ s+1 := by omega
  have dens := rank_partition_density G P hd hat r
  rw [hu,card_univ,hn,blockEdges_univ,ha] at dens
  have lim' := Nat.mul_le_mul_left (r-1) lim
  have cap' := Nat.mul_le_mul_left (r.choose 2+1) cap
  have bound : r*(r^2+1) < G.edgeFinset.card+(r.choose 2+1)*r+(r-1)*(s+1) := by
    rcases lt_or_eq_of_le lim with less | eq
    · have strict := Nat.mul_lt_mul_of_pos_left less (by omega : 0 < r-1)
      omega
    have sg : r*A.card < blockEdges G A+(r.choose 2+1)*rankOn G A+(r-1) := by
      refine lt_of_le_of_ne (rank_density G A (hat A hA) r) ?_
      intro tight
      have endpoint := rank_density_order_cap G A (hat A hA) (by omega : 1 ≤ r) tight
      rw [Nat.mul_comm (rankOn G A) r] at hlarge
      obtain ⟨C,hC,hcl⟩ := exists_clique_of_rank_density_eq G A (hat A hA) r (by omega) (by omega) tight
      exact (hat A hA).no_full_clique hb (by change 1<rankOn G A; omega)
        (by change rankOn G A < r; omega) hC hcl
    have sl := sum_lt_sum (f:=fun B : Finset V => r*B.card)
      (g:=fun B : Finset V => blockEdges G B+(r.choose 2+1)*rankOn G B+(r-1))
      (fun B hB => rank_density G B (hat B hB) r) ⟨A,hA,sg⟩
    simp only [sum_add_distrib,←mul_sum,←count,ha,sum_const,nsmul_eq_mul,Nat.cast_id] at sl
    have boundary := boundary_edge_count G univ P hu.le hd
    rw [blockEdges_univ] at boundary
    rw [Nat.mul_comm P.card] at sl
    omega
  have ch := congrArg (r*·) (twice_choose_two r)
  change r*(r^2+1) < 2*G.edgeFinset.card+2*s
  generalize he : G.edgeFinset.card = e at bound ⊢
  rw [hr, Nat.add_sub_cancel] at bound
  rw [hr] at ch ⊢
  nlinarith only [ch,bound]

/-- At least three colors are at or below the mean edge count at the odd endpoint. -/
theorem odd_endpoint_three_sparse (hs : 1 ≤ s) (hr : r=2*s+1)
    (hn : Fintype.card V = r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c)
    (hsmall : ∀ (k : Fin r) (a : ℕ), a ≤ s → ∀ W : Finset V, ¬MinimalObstruction c k a W) :
    3 ≤ (univ.filter fun k => 2*(colorGraph c k).edgeFinset.card ≤ r*(r^2+1)).card := by
  classical
  let E (i : Fin r) := (colorGraph c i).edgeFinset.card
  let μ := r*(2*s^2+2*s+1)
  have even : r*(r^2+1)=2*μ := by dsimp [μ]; rw [hr]; ring
  have per (i : Fin r) (_ : i ∈ univ) : μ+1 ≤ E i + if 2*E i ≤ r*(r^2+1) then s else 0 := by
    have h := odd_endpoint_edge_floor hs hr hn c hb i (hsmall i)
    change r*(r^2+1) < 2*E i+2*s at h
    rw [even] at h ⊢
    split <;> omega
  have lower := sum_le_sum per
  simp only [sum_add_distrib] at lower
  rw [←sum_filter] at lower
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at lower
  have total := sum_color_edges c
  change ∑ i, E i = (Fintype.card V).choose 2 at total
  rw [hn] at total
  have sumEq : (r^2+1).choose 2=r*μ := by
    have h := twice_choose_two (r^2+1)
    have he := congrArg (r*·) even
    nlinarith only [he,h]
  rw [total,sumEq,Nat.mul_one] at lower
  by_contra! fewer
  change (univ.filter (fun i => 2*E i ≤ r*(r^2+1))).card < 3 at fewer
  have le := Nat.mul_le_mul_right s (show (univ.filter (fun i => 2*E i ≤ r*(r^2+1))).card ≤ 2 by omega)
  omega

theorem odd_endpoint_two_sparse (hs : 1 ≤ s) (hr : r=2*s+1)
    (hn : Fintype.card V = r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c)
    (hsmall : ∀ (k : Fin r) (a : ℕ), a ≤ s → ∀ W : Finset V, ¬MinimalObstruction c k a W) :
    ∃ i j : Fin r, i≠j ∧ 2*(colorGraph c i).edgeFinset.card ≤ r*(r^2+1) ∧
      2*(colorGraph c j).edgeFinset.card ≤ r*(r^2+1) := by
  have many := odd_endpoint_three_sparse hs hr hn c hb hsmall
  obtain ⟨i,hi,j,hj,hij⟩ := one_lt_card.mp (show 1 < _ by exact lt_of_lt_of_le (by decide : 1<3) many)
  exact ⟨i,j,hij,(mem_filter.mp hi).2,(mem_filter.mp hj).2⟩

theorem card_inter_complement_sum (A B : Finset V) (Q : Finset (Finset V))
    (hu : Q.biUnion id=univ \ A) (hd : (↑Q : Set (Finset V)).PairwiseDisjoint id) :
    (∑ C ∈ Q,(B ∩ C).card)+(B ∩ A).card=B.card := by
  have dis : (↑Q : Set (Finset V)).PairwiseDisjoint (fun C => B ∩ C) :=
    fun _ hC _ hD hne => (hd hC hD hne).mono inter_subset_right inter_subset_right
  have split := card_sdiff_add_card_inter B A
  rw [←card_biUnion dis]
  change (Q.biUnion (fun C => B ∩ id C)).card+(B ∩ A).card=B.card
  rw [←inter_biUnion,hu]
  rwa [←inter_sdiff_assoc,inter_univ]

theorem full_clique_intersections {c : Sym2 V → Fin r} {i j : Fin r} (hne : i≠j)
    (hr : r=2*s+1) {A : Finset V} (hA : MinimalObstruction c j (s+1) A)
    {Q : Finset (Finset V)} (hc : Q.card=s) (hu : Q.biUnion id=univ \ A)
    (hd : (↑Q : Set (Finset V)).PairwiseDisjoint id ∧ ∀ C∈Q,(colorGraph c j).IsNClique r C)
    {B : Finset V} (hB : (colorGraph c i).IsNClique r B) :
    (B∩A).card=s+1 ∧ ∀ C ∈ Q,(B∩C).card=1 := by
  have indep : (colorGraph c j).IsIndepSet (B : Set V) :=
    fun _ hx _ hy hxy he => hne ((hB.isClique hx hy hxy).2.symm.trans he.2)
  have bound := card_le_rankOn _ (inter_subset_right : B∩A ⊆ A) (indep.mono inter_subset_left)
  rw [hA.rank_eq (by omega)] at bound
  have one (C : Finset V) (hC : C ∈ Q) : (B∩C).card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    by_contra h
    exact indep (mem_inter.mp hx).1 (mem_inter.mp hy).1 h ((hd.2 C hC).isClique (mem_inter.mp hx).2 (mem_inter.mp hy).2 h)
  have all := sum_le_sum one
  have split := card_inter_complement_sum A B Q hu hd.1
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,hc] at all
  rw [hB.card_eq] at split
  refine ⟨by omega,?_⟩
  apply (sum_eq_sum_iff_of_le one).mp
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,hc]
  omega

private theorem two_endpoint_grids {c : Sym2 V → Fin r} {i j : Fin r} (hij : i≠j)
    (hr : r=2*s+1) {A B : Finset V} {P Q : Finset (Finset V)}
    (hA : MinimalObstruction c i (s+1) A) (hB : MinimalObstruction c j (s+1) B)
    (pC : P.card=s) (qC : Q.card=s) (pU : P.biUnion id=univ \ A)
    (qU : Q.biUnion id=univ \ B) (pD : (↑P : Set (Finset V)).PairwiseDisjoint id)
    (qD : (↑Q : Set (Finset V)).PairwiseDisjoint id)
    (pG : ∀ C ∈ P, (colorGraph c i).IsNClique r C)
    (qG : ∀ D ∈ Q, (colorGraph c j).IsNClique r D) :
    (∀ C ∈ P, ∀ D ∈ Q,(C ∩ D).card=1) ∧ (A ∩ B).card=(s+1)^2+1 ∧
    rankOn (colorGraph c i) (A∩B) ≤ s+1 ∧ rankOn (colorGraph c j) (A∩B) ≤ s+1 := by
  have one (C : Finset V) (hC : C ∈ P) := full_clique_intersections hij hr hB qC qU ⟨qD,qG⟩ (pG _ hC)
  have split := card_inter_complement_sum A B P pU pD
  have rows (C : Finset V) (hC : C∈P) : (B∩C).card=s+1 := by simpa [inter_comm B C] using (one C hC).1
  rw [sum_congr rfl rows,sum_const,nsmul_eq_mul,Nat.cast_id,pC,inter_comm B A,hB.card_eq] at split
  have size : (A∩B).card=(s+1)^2+1 := by rw [hr] at split; nlinarith only [split]
  exact ⟨fun C hC => (one C hC).2,size,
    (rankOn_mono _ inter_subset_left).trans_eq (hA.rank_eq (by omega)),
    (rankOn_mono _ inter_subset_right).trans_eq (hB.rank_eq (by omega))⟩

/-- At the odd endpoint a sparse color has fewer than s edges between
different parts of its decomposition. Its s displayed cliques are all
of its monochromatic r-cliques. -/
theorem odd_endpoint_crossing_edges {c : Sym2 V → Fin r} {k : Fin r} {A : Finset V}
    {P : Finset (Finset V)} (hs : 1 ≤ s) (hr : r=2*s+1) (hb : Balanced c)
    (hk : 2*(colorGraph c k).edgeFinset.card ≤ r*(r^2+1))
    (hA : MinimalObstruction c k (s+1) A) (hN : P.card=s) (hU : P.biUnion id=univ \ A)
    (hD : (↑P : Set (Finset V)).PairwiseDisjoint id)
    (hG : ∀ C∈P,(colorGraph c k).IsNClique r C) :
    let G := colorGraph c k
    (inducedEdgeSet G univ \ (insert A P).biUnion (inducedEdgeSet G)).card < s ∧
      ∀ D : Finset V, G.IsNClique r D ↔ D ∈ P := by
  classical
  intro G
  have disA (C : Finset V) (hC : C∈P) : Disjoint A C := by
    have sub := biUnion_subset.mp hU.le C hC
    exact disjoint_sdiff.mono_right sub
  have notA : A ∉ P := by
    intro h
    obtain ⟨x,hx⟩ := card_pos.mp (show 0 < A.card by rw [hA.card_eq]; omega)
    exact disjoint_left.mp (disA A h) hx hx
  have dis : (↑(insert A P) : Set (Finset V)).PairwiseDisjoint id := by
    rw [coe_insert]
    exact hD.insert_of_notMem notA disA
  let X := inducedEdgeSet G univ \ (insert A P).biUnion (inducedEdgeSet G)
  have edge := boundary_edge_count G univ (insert A P) (subset_univ _) dis
  change X.card+(∑ C∈insert A P,blockEdges G C)=blockEdges G univ at edge
  have cliqueEdges (C : Finset V) (hC : C∈P) : blockEdges G C=r.choose 2 := by
    let H := G.induce (C : Set V)
    have eq : H=⊤ := G.induce_eq_top.mpr (hG C hC).isClique
    have eqq : H.edgeFinset=(⊤ : SimpleGraph C).edgeFinset := by
      ext e
      rw [mem_edgeFinset,mem_edgeFinset,eq]
      rfl
    change H.edgeFinset.card=r.choose 2
    rw [eqq,card_edgeFinset_top_eq_card_choose_two,Fintype.card_coe,(hG C hC).card_eq]
  rw [sum_insert notA,sum_congr rfl cliqueEdges,sum_const,hN,nsmul_eq_mul,Nat.cast_id,
    blockEdges_univ] at edge
  have atom := hA.rank_inseparable (by omega)
  have dens : r*A.card < blockEdges G A+(r.choose 2+1)*(s+1)+(r-1) := by
    have rankEq : rankOn G A=s+1 := hA.rank_eq (by omega)
    rw [←rankEq]
    refine lt_of_le_of_ne (rank_density G A atom r) ?_
    intro eq
    obtain ⟨C,hC,cl⟩ := exists_clique_of_rank_density_eq G A atom r (by omega)
      (by rw [rankEq,Nat.mul_comm r]; exact hA.card_eq) eq
    exact hA.no_clique hb (by omega) C hC cl
  rw [hA.card_eq] at dens
  have short : X.card<s := by
    change 2*G.edgeFinset.card ≤ r*(r^2+1) at hk
    generalize h_e : G.edgeFinset.card = e at edge hk
    generalize h_a : blockEdges G A = a at edge dens
    generalize h_x : X.card = x at edge ⊢
    have ch := twice_choose_two r
    rw [hr] at edge hk ch
    rw [hr,Nat.add_sub_cancel] at dens
    nlinarith only [edge,hk,ch,dens]
  refine ⟨short,fun D => ⟨?_,hG D⟩⟩
  intro hCl
  obtain ⟨x,hxD,hxA⟩ : ∃ x∈D,x∉A := by
    by_contra! h
    exact hA.no_clique hb (by omega) D h hCl
  have hxU : x∈P.biUnion id := hU ▸ mem_sdiff.mpr ⟨mem_univ _,hxA⟩
  obtain ⟨C,hCP,hxC⟩ := mem_biUnion.mp hxU
  by_contra hDP
  obtain ⟨z,hzD,hzC⟩ : ∃ z∈D,z∉C := by
    by_contra! sub
    exact hDP ((eq_of_subset_of_card_le sub ((hG C hCP).card_eq.trans hCl.card_eq.symm).le) ▸ hCP)
  have outside (y : V) (hy : y∈D.erase x) : y∉C := by
    intro hyC
    have hz {u : V} (hu : u∈C) : z≠u := fun eq => hzC (eq ▸ hu)
    exact (mem_erase.mp hy).1 (exterior_clique_neighbor_unique c hb k C (hG C hCP) z hzC hyC hxC
      (hCl.isClique hzD (mem_of_mem_erase hy) (hz hyC)) (hCl.isClique hzD hxD (hz hxC)))
  have sub : (D.erase x).map (Sym2.mkEmbedding x) ⊆ X := by
    intro e he
    obtain ⟨y,hy,rfl⟩ := mem_map.mp he
    change s(x,y) ∈ inducedEdgeSet G univ \ (insert A P).biUnion (inducedEdgeSet G)
    refine mem_sdiff.mpr ⟨(mem_inducedEdgeSet G).mpr ⟨mem_univ _,mem_univ _,
      hCl.isClique hxD (mem_of_mem_erase hy) (mem_erase.mp hy).1.symm⟩,?_⟩
    intro mem
    obtain ⟨B,hB,hm⟩ := mem_biUnion.mp mem
    obtain ⟨hxB,hyB,_⟩ := (mem_inducedEdgeSet G).mp hm
    by_cases heq : B=C
    · exact outside y hy (heq ▸ hyB)
    · exact disjoint_left.mp (dis hB (mem_insert_of_mem hCP) heq) hxB hxC
  have lower := card_le_card sub
  rw [card_map,card_erase_of_mem hxD,hCl.card_eq] at lower
  omega

/-- Simultaneous odd-endpoint decompositions for all sparse colors. There are
at least three of them, and every pair of the clique families crosses in a grid. -/
theorem odd_endpoint_grids (hs : 1 ≤ s) (hr : r=2*s+1)
    (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c)
    (hsmall : ∀ (k : Fin r) (a : ℕ), a ≤ s → ∀ W : Finset V, ¬MinimalObstruction c k a W) :
    let T := univ.filter fun i => 2*(colorGraph c i).edgeFinset.card ≤ r*(r^2+1)
    3 ≤ T.card ∧ ∃ (A : T → Finset V) (P : T → Finset (Finset V)),
      (∀ i, MinimalObstruction c i.val (s+1) (A i) ∧ (P i).card=s ∧
        (P i).biUnion id=univ \ A i ∧ (↑(P i) : Set (Finset V)).PairwiseDisjoint id ∧
        (∀ C, (colorGraph c i.val).IsNClique r C ↔ C∈P i) ∧
        (inducedEdgeSet (colorGraph c i.val) univ \
          (insert (A i) (P i)).biUnion (inducedEdgeSet (colorGraph c i.val))).card < s) ∧
      ∀ i j, i≠j → (∀ C∈P i, ∀ D∈P j,(C∩D).card=1) ∧
        (A i ∩ A j).card=(s+1)^2+1 ∧ rankOn (colorGraph c i.val) (A i ∩ A j) ≤ s+1 ∧
        rankOn (colorGraph c j.val) (A i ∩ A j) ≤ s+1 := by
  classical
  intro T
  choose A P hA hN hU hD hG using fun i : T =>
    odd_endpoint_of_sparse_color hs hr hn c hb i.val (mem_filter.mp i.prop).2 (hsmall i.val)
  have exactFamily (i : T) := odd_endpoint_crossing_edges hs hr hb (mem_filter.mp i.prop).2
    (hA i) (hN i) (hU i) (hD i) (hG i)
  refine ⟨odd_endpoint_three_sparse hs hr hn c hb hsmall,A,P,
    fun i => ⟨hA i,hN i,hU i,hD i,(exactFamily i).2,(exactFamily i).1⟩,?_⟩
  intro i j hij
  exact two_endpoint_grids (fun eq => hij (Subtype.ext eq)) hr (hA i) (hA j)
    (hN i) (hN j) (hU i) (hU j) (hD i) (hD j) (hG i) (hG j)

/-- If the first obstruction occurs at the odd endpoint, two of the cores
meet in precisely (s+1)²+1 vertices, and both independence numbers there
are at most s+1. The two complement clique families form a grid of singletons. -/
theorem odd_endpoint_intersection (hs : 1 ≤ s) (hr : r=2*s+1)
    (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c)
    (hsmall : ∀ (k : Fin r) (a : ℕ), a ≤ s → ∀ W : Finset V, ¬MinimalObstruction c k a W) :
    ∃ (i j : Fin r) (A B : Finset V) (P Q : Finset (Finset V)),
      i≠j ∧ MinimalObstruction c i (s+1) A ∧ MinimalObstruction c j (s+1) B ∧
      P.card=s ∧ Q.card=s ∧ P.biUnion id=univ \ A ∧ Q.biUnion id=univ \ B ∧
      (∀ C ∈ P, (colorGraph c i).IsNClique r C) ∧
      (∀ D ∈ Q, (colorGraph c j).IsNClique r D) ∧
      (∀ C ∈ P, ∀ D ∈ Q, (C∩D).card=1) ∧
      (A∩B).card=(s+1)^2+1 ∧
      rankOn (colorGraph c i) (A∩B) ≤ s+1 ∧ rankOn (colorGraph c j) (A∩B) ≤ s+1 := by
  obtain ⟨i,j,hij,hi,hj⟩ := odd_endpoint_two_sparse hs hr hn c hb hsmall
  obtain ⟨A,P,hA,pC,pU,pD,pG⟩ := odd_endpoint_of_sparse_color hs hr hn c hb i hi (hsmall i)
  obtain ⟨B,Q,hB,qC,qU,qD,qG⟩ := odd_endpoint_of_sparse_color hs hr hn c hb j hj (hsmall j)
  exact ⟨i,j,A,B,P,Q,hij,hA,hB,pC,qC,pU,qU,pG,qG,
    two_endpoint_grids hij hr hA hB pC qC pU qU pD qD pG qG⟩

end Erdos617
