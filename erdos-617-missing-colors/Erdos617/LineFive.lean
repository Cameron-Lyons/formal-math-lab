import Erdos617.LineMultiplicity
import Erdos617.SmallRange

namespace Erdos617

open Finset SimpleGraph

variable {V L : Type*} [Fintype V] [DecidableEq V] [DecidableEq L] {r : ℕ}

omit [DecidableEq V] in
/-- The label neighbors of a full star are independent in the endpoint graph. -/
theorem full_line_star_triangle_free (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r)
    (p : V → Sym2 L) (rep : LineRepresentation (colorGraph c k) univ p)
    {i a b : L} (hi : (lineStar p i).card = r)
    (hia : s(i,a) ∈ univ.image p) (hib : s(i,b) ∈ univ.image p)
    (hab : s(a,b) ∈ univ.image p) : False := by
  obtain ⟨u,_,hu⟩ := mem_image.mp hia
  obtain ⟨v,_,hv⟩ := mem_image.mp hib
  obtain ⟨x,_,hx⟩ := mem_image.mp hab
  have ia : i≠a := by simpa [hu,Sym2.mk_isDiag_iff] using rep.distinct u (mem_univ _)
  have ib : i≠b := by simpa [hv,Sym2.mk_isDiag_iff] using rep.distinct v (mem_univ _)
  have ab : a≠b := by simpa [hx,Sym2.mk_isDiag_iff] using rep.distinct x (mem_univ _)
  have huS : u ∈ lineStar p i := by simp [lineStar,hu]
  have hvS : v ∈ lineStar p i := by simp [lineStar,hv]
  have hxS : x ∉ lineStar p i := by simp [lineStar,hx,ia,ib]
  have adju : (colorGraph c k).Adj x u := by
    apply (rep.adj x (mem_univ _) u (mem_univ _) (fun e => hxS (e ▸ huS))).mpr
    apply Finset.not_disjoint_iff.mpr
    exact ⟨a,by simp [hx,Sym2.toFinset_mk_eq],by simp [hu,Sym2.toFinset_mk_eq]⟩
  have adjv : (colorGraph c k).Adj x v := by
    apply (rep.adj x (mem_univ _) v (mem_univ _) (fun e => hxS (e ▸ hvS))).mpr
    apply Finset.not_disjoint_iff.mpr
    exact ⟨b,by simp [hx,Sym2.toFinset_mk_eq],by simp [hv,Sym2.toFinset_mk_eq]⟩
  have eq := exterior_clique_neighbor_unique c hb k (lineStar p i) ⟨rep.star_isClique i,hi⟩ x hxS huS hvS adju adjv
  have endeq := Sym2.eq_iff.mp (hu.symm.trans ((congrArg p eq).trans hv))
  grind

/-- Mantel's bound for the vertices whose two labels are full. -/
theorem full_line_edge_bound (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r)
    (p : V → Sym2 L) (rep : LineRepresentation (colorGraph c k) univ p)
    (F : Finset L) (hne : F.Nonempty) (hsize : ∀ i ∈ F, (lineStar p i).card = r)
    (hinj : ∀ i ∈ F, Set.InjOn p (↑(lineStar p i) : Set V)) :
    4*(univ.filter (fun x => (p x).toFinset ⊆ F)).card ≤ F.card^2 := by
  classical
  let X := univ.filter (fun x => (p x).toFinset ⊆ F)
  let N (i : L) := F.filter (fun j => s(i,j) ∈ univ.image p)
  let B (i : L) := X.filter (fun x => i∈(p x).toFinset)
  have row (i : L) (hi : i ∈ F) : (B i).card ≤ (N i).card := by
    have pick (x : B i) : ∃ j ∈ N i, p x.val=s(i,j) := by
      obtain ⟨hx,hi'⟩ := mem_filter.mp x.prop
      obtain ⟨j,eq⟩ := Sym2.mem_iff_exists.mp (Sym2.mem_toFinset.mp hi')
      have hj : j ∈ (p x.val).toFinset := by simp [eq,Sym2.toFinset_mk_eq]
      exact ⟨j,mem_filter.mpr ⟨(mem_filter.mp hx).2 hj,mem_image.mpr ⟨_,mem_univ _,eq⟩⟩,eq⟩
    choose f hf eq using pick
    apply card_le_card_of_injective (f:=fun x => ⟨f x,hf x⟩)
    intro x y h
    apply Subtype.ext
    exact hinj i hi (mem_filter.mpr ⟨mem_univ _,(mem_filter.mp x.prop).2⟩)
      (mem_filter.mpr ⟨mem_univ _,(mem_filter.mp y.prop).2⟩)
      ((eq x).trans ((congrArg (s(i,·)) (congrArg Subtype.val h)).trans (eq y).symm))
  obtain ⟨i,hi,hmax⟩ := F.exists_max_image (fun j => (N j).card) hne
  have covered : X ⊆ (F \ N i).biUnion B := by
    intro x hx
    obtain ⟨a,b,eq⟩ := Sym2.exists.mp (show ∃ e : Sym2 L, p x=e from ⟨_,rfl⟩)
    have ha : a ∈ (p x).toFinset := by simp [eq,Sym2.toFinset_mk_eq]
    have hb' : b ∈ (p x).toFinset := by simp [eq,Sym2.toFinset_mk_eq]
    have someEnd : a ∉ N i ∨ b ∉ N i := by
      by_contra! both
      exact full_line_star_triangle_free c hb k p rep (hsize _ hi) (mem_filter.mp both.1).2
        (mem_filter.mp both.2).2 (mem_image.mpr ⟨_,mem_univ _,eq⟩)
    rcases someEnd with h | h
    · exact mem_biUnion.mpr ⟨a,mem_sdiff.mpr ⟨(mem_filter.mp hx).2 ha,h⟩,mem_filter.mpr ⟨hx,ha⟩⟩
    · exact mem_biUnion.mpr ⟨b,mem_sdiff.mpr ⟨(mem_filter.mp hx).2 hb',h⟩,mem_filter.mpr ⟨hx,hb'⟩⟩
  have bound := (card_le_card covered).trans card_biUnion_le
  have small := sum_le_sum (s:=F \ N i) (fun j hj => (row j (mem_sdiff.mp hj).1).trans (hmax j (mem_sdiff.mp hj).1))
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at small
  have split := card_sdiff_add_card_inter F (N i)
  rw [inter_eq_right.mpr (filter_subset ..)] at split
  change 4*X.card ≤ F.card^2
  have prod := bound.trans small
  rcases le_total (F \ N i).card (N i).card with h | h
  · obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le h
    nlinarith only [prod,congrArg (·^2) split,congrArg (·^2) hd,congrArg (· * (F \ N i).card) hd,Nat.zero_le (d^2),congrArg (· * d) hd]
  · obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le h
    nlinarith only [prod,congrArg (·^2) split,congrArg (·^2) hd,congrArg (· * (N i).card) hd,Nat.zero_le (d^2),congrArg (· * d) hd]

omit [DecidableEq V] in
/-- Each represented edge uses zero, one, or two full endpoints. Counting
them relates the numbers of edges wholly on either side of a label partition. -/
private theorem endpoint_partition_count (p : V → Sym2 L) (C D : Finset L) (r : ℕ)
    (hcov : ∀ x, (p x).toFinset ⊆ C) (hnd : ∀ x, ¬(p x).IsDiag)
    (hsize : ∀ i ∈ C \ D, (lineStar p i).card = r) :
    (univ.filter (fun x => (p x).toFinset ⊆ D)).card + (C\D).card*r =
      Fintype.card V + (univ.filter (fun x => (p x).toFinset ⊆ C\D)).card := by
  classical
  let F := C \ D
  have per (x : V) (_ : x∈univ) :
      (if (p x).toFinset ⊆ D then 1 else 0 : ℕ)+(F.filter fun i => i∈(p x).toFinset).card =
        1+(if (p x).toFinset ⊆ F then 1 else 0 : ℕ) := by
    obtain ⟨a,b,eq⟩ := Sym2.exists.mp (show ∃ e : Sym2 L, p x=e from ⟨_,rfl⟩)
    have hne : a ≠ b := by simpa [eq,Sym2.mk_isDiag_iff] using hnd x
    have ha : a ∈ C := hcov x (by simp [eq,Sym2.toFinset_mk_eq])
    have hb : b ∈ C := hcov x (by simp [eq,Sym2.toFinset_mk_eq])
    rw [filter_mem_eq_inter,inter_comm F,←filter_mem_eq_inter]
    by_cases had : a∈D <;> by_cases hbd : b∈D <;>
      simp [eq,Sym2.toFinset_mk_eq,filter_insert,filter_singleton,insert_subset_iff,singleton_subset_iff,F,ha,hb,hne,had,hbd]
  have tot := sum_congr rfl per
  simp only [sum_add_distrib,sum_boole,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at tot
  have incidence := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s:=F) (t:=univ) (fun i x => i∈(p x).toFinset)
  change (∑ i∈F,(lineStar p i).card)=∑ x,(F.filter fun i => i∈(p x).toFinset).card at incidence
  have sizes : ∀ i ∈ F, (lineStar p i).card=r := hsize
  rw [←incidence,sum_congr rfl sizes,sum_const,nsmul_eq_mul] at tot
  exact tot

/-- Four times the number of represented edges whose two endpoint stars are
deficient is at most (d−1)²+4 when there are d ≥ 1 deficient labels. -/
theorem deficient_line_edge_bound (hn : Fintype.card V = r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r) (p : V → Sym2 L)
    (rep : LineRepresentation (colorGraph c k) univ p) (C : Finset L) (hc : C.card=2*r+1)
    (hcover : ∀ x, (p x).toFinset ⊆ C) (hsize : ∀ i∈C, (lineStar p i).card ≤ r)
    (hinj : ∀ i∈C, (lineStar p i).card=r → Set.InjOn p (↑(lineStar p i) : Set V))
    (hD : 0 < (deficientLineLabels p C r).card) :
    4*(univ.filter (fun x => (p x).toFinset ⊆ deficientLineLabels p C r)).card ≤
      ((deficientLineLabels p C r).card-1)^2+4 := by
  classical
  let D := deficientLineLabels p C r
  let F := C\D
  have full (i : L) (hi : i ∈ F) : (lineStar p i).card=r := by
    obtain ⟨hi,hn⟩ := mem_sdiff.mp hi
    have lt : ¬ (lineStar p i).card < r := fun lt => hn (mem_filter.mpr ⟨hi,lt⟩)
    exact le_antisymm (hsize i hi) (Nat.le_of_not_lt lt)
  have split : F.card+D.card=2*r+1 := (card_sdiff_add_card_eq_card
    (show D ⊆ C from filter_subset ..)).trans hc
  have fsum : F.card+(D.card-1)=2*r := by change 0<D.card at hD; omega
  have mantel : 4*(univ.filter (fun x => (p x).toFinset ⊆ F)).card ≤ F.card^2 := by
    rcases F.eq_empty_or_nonempty with h0|hpos
    · have nil : univ.filter (fun x => (p x).toFinset ⊆ F)=∅ :=
        eq_empty_iff_forall_notMem.mpr fun x hx => by
          have htwo := (p x).card_toFinset_of_not_isDiag (rep.distinct x (mem_univ _))
          have bound := card_le_card (mem_filter.mp hx).2
          rw [h0,card_empty] at bound
          omega
      simp [nil]
    · exact full_line_edge_bound c hb k p rep F hpos full
        (fun i hi => hinj i (mem_sdiff.mp hi).1 (full i hi))
  have count := endpoint_partition_count p C D r hcover (fun x => rep.distinct x (mem_univ _)) full
  change _ + F.card*r=Fintype.card V+_ at count
  rw [hn] at count
  change 4*(univ.filter (fun x => (p x).toFinset ⊆ D)).card ≤ (D.card-1)^2+4
  nlinarith only [mantel,count,congrArg (·^2) fsum,congrArg (·*F.card) fsum]

/-- The multiplicities on deficient labels must account for the required
ordered parallel pairs in a balanced line-graph color. -/
theorem line_deficient_parallel_bound (hr : 3 ≤ r) (hn : Fintype.card V = r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r) (p : V → Sym2 L)
    (rep : LineRepresentation (colorGraph c k) univ p) (C : Finset L) (hc : C.card=2*r+1)
    (hcover : ∀ x, (p x).toFinset ⊆ C) (hsize : ∀ i∈C, (lineStar p i).card ≤ r)
    (hinj : ∀ i∈C, (lineStar p i).card=r → Set.InjOn p (↑(lineStar p i) : Set V))
    (hD : 0 < (deficientLineLabels p C r).card) (M : ℕ) (hm : ∀ e, lineMultiplicity p e ≤ M) :
    4*((r-2)*(r+1)) ≤ (M-1)*(((deficientLineLabels p C r).card-1)^2+4) := by
  classical
  have low := line_parallel_excess hr hn c hb k p rep
  have mult := parallel_pairs_le_repeated p (M-1) (fun e => (hm e).trans (by omega))
  have cap := deficient_line_edge_bound hn c hb k p rep C hc hcover hsize hinj hD
  have sub := card_le_card (show (univ.filter fun x => 2≤lineMultiplicity p (p x)) ⊆
      univ.filter (fun x => (p x).toFinset ⊆ deficientLineLabels p C r) from
    fun _ hx => mem_filter.mpr ⟨mem_univ _,repeated_endpoints_are_deficient p C r hcover hsize hinj (mem_filter.mp hx).2⟩)
  have inc := (low.trans mult).trans (Nat.mul_le_mul_left (M-1) sub)
  have step := Nat.mul_le_mul_left 4 inc
  have upper := Nat.mul_le_mul_left (M-1) cap
  nlinarith only [step,upper]

/-- The conjectured missing-color set exists if one color contains a spanning
line graph with independence number at most r and edge multiplicity at most five. -/
theorem missing_of_line_subgraph_of_multiplicity_le_five (hr : 3 ≤ r)
    (hn : Fintype.card V = r^2+1) (c : Sym2 V → Fin r) (k : Fin r) (H : SimpleGraph V)
    (hsub : H ≤ colorGraph c k) (hα : H.indepNum ≤ r) (p : V → Sym2 L)
    (rep : LineRepresentation H univ p) (hm : ∀ e, lineMultiplicity p e ≤ 5) :
    ∃ (S : Finset V) (l : Fin r), l ≠ k ∧ S.card=r+1 ∧
      ∀ u∈S, ∀ v∈S, u≠v → c s(u,v)≠l := by
  apply missing_of_spanning_subgraph (by omega) c k H hsub hα
  intro d eq
  by_cases small : r≤6
  · exact missing_of_at_most_six_colors hr small hn d
  by_contra no
  have hb := balanced_of_no_witness d no
  have rep' : LineRepresentation (colorGraph d k) univ p := eq ▸ rep
  obtain ⟨C,hc,cover,size,inj,count,defle,_⟩ := line_label_data hr hn d hb k p rep'
  let D := deficientLineLabels p C r
  have hce : C.card=2*r+1 := by
    by_contra wrong
    have cap := sum_le_sum (s:=C) fun i _ => size i
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id,count] at cap
    nlinarith only [cap,Nat.mul_le_mul_right r (show C.card≤2*r by omega)]
  have pos : 0<D.card := by
    by_contra! notpos
    have empty : D=∅ := card_eq_zero.mp (by omega)
    have full (i : L) (hi : i∈C) : (lineStar p i).card=r := by
      apply le_antisymm (size i)
      by_contra! lt
      have hiD : i ∈ D := mem_filter.mpr ⟨hi,lt⟩
      simp [empty] at hiD
    rw [sum_congr rfl full,sum_const,nsmul_eq_mul,hce] at count
    nlinarith only [count,hr]
  have bound := line_deficient_parallel_bound hr hn d hb k p rep' C hce cover
    (fun i _ => size i) inj pos 5 hm
  change 4*((r-2)*(r+1)) ≤ 4*((D.card-1)^2+4) at bound
  have sq := Nat.pow_le_pow_left (show D.card-1≤r-3 by change D.card ≤ r-2 at defle; omega) 2
  obtain ⟨u,eqr⟩ : ∃ u, r=u+7 := ⟨r-7,by omega⟩
  rw [eqr,show u+7-2=u+5 by omega] at bound
  rw [eqr,show u+7-3=u+4 by omega] at sq
  nlinarith only [bound,sq,Nat.zero_le u]

end Erdos617
