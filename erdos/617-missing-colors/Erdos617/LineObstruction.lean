module

public import Erdos617.DoubleCoverBound
public import Erdos617.ObstructionBounds
public import Erdos617.MatchingCertificate

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V L : Type*} [DecidableEq V] [Fintype L] [DecidableEq L]
variable {r t : ℕ} {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V}

/-- The labels at the ends of a multigraph edge. Parallel edges may have the same labels. -/
structure LineRepresentation (G : SimpleGraph V) (S : Finset V) (p : V → Sym2 L) : Prop where
  distinct : ∀ x ∈ S, ¬ (p x).IsDiag
  adj : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → (G.Adj x y ↔ ¬ Disjoint (p x).toFinset (p y).toFinset)

omit [Fintype L] in
private theorem matching_bound (h : MinimalObstruction c k t S)
    (p : V → Sym2 L) (rep : LineRepresentation (colorGraph c k) S p)
    (F : Finset (Sym2 L)) (hF : ∀ e ∈ F, e ∈ (fromEdgeSet (↑(S.image p) : Set _)).edgeSet)
    (hD : (↑F : Set (Sym2 L)).PairwiseDisjoint Sym2.toFinset) : F.card ≤ t := by
  classical
  have pick (e : F) : ∃ x ∈ S, p x = e := by
    have hs := hF e e.prop
    rw [edgeSet_fromEdgeSet] at hs
    exact mem_image.mp hs.1
  choose g hg hp using pick
  have hg' : Function.Injective g := fun a b eq => Subtype.ext ((hp a).symm.trans ((congrArg p eq).trans (hp b)))
  let I := univ.image g
  have hIS : I ⊆ S := by
    intro x hx
    obtain ⟨a,_,rfl⟩ := mem_image.mp hx
    exact hg a
  have hind : (colorGraph c k).IsIndepSet (I : Set V) := by
    intro x hx y hy hxy he
    obtain ⟨a,_,rfl⟩ := mem_image.mp hx
    obtain ⟨b,_,rfl⟩ := mem_image.mp hy
    have hd := hD a.prop b.prop (fun eq => hxy (congrArg g (Subtype.ext eq)))
    exact ((rep.adj _ (hg a) _ (hg b) hxy).mp he) (by rwa [hp,hp])
  have hc : I.card=F.card := by simp [I, card_image_of_injective _ hg']
  by_contra! high
  obtain ⟨J,hJ,hcJ⟩ := exists_subset_card_eq (s:=I) (show t+1≤I.card by omega)
  exact h.free J (hJ.trans hIS) ⟨hind.mono hJ,hcJ⟩

omit [Fintype L] in
/-- A Tutte–Berge certificate for the endpoint graph of a line representation
puts every edge of the obstruction in a single part of size at most 2t+1. -/
private theorem line_cover_of_certificate (h : MinimalObstruction c k t S) (hb : Balanced c)
    (hr : 2≤r) (p : V → Sym2 L) (rep : LineRepresentation (colorGraph c k) S p)
    (U : Finset L) (P : Finset (Finset L))
    (hpart : ∀ a b, a ∉ U → b ∉ U →
      (fromEdgeSet (↑(S.image p) : Set _)).Adj a b → ∃ A ∈ P, a ∈ A ∧ b ∈ A)
    (hcnt : U.card+(∑ A ∈ P,A.card/2) ≤ t) :
    ∃ C : Finset L, C.card ≤ 2*t+1 ∧ ∀ x ∈ S, (p x).toFinset ⊆ C := by
  classical
  let B (i : L) := S.filter fun x => i ∈ (p x).toFinset
  let T (C : Finset L) := S.filter fun x => (p x).toFinset ⊆ C
  have bcl (i : L) : (colorGraph c k).IsClique (B i : Set V) := by
    intro x hx y hy hn
    exact (rep.adj _ (mem_filter.mp hx).1 _ (mem_filter.mp hy).1 hn).mpr
      (Finset.not_disjoint_iff.mpr ⟨i,(mem_filter.mp hx).2,(mem_filter.mp hy).2⟩)
  have bcap (i : L) : (B i).card ≤ r := by
    by_contra! tooBig
    obtain ⟨C,hC,hn⟩ := exists_subset_card_eq (Nat.succ_le_of_lt tooBig)
    obtain ⟨j,hj⟩ : (univ.erase k).Nonempty := card_pos.mp (by simp; omega)
    obtain ⟨x,hx,y,hy,hxy,he⟩ := hb C hn j
    exact (mem_erase.mp hj).1 (he.symm.trans (bcl i (hC hx) (hC hy) hxy).2)
  have cover : S ⊆ U.biUnion B ∪ P.biUnion T := by
    intro x hx
    generalize he : p x = e
    induction e using Sym2.inductionOn with
    | _ a b =>
      by_cases ha : a ∈ U
      · exact mem_union_left _ (mem_biUnion.mpr ⟨a,ha,mem_filter.mpr ⟨hx,by simp [he,Sym2.toFinset_mk_eq]⟩⟩)
      by_cases hb' : b ∈ U
      · exact mem_union_left _ (mem_biUnion.mpr ⟨b,hb',mem_filter.mpr ⟨hx,by simp [he,Sym2.toFinset_mk_eq]⟩⟩)
      have hab : a ≠ b := by
        simpa [he,Sym2.mk_isDiag_iff] using rep.distinct x hx
      obtain ⟨A,hA,haA,hbA⟩ := hpart a b ha hb' ((fromEdgeSet_adj _).mpr ⟨mem_image.mpr ⟨x,hx,he⟩,hab⟩)
      exact mem_union_right _ (mem_biUnion.mpr ⟨A,hA,mem_filter.mpr
        ⟨hx,by rw [he,Sym2.toFinset_mk_eq]; exact insert_subset haA (singleton_subset_iff.mpr hbA)⟩⟩)
  have full : ∃ C ∈ P, T C = S := by
    by_contra! hn
    have per (C : Finset L) (hC : C ∈ P) : (T C).card ≤ (C.card/2)*r := by
      have hss : T C ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset ..,hn C hC⟩
      obtain ⟨I,hI,hind,hsize⟩ := h.proper_subset (by omega) _ hss
      have d : (↑I : Set V).PairwiseDisjoint (fun x => (p x).toFinset) := by
        intro x hx y hy hxy
        by_contra notD
        exact hind hx hy hxy ((rep.adj x (hss.le (hI hx)) y (hss.le (hI hy)) hxy).mpr notD)
      have sub : I.biUnion (fun x => (p x).toFinset) ⊆ C :=
        biUnion_subset.mpr fun x hx => (mem_filter.mp (hI hx)).2
      have bd := card_le_card sub
      rw [card_biUnion d, sum_congr rfl (fun x hx => (p x).card_toFinset_of_not_isDiag
        (rep.distinct x (hss.le (hI hx))))] at bd
      simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at bd
      exact hsize.trans (Nat.mul_le_mul_right _ (by omega))
    have s1 := card_biUnion_le (s:=U) (t:=B)
    have s2 := card_biUnion_le (s:=P) (t:=T)
    have h1 := sum_le_sum (s:=U) (fun i _ => bcap i)
    have h2 := sum_le_sum per
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at h1
    rw [← sum_mul] at h2
    have all := (card_le_card cover).trans (card_union_le ..)
    have cap := Nat.mul_le_mul_right r hcnt
    rw [Nat.add_mul] at cap
    have := h.card_eq
    omega
  obtain ⟨C,hC,hfull⟩ := full
  have b := single_le_sum_of_canonicallyOrdered (f:=fun A : Finset L => A.card/2) hC
  exact ⟨C,by omega,fun x hx => (mem_filter.mp (show x ∈ T C from hfull ▸ hx)).2⟩

omit [Fintype L] in
private theorem not_twofold_line_cover (h : MinimalObstruction c k t S) (hb : Balanced c)
    (ht : 2 ≤ t) (htr : t<r) (p : V → Sym2 L) (rep : LineRepresentation (colorGraph c k) S p)
    (C : Finset L) (hC : C.card ≤ 2*t+1) (hpart : ∀ x ∈ S, (p x).toFinset ⊆ C) : False := by
  classical
  let B (i : C) := S.filter fun x => i.val ∈ (p x).toFinset
  have cl (i : C) : (colorGraph c k).IsClique (B i : Set V) := by
    intro x hx y hy hn
    exact (rep.adj _ (mem_filter.mp hx).1 _ (mem_filter.mp hy).1 hn).mpr
      (Finset.not_disjoint_iff.mpr ⟨i.val,(mem_filter.mp hx).2,(mem_filter.mp hy).2⟩)
  have two (x : V) (hx : x ∈ S) : 2 ≤ (univ.filter fun i => x ∈ B i).card := by
    have eq : univ.filter (fun i => x ∈ B i) = (p x).toFinset.subtype (· ∈ C) := by
      ext i
      simp [B,hx]
    rw [eq,card_subtype,filter_eq_self.mpr (hpart _ hx),(p x).card_toFinset_of_not_isDiag (rep.distinct _ hx)]
  have bd := h.twofold_clique_cover_card hb ht htr B (fun _ => filter_subset ..) cl two
  rw [Fintype.card_coe] at bd
  omega

omit [Fintype L] in
private theorem LineRepresentation.finite_labels {G : SimpleGraph V} {p : V → Sym2 L}
    (rep : LineRepresentation G S p) (hne : S.Nonempty) :
    ∃ (A : Finset L) (q : V → Sym2 A), (∀ x ∈ S, (q x).map Subtype.val = p x) ∧ LineRepresentation G S q := by
  classical
  let A := S.biUnion fun x => (p x).toFinset
  have inc {x : V} (hx : x ∈ S) : (p x).toFinset ⊆ A := fun _ hl => mem_biUnion.mpr ⟨x,hx,hl⟩
  obtain ⟨x0,h0⟩ := hne
  let d : A := ⟨(p x0).out.1,inc h0 (Sym2.mem_toFinset.mpr (Sym2.out_fst_mem _))⟩
  have lift (x : V) (hx : x ∈ S) : ∃ e : Sym2 A, e.map Subtype.val = p x := by
    generalize he : p x = v
    induction v using Sym2.inductionOn with
    | _ a b =>
      have s := inc hx
      rw [he,Sym2.toFinset_mk_eq] at s
      exact ⟨s((⟨a,s (by simp)⟩ : A),(⟨b,s (by simp)⟩ : A)),rfl⟩
  let q (x : V) := if hx : x ∈ S then (lift x hx).choose else s(d,d)
  have eq (x : V) (hx : x ∈ S) : (q x).map Subtype.val = p x := by
    simpa [q,hx] using (lift x hx).choose_spec
  refine ⟨A,q,eq,fun x hx hh => rep.distinct x hx ((eq x hx) ▸ (Sym2.isDiag_map Subtype.val_injective).mpr hh),?_⟩
  intro x hx y hy hn
  rw [rep.adj x hx y hy hn,Finset.not_disjoint_iff,Finset.not_disjoint_iff]
  simp only [Sym2.mem_toFinset]
  rw [← eq _ hx,← eq _ hy]
  simp only [Sym2.mem_map]
  constructor
  · rintro ⟨a,⟨u,hu,rfl⟩,v,hv,hvu⟩
    exact ⟨u,hu,Subtype.ext hvu ▸ hv⟩
  · rintro ⟨a,ha,hb⟩
    exact ⟨a.val,⟨a,ha,rfl⟩,a,hb,rfl⟩

omit [Fintype L] in
/-- At most 2t+1 endpoint labels suffice for any line representation of a
minimal obstruction, including the parameter t=r. -/
theorem MinimalObstruction.line_support (h : MinimalObstruction c k t S) (hr : 2≤r)
    (hb : Balanced c) (p : V → Sym2 L) (rep : LineRepresentation (colorGraph c k) S p) :
    ∃ C : Finset L, C.card ≤ 2*t+1 ∧ ∀ x ∈ S, (p x).toFinset ⊆ C := by
  obtain ⟨A,q,eq,qrep⟩ := rep.finite_labels (card_pos.mp (by rw [h.card_eq]; omega))
  obtain ⟨U,P,_,_,hpart,hcnt⟩ := matching_certificate (V:=A) (fromEdgeSet (↑(S.image q) : Set (Sym2 A)))
    t (matching_bound h q qrep)
  obtain ⟨C,hcard,hcover⟩ := line_cover_of_certificate h hb hr q qrep U P hpart hcnt
  refine ⟨C.image Subtype.val,card_image_le.trans hcard,?_⟩
  intro x hx l hl
  rw [← eq x hx,Sym2.mem_toFinset,Sym2.mem_map] at hl
  obtain ⟨u,hu,rfl⟩ := hl
  exact mem_image.mpr ⟨u,hcover x hx (Sym2.mem_toFinset.mpr hu),rfl⟩

omit [Fintype L] in
/-- A minimal obstruction cannot be the line graph of a loopless multigraph.
The endpoints need only encode adjacencies within the obstruction. -/
theorem MinimalObstruction.not_line_representation (h : MinimalObstruction c k t S)
    (hb : Balanced c) (ht : 2 ≤ t) (htr : t<r) (p : V → Sym2 L) :
    ¬ LineRepresentation (colorGraph c k) S p := by
  intro rep
  obtain ⟨C,hcard,hcover⟩ := h.line_support (by omega) hb p rep
  exact not_twofold_line_cover h hb ht htr p rep C hcard hcover

omit [Fintype L] in
/-- Erdős 617 holds whenever every color graph is the line graph of a loopless
multigraph. Multiple vertices may represent parallel edges. -/
theorem missing_of_line_representations [Fintype V] (hr : 3 ≤ r)
    (hn : Fintype.card V = r^2+1) (c : Sym2 V → Fin r)
    (hline : ∀ k, ∃ p : V → Sym2 L, LineRepresentation (colorGraph c k) univ p) :
    ∃ (S : Finset V) (k : Fin r), S.card = r+1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u,v) ≠ k := by
  by_contra hno
  have hb := balanced_of_no_witness c hno
  obtain ⟨k,t,S,_,htr,h⟩ := exists_minimalObstruction hr hn c hb
  obtain ⟨p,rep⟩ := hline k
  apply h.not_line_representation hb (h.two_le_parameter hr hb htr) htr p
  exact ⟨fun x _ => rep.distinct x (mem_univ _),
    fun x _ y _ => rep.adj x (mem_univ _) y (mem_univ _)⟩

omit [Fintype L] in
/-- A single color class of average degree at most r suffices when it is the
line graph of a loopless multigraph. -/
theorem missing_of_sparse_line_representation [Fintype V] (hr : 3 ≤ r)
    (hn : Fintype.card V = r^2+1) (c : Sym2 V → Fin r) (k : Fin r)
    (hsparse : 2*(colorGraph c k).edgeFinset.card ≤ r*Fintype.card V)
    (hline : ∃ p : V → Sym2 L, LineRepresentation (colorGraph c k) univ p) :
    ∃ (S : Finset V) (j : Fin r), S.card = r+1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u,v) ≠ j := by
  classical
  by_contra hno
  have hb := balanced_of_no_witness c hno
  let G := colorGraph c k
  obtain ⟨v,hv⟩ : ∃ v, r < G.degree v := by
    by_contra! bounded
    exact hno (missing_of_bounded_color_degree r hr hn c k bounded)
  obtain ⟨x,hx⟩ : ∃ x, G.degree x < r := by
    by_contra! high
    have hs := sum_lt_sum (s:=univ) (fun x _ => high x) ⟨v,mem_univ _,hv⟩
    simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,G.sum_degrees_eq_twice_card_edges] at hs
    exact hs.not_ge (by simpa only [G,Nat.mul_comm (Fintype.card V) r] using hsparse)
  have many : (r-1)*r+1 ≤ (Gᶜ.neighborFinset x).card := by
    rw [card_neighborFinset_eq_degree,degree_compl,hn,pow_two,Nat.sub_mul,Nat.one_mul]
    have rr : r ≤ r*r := by simpa using Nat.mul_le_mul_right r (show 1 ≤ r by omega)
    omega
  obtain ⟨W,hW,hw⟩ := exists_subset_card_eq many
  obtain ⟨I,hI,ind⟩ : ∃ I ⊆ W, G.IsNIndepSet ((r-1)+1) I := by
    by_contra! noInd
    obtain ⟨t,T,ht,_,h⟩ := minimalObstruction_of_failure (c:=c) (k:=k) hw noInd
    obtain ⟨p,rep⟩ := hline
    apply h.not_line_representation hb (h.two_le_parameter hr hb (by omega)) (by omega) p
    exact ⟨fun y _ => rep.distinct y (mem_univ _),
      fun y _ z _ => rep.adj y (mem_univ _) z (mem_univ _)⟩
  have hnon (y : V) (hy : y ∈ I) : Gᶜ.Adj x y :=
    (Gᶜ.mem_neighborFinset ..).mp (hW (hI hy))
  have hxI : x ∉ I := fun hi => (hnon x hi).ne rfl
  have hind := independent_insert_of_nonadjacent G ind.isIndepSet x (fun y hy => (hnon y hy).2)
  exact hno ⟨insert x I,k,by rw [card_insert_of_notMem hxI,ind.card_eq]; omega,
    fun _ hu _ hv huv he => hind hu hv huv ⟨huv,he⟩⟩

end Erdos617
