module

public import Erdos617.LocalPaletteEnergy
public import Mathlib.Combinatorics.Hall.Finite

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] {r t : ℕ}

/-- Monochromatic cliques in distinct colors through a common vertex.
The indexed sets are the cliques with the common vertex removed. -/
structure CliqueBouquet (c : Sym2 V → Fin r) (k : Fin r) (t : ℕ) (x : V)
    (T : Finset (Fin r)) (P : Fin r → Finset V) : Prop where
  foreign : ∀ j ∈ T, j ≠ k
  rows : ∀ j ∈ T, x ∉ P j ∧ (colorGraph c j).IsNClique t (insert x (P j))
  disjoint : (T : Set (Fin r)).PairwiseDisjoint P

variable {d : Sym2 V → Fin r} {k : Fin r} {x y : V} {T : Finset (Fin r)} {P : Fin r → Finset V}

/-- A nonneighbor of the common vertex has an obstruction-color neighbor
in every petal other than the petal containing it. -/
theorem CliqueBouquet.hits_petal (h : CliqueBouquet d k t x T P)
    (free : (colorGraph d k).IndepSetFree (t+1))
    (hxy : y≠x) (hn : ¬(colorGraph d k).Adj y x)
    {j : Fin r} (hj : j∈T) (hy : y∉P j) :
    ∃ z∈P j, (colorGraph d k).Adj y z := by
  classical
  obtain ⟨_,row⟩ := h.rows j hj
  let B := insert x (P j)
  have hind : (colorGraph d k).IsIndepSet (B : Set V) := by
    intro a ha b hb hab hadj
    exact h.foreign j hj ((row.isClique ha hb hab).2.symm.trans hadj.2)
  have hout : y∉B := fun h => (mem_insert.mp h).elim hxy hy
  by_contra! miss
  apply free (insert y B)
  refine ⟨independent_insert_of_nonadjacent _ hind y ?_,?_⟩
  · intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact hn
    · exact miss z hz
  · rw [card_insert_of_notMem hout,show B.card=t from row.card_eq]

/-- Counting disjoint petals makes the neighbors in them distinct. -/
theorem CliqueBouquet.neighbor_count (h : CliqueBouquet d k t x T P)
    (free : (colorGraph d k).IndepSetFree (t+1))
    (hxy : y≠x) (hn : ¬(colorGraph d k).Adj y x) :
    T.card ≤ ((T.biUnion P).filter ((colorGraph d k).Adj y)).card +
      (if y∈T.biUnion P then 1 else 0) := by
  classical
  let U := T.filter fun j => y∉P j
  let R (j : Fin r) := (P j).filter ((colorGraph d k).Adj y)
  have per (j : Fin r) (hj : j∈U) : 1 ≤ (R j).card := by
    obtain ⟨hjT,hy⟩ := mem_filter.mp hj
    obtain ⟨z,hz,ha⟩ := h.hits_petal free hxy hn hjT hy
    exact card_pos.mpr ⟨z,mem_filter.mpr ⟨hz,ha⟩⟩
  have dis : (U : Set (Fin r)).PairwiseDisjoint R := fun i hi j hj hij =>
    (h.disjoint (mem_filter.mp hi).1 (mem_filter.mp hj).1 hij).mono (filter_subset ..) (filter_subset ..)
  have size := sum_le_sum per
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,←card_biUnion dis] at size
  have incl : U.biUnion R ⊆ (T.biUnion P).filter ((colorGraph d k).Adj y) := by
    intro z hz
    obtain ⟨j,hj,hz⟩ := mem_biUnion.mp hz
    exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨j,(mem_filter.mp hj).1,(mem_filter.mp hz).1⟩,(mem_filter.mp hz).2⟩
  have supply := size.trans (card_le_card incl)
  have split := card_filter_add_card_filter_not (s:=T) (fun j => y∈P j)
  have left : (T.filter fun j => y∈P j).card ≤ (if y∈T.biUnion P then 1 else 0) := by
    split <;> rename_i present
    · apply card_le_one.mpr
      intro a ha b hb
      by_contra hne
      exact disjoint_left.mp (h.disjoint (mem_filter.mp ha).1 (mem_filter.mp hb).1 hne)
        (mem_filter.mp ha).2 (mem_filter.mp hb).2
    · have empty : T.filter (fun j => y∈P j) = ∅ :=
        eq_empty_iff_forall_notMem.mpr (fun j hj => present (mem_biUnion.mpr
          ⟨j,(mem_filter.mp hj).1,(mem_filter.mp hj).2⟩))
      simp [empty]
  change _+U.card=T.card at split
  omega

/-- Given attained cliques at one vertex, a small total size deficit there
forces many disjoint petals of full size. -/
private theorem bouquet_of_deficit (_hr : 3 ≤ r) (ht : 4 ≤ t) (htr : t<r)
    (d : Sym2 V → Fin r) (k : Fin r) (x : V) (Q : Fin r → Finset V)
    (contains : ∀ j, x∈Q j) (clique : ∀ j, (colorGraph d j).IsClique (Q j : Set V))
    (cap : ∀ j≠k, (Q j).card ≤ t)
    (deficit : (∑ j∈univ.erase k, (t-(Q j).card)) ≤ t-4) :
    ∃ T : Finset (Fin r), r-t+3 ≤ T.card ∧ CliqueBouquet d k t x T (fun j => (Q j).erase x) := by
  classical
  let F := univ.erase k
  let T := F.filter (fun j => (Q j).card=t)
  let P (j : Fin r) := (Q j).erase x
  have subset : T⊆F := filter_subset ..
  have hF : F.card = r-1 := by simp [F]
  have per (j : Fin r) (hj : j∈F \ T) : 1 ≤ t-(Q j).card := by
    obtain ⟨hjF,hn⟩ := mem_sdiff.mp hj
    have neq : (Q j).card ≠t := fun eq => hn (mem_filter.mpr ⟨hjF,eq⟩)
    have ub := cap j (mem_erase.mp hjF).1
    omega
  have size := (sum_le_sum per).trans (sum_le_sum_of_subset (f:=fun j => t-(Q j).card) sdiff_subset)
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,card_sdiff_of_subset subset,hF] at size
  change (∑ j∈F, (t-(Q j).card)) ≤ t-4 at deficit
  have Ts := card_le_card subset
  rw [hF] at Ts
  refine ⟨T,by omega,fun j hj => (mem_erase.mp (mem_filter.mp hj).1).1,?_,?_⟩
  · intro j hj
    refine ⟨notMem_erase x (Q j),?_⟩
    rw [show insert x (P j)=Q j from insert_erase (contains j)]
    exact ⟨clique j,(mem_filter.mp hj).2⟩
  · intro i hi j hj hij
    exact disjoint_left.mpr (fun y hy hz => hij (
      ((clique i (contains i) (mem_erase.mp hy).2 (mem_erase.mp hy).1.symm).2).symm.trans
        (clique j (contains j) (mem_erase.mp hz).2 (mem_erase.mp hz).1.symm).2))

/-- Hall's condition between any two full petals. All neighbors here are in
the obstruction color. A deficient neighborhood together with the rest of
the second petal and the center would be an independent set of size t+1. -/
theorem CliqueBouquet.hall (h : CliqueBouquet d k t x T P)
    (free : (colorGraph d k).IndepSetFree (t+1)) {i j : Fin r} (hi : i∈T)
    (hj : j∈T) (hne : i≠j) (A : Finset V) (hA : A⊆P i) :
    A.card ≤ ((P j).filter (fun z => ∃ a∈A, (colorGraph d k).Adj a z)).card := by
  classical
  let G := colorGraph d k
  let N := (P j).filter (fun z => ∃ a∈A, G.Adj a z)
  let B := P j \ N
  have row {z : Fin r} (hz : z∈T) : G.IsIndepSet (insert x (P z) : Finset V) := by
    intro a ha b hb hab hadj
    exact h.foreign z hz (((h.rows z hz).2.isClique ha hb hab).2.symm.trans hadj.2)
  have dis := (h.disjoint hi hj hne).mono hA (sdiff_subset (s:=P j) (t:=N))
  have ax : x∉A := fun hx => (h.rows i hi).1 (hA hx)
  have bx : x∉B := fun hx => (h.rows j hj).1 (mem_sdiff.mp hx).1
  have ind : G.IsIndepSet (A ∪ insert x B : Finset V) := by
    intro a ha b hb hab he
    rcases mem_union.mp ha with ha | ha <;> rcases mem_union.mp hb with hb | hb
    · exact row hi (mem_insert_of_mem (hA ha)) (mem_insert_of_mem (hA hb)) hab he
    · rcases mem_insert.mp hb with eq | hb
      · exact row hi (mem_insert_of_mem (hA ha)) (mem_insert.mpr (Or.inl eq)) hab he
      · exact (mem_sdiff.mp hb).2 (mem_filter.mpr ⟨(mem_sdiff.mp hb).1,a,ha,he⟩)
    · rcases mem_insert.mp ha with eq | ha
      · exact row hi (mem_insert.mpr (Or.inl eq)) (mem_insert_of_mem (hA hb)) hab he
      · exact (mem_sdiff.mp ha).2 (mem_filter.mpr ⟨(mem_sdiff.mp ha).1,b,hb,he.symm⟩)
    · have incl : insert x B ⊆ insert x (P j) := insert_subset_insert _ sdiff_subset
      exact row hj (incl ha) (incl hb) hab he
  have cap : (A ∪ insert x B).card ≤ t := by
    by_contra! high
    obtain ⟨D,hD,hc⟩ := exists_subset_card_eq (Nat.succ_le_of_lt high)
    exact free D ⟨ind.mono hD,hc⟩
  have disx : Disjoint A (insert x B) := disjoint_left.mpr (fun z hz hz' =>
    (mem_insert.mp hz').elim (fun eq => ax (eq ▸ hz)) (disjoint_left.mp dis hz))
  rw [card_union_of_disjoint disx,card_insert_of_notMem bx] at cap
  have rc := (h.rows j hj).2.card_eq
  rw [card_insert_of_notMem (h.rows j hj).1] at rc
  have ncard : B.card+N.card=(P j).card := card_sdiff_add_card_eq_card (filter_subset ..)
  change A.card ≤ N.card
  omega

/-- Between two full petals there is a matching saturating both. -/
theorem CliqueBouquet.perfect_matching (h : CliqueBouquet d k t x T P)
    (free : (colorGraph d k).IndepSetFree (t+1)) {i j : Fin r} (hi : i ∈ T)
    (hj : j ∈ T) (hne : i≠j) :
    ∃ f : P i ≃ P j, ∀ a, (colorGraph d k).Adj a.val (f a).val := by
  classical
  let E (a : P i) := (P j).filter ((colorGraph d k).Adj a.val)
  have hall (U : Finset (P i)) : U.card ≤ (U.biUnion E).card := by
    let incl := Function.Embedding.subtype (·∈P i)
    let A := U.map incl
    have sub : A⊆P i := fun _ hz => U.property_of_mem_map_subtype hz
    have eq : U.biUnion E = (P j).filter (fun z => ∃ a∈A, (colorGraph d k).Adj a z) := by
      ext z
      constructor
      · intro hz
        obtain ⟨a,ha,hadj⟩ := mem_biUnion.mp hz
        exact mem_filter.mpr ⟨(mem_filter.mp hadj).1,a.val,mem_map_of_mem incl ha,(mem_filter.mp hadj).2⟩
      · intro hz
        obtain ⟨hzj,a,ha,hadj⟩ := mem_filter.mp hz
        obtain ⟨u,hu,rfl⟩ := mem_map.mp ha
        exact mem_biUnion.mpr ⟨u,hu,mem_filter.mpr ⟨hzj,hadj⟩⟩
    rw [eq,← card_map (f:=incl)]
    exact h.hall free hi hj hne A sub
  obtain ⟨g,hg,hm⟩ := (all_card_le_biUnion_card_iff_existsInjective' E).mp hall
  let f (a : P i) : P j := ⟨g a, (mem_filter.mp (hm a)).1⟩
  have inj : Function.Injective f := fun _ _ eq => hg (congrArg Subtype.val eq)
  have sizes : (P i).card=(P j).card := by
    have c₁ := (h.rows i hi).2.card_eq
    have c₂ := (h.rows j hj).2.card_eq
    rw [card_insert_of_notMem (h.rows i hi).1] at c₁
    rw [card_insert_of_notMem (h.rows j hj).1] at c₂
    omega
  have bij := (Fintype.bijective_iff_injective_and_card f).mpr ⟨inj,by simpa using sizes⟩
  exact ⟨Equiv.ofBijective f bij, fun a => (mem_filter.mp (hm a)).2⟩

/-- Any obstruction has a vertex where one clique per color covers all but
2t−3 vertices. At least r−t+3 of the other colors achieve full size t there.
Their disjoint petals satisfy the matching and neighborhood bounds above. -/
theorem MinimalObstruction.exists_clique_bouquet {c : Sym2 V → Fin r} {S : Finset V}
    (h : MinimalObstruction c k t S) (hr : 3≤r) (hb : Balanced c) (htr : t<r) :
    let d := fun e : Sym2 S => c (Sym2.map Subtype.val e)
    ∃ (x : S) (Q : Fin r → Finset S) (T : Finset (Fin r)),
      (∀ j, x∈Q j ∧ (colorGraph d j).IsNClique (pointClique (colorGraph d j) x) (Q j)) ∧
      (univ.biUnion Q)ᶜ.card ≤ 2*t-3 ∧ r-t+3 ≤ T.card ∧
      CliqueBouquet d k t x T (fun j => (Q j).erase x) := by
  classical
  intro d
  obtain ⟨x,hd⟩ := h.exists_local_clique_deficit hr hb htr
  choose Q contains cl using (fun j => exists_pointClique (colorGraph d j) x)
  have ⟨_,corecap,cap⟩ := h.point_clique_caps hb htr
  let F := (univ : Finset (Fin r)).erase k
  have hc (j : Fin r) : (Q j).card=pointClique (colorGraph d j) x := (cl j).card_eq
  change r-1-pointClique (colorGraph d k) x + (∑ j∈F,(t-pointClique (colorGraph d j) x)) ≤ t-4 at hd
  simp_rw [← hc] at hd
  have hcap (j : Fin r) (hj : j≠k) : (Q j).card≤t := (hc j).le.trans (cap j hj x)
  obtain ⟨_,_,_,_,_,_,half,_,two,_⟩ := h.exists_nested_product_obstruction hr hb htr
  obtain ⟨T,hT,hB⟩ := bouquet_of_deficit hr (by omega) htr d k x Q contains (fun j => (cl j).isClique)
    hcap (by change (∑ j∈F,(t-(Q j).card)) ≤ t-4; omega)
  refine ⟨x,Q,T,fun j => ⟨contains j,cl j⟩,?_,hT,hB⟩
  let R (j : Fin r) := (Q j).erase x
  have dis : ((univ : Finset (Fin r)) : Set (Fin r)).PairwiseDisjoint R := by
    intro i _ j _ hij
    exact disjoint_left.mpr (fun y hy hz => hij ((((cl i).isClique
      (contains i) (mem_erase.mp hy).2 (mem_erase.mp hy).1.symm).2).symm.trans
      ((cl j).isClique (contains j) (mem_erase.mp hz).2 (mem_erase.mp hz).1.symm).2))
  have cover : univ.biUnion Q=insert x (univ.biUnion R) := by
    ext y
    by_cases he : y=x
    · subst y
      exact iff_of_true (mem_biUnion.mpr ⟨k,mem_univ _,contains k⟩) (mem_insert_self ..)
    · simp [R,he]
  have out : x ∉ univ.biUnion R := by simp [R]
  have counts := sum_congr (s₁:=univ) rfl (fun j _ => card_erase_add_one (contains j))
  change (∑ j : Fin r, ((R j).card+1)) = ∑ j, (Q j).card at counts
  simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at counts
  have partition := card_add_card_compl (univ.biUnion Q)
  have countU : (univ.biUnion Q).card = (∑ j, (R j).card)+1 := by
    rw [cover,card_insert_of_notMem out,card_biUnion dis]
  rw [countU] at partition
  rw [Fintype.card_coe,h.card_eq] at partition
  have sizes := sum_congr (s₁:=F) rfl (fun j hj => Nat.sub_add_cancel (hcap j (mem_erase.mp hj).1))
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id] at sizes
  have fsize : F.card=r-1 := by simp [F]
  rw [fsize] at sizes
  have cut := sum_erase_add univ (fun j => (Q j).card) (mem_univ k)
  change (∑ j∈F,(Q j).card)+(Q k).card=∑ j,(Q j).card at cut
  have full := Nat.sub_add_cancel ((hc k).le.trans (corecap x))
  have prod : (r-1)*t+t=t*r := by rw [←Nat.succ_mul,show (r-1).succ=r by omega,Nat.mul_comm]
  omega

end Erdos617
