import Erdos617.ColorCounts
import Erdos617.IndependentSets

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ} {c : Sym2 V → Fin r} {k : Fin r}

omit [Fintype V] in
/-- A clique of order r-b has at most b outside vertices that are joined to
all but q of its vertices whenever the missing spokes and outside pairs
cannot account for the other r−1 colors. -/
theorem near_neighbors_of_large_clique (hb : Balanced c) {b q : ℕ}
    (few : (b+1)*q+(b+1).choose 2 < r-1) (C W : Finset V)
    (size : C.card+b=r) (cl : (colorGraph c k).IsClique (C : Set V)) (apart : Disjoint C W)
    (miss : ∀ w∈W,(C.filter fun x => ¬(colorGraph c k).Adj w x).card≤q) : W.card≤b := by
  classical
  by_contra! many
  obtain ⟨Y,sub,n⟩ := exists_subset_card_eq (s:=W) (Nat.succ_le_of_lt many)
  have dis := apart.mono_right sub
  have order : (C∪Y).card=r+1 := by rw [card_union_of_disjoint dis,n]; omega
  let f (e : Sym2 Y) := c (e.map Subtype.val)
  let inner := ((⊤ : SimpleGraph Y).edgeFinset).image f
  let spoke (w : V) := (C.filter fun z => ¬(colorGraph c k).Adj w z).image (fun z => c s(w,z))
  have cover : univ.erase k ⊆ (Y.biUnion spoke) ∪ inner := by
    intro j hj
    have jk := (mem_erase.mp hj).1
    have cross {w z : V} (hw : w∈Y) (hz : z∈C) (col : c s(w,z)=j) : j∈Y.biUnion spoke :=
      mem_biUnion.mpr ⟨w,hw,mem_image.mpr ⟨z,mem_filter.mpr ⟨hz,fun e => jk (col.symm.trans e.2)⟩,col⟩⟩
    obtain ⟨a,ha,z,hz,ne,col⟩ := hb (C∪Y) order j
    rcases mem_union.mp ha with ac|ay <;> rcases mem_union.mp hz with zc|zy
    · exact (jk (col.symm.trans (cl ac zc ne).2)).elim
    · exact mem_union_left _ (cross zy ac (by rwa [Sym2.eq_swap]))
    · exact mem_union_left _ (cross ay zc col)
    · let u : Y := ⟨a,ay⟩
      let v : Y := ⟨z,zy⟩
      exact mem_union_right _ (mem_image.mpr ⟨s(u,v),mem_edgeFinset.mpr
        (show u≠v from fun e => ne (congrArg Subtype.val e)),col⟩)
  have per (w : V) (hw : w∈Y) : (spoke w).card ≤ q := card_image_le.trans (miss w (sub hw))
  have sums := card_biUnion_le.trans (sum_le_sum per)
  rw [sum_const,nsmul_eq_mul,Nat.cast_id,n] at sums
  have inc : inner.card ≤ (b+1).choose 2 := by
    apply card_image_le.trans
    rw [card_edgeFinset_top_eq_card_choose_two,Fintype.card_coe,n]
  have total := (card_le_card cover).trans ((card_union_le ..).trans (Nat.add_le_add sums inc))
  simp only [card_erase_of_mem (mem_univ k),card_univ,Fintype.card_fin] at total
  exact few.not_ge total

omit [Fintype V] in
/-- If a clique has order r-b, adjoining b+1 of its common neighbors exposes
all r−1 foreign colors on the pairs of those new vertices. -/
theorem common_neighbors_of_large_clique {b : ℕ} (hb : Balanced c)
    (few : (b+1).choose 2 < r-1) (C W : Finset V)
    (size : C.card+b=r) (cl : (colorGraph c k).IsClique (C : Set V)) (apart : Disjoint C W)
    (all : ∀ w∈W, ∀ x∈C, (colorGraph c k).Adj w x) : W.card≤b := by
  classical
  apply near_neighbors_of_large_clique hb (q:=0) (by simpa using few) C W size cl apart
  intro w hw
  simpa only [Nat.le_zero,card_eq_zero,filter_eq_empty_iff] using
    (show ∀ x∈C, ¬¬(colorGraph c k).Adj w x from fun x hx => not_not.mpr (all w hw x hx))

/-- An induced disjoint union of r monochromatic cliques cannot occur on a
subset of a balanced counterexample if the rows are all this close to full.
An outside vertex must be joined in that color to an entire row. -/
theorem no_induced_large_clique_partition (hn : Fintype.card V=r^2+1) (hb : Balanced c)
    {U : Finset V} (P : Fin r → Finset V) (cover : univ.biUnion P=U)
    (dis : Pairwise fun i j => Disjoint (P i) (P j))
    (cl : ∀ i,(colorGraph c k).IsClique (P i : Set V))
    (separate : ∀ i j, i≠j → ∀ x∈P i, ∀ y∈P j, ¬(colorGraph c k).Adj x y)
    (size : ∀ i,(P i).card≤r) (cap : ∀ i,(r-(P i).card+1).choose 2 < r-1) : False := by
  classical
  let G := colorGraph c k
  let W (i : Fin r) := Uᶜ.filter fun w => ∀ x∈P i,G.Adj w x
  have inside (i : Fin r) : P i ⊆ U := cover ▸ subset_biUnion_of_mem P (mem_univ i)
  have paid (i : Fin r) : (W i).card ≤ r-(P i).card := by
    apply common_neighbors_of_large_clique hb (cap i) (P i) (W i) (Nat.add_sub_of_le (size i)) (cl i)
    · exact Finset.disjoint_left.mpr fun x hx hw => (mem_compl.mp (mem_filter.mp hw).1) (inside i hx)
    · exact fun w hw => (mem_filter.mp hw).2
  have outside : Uᶜ ⊆ univ.biUnion W := by
    intro x hx
    by_contra missing
    have each (i : Fin r) : ∃ y∈P i, ¬G.Adj x y := by
      by_contra! all
      exact missing (mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨hx,all⟩⟩)
    choose y row noedge using each
    have inj : Function.Injective y := by
      intro i j same
      by_contra ne
      exact Finset.disjoint_left.mp (dis ne) (row i) (same ▸ row j)
    let I := univ.image y
    have ind : G.IsIndepSet (I : Set V) := by
      intro a ha b hB ne
      obtain ⟨i,_,rfl⟩ := mem_image.mp ha
      obtain ⟨j,_,rfl⟩ := mem_image.mp hB
      exact separate i j (fun h => ne (congrArg y h)) _ (row i) _ (row j)
    have xi : x∉I := by
      intro h
      obtain ⟨j,_,eq⟩ := mem_image.mp h
      exact mem_compl.mp hx (eq ▸ inside j (row j))
    have bound := independent_insert_of_nonadjacent G ind x (by
      intro z hz
      obtain ⟨j,_,rfl⟩ := mem_image.mp hz
      exact noedge j)
    have ord : (insert x I).card=r+1 := by simp [card_insert_of_notMem xi,I,card_image_of_injective _ inj]
    obtain ⟨u,hu,v,hv,ne,edge⟩ := hb _ ord k
    exact bound hu hv ne ⟨ne,edge⟩
  have outcard := (card_le_card outside).trans card_biUnion_le
  have count := card_biUnion (s:=univ) (t:=P) (fun _ _ _ _ ne => dis ne)
  rw [cover] at count
  have total := sum_le_sum (s:=univ) fun i _ => paid i
  have payments := sum_congr (s₁:=univ) rfl fun i _ => Nat.sub_add_cancel (size i)
  rw [sum_add_distrib,sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin,Nat.cast_id,←pow_two] at payments
  have sz : Uᶜ.card+U.card=r^2+1 := (card_compl_add_card U).trans hn
  omega

/-- Transfer the partition on an induced vertex type to the ambient coloring. -/
theorem no_square_turan_partition {U : Finset V} (hr : 5≤r) (hn : Fintype.card V=r^2+1)
    (hb : Balanced c) (P : Fin r → Finset U) (cover : univ.biUnion P=univ)
    (dis : Pairwise fun i j => Disjoint (P i) (P j))
    (cl : ∀ i, (colorGraph (fun e : Sym2 U => c (e.map Subtype.val)) k).IsClique (P i : Set U) ∧
      ((P i).card=r-2 ∨ (P i).card=r-1))
    (sep : ∀ i j, i≠j → ∀ x∈P i, ∀ y∈P j, ¬(colorGraph (fun e : Sym2 U => c (e.map Subtype.val)) k).Adj x y) :
    False := by
  classical
  let f := Function.Embedding.subtype (·∈U)
  let R (i : Fin r) := (P i).map f
  have equiv {a b : U} : (colorGraph c k).Adj a.val b.val ↔
      (colorGraph (fun e : Sym2 U => c (e.map Subtype.val)) k).Adj a b :=
    ⟨fun e => ⟨fun h => e.1 (congrArg Subtype.val h),e.2⟩,fun e => ⟨fun h => e.1 (Subtype.ext h),e.2⟩⟩
  apply no_induced_large_clique_partition hn hb (k:=k) (U:=U) R
  · ext w
    constructor
    · intro hw
      obtain ⟨i,_,hwi⟩ := mem_biUnion.mp hw
      exact (P i).property_of_mem_map_subtype hwi
    · intro hw
      have p : (⟨w,hw⟩ : U) ∈ univ.biUnion P := cover ▸ mem_univ _
      obtain ⟨i,_,hm⟩ := mem_biUnion.mp p
      exact mem_biUnion.mpr ⟨i,mem_univ _,mem_map_of_mem f hm⟩
  · exact fun _ _ ne => (Finset.disjoint_map f).mpr (dis ne)
  · intro i a ha b hB ne
    obtain ⟨y,hy,rfl⟩ := mem_map.mp ha
    obtain ⟨z,hz,rfl⟩ := mem_map.mp hB
    exact equiv.mpr ((cl i).1 hy hz (fun eq => ne (congrArg f eq)))
  · intro i j ij x hx y hy
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
    obtain ⟨b,hB,rfl⟩ := mem_map.mp hy
    exact fun e => sep i j ij _ ha _ hB (equiv.mp e)
  · intro i
    have h := (cl i).2
    simp only [R,card_map]
    omega
  · intro i
    have h := (cl i).2
    simp only [R,card_map]
    have q : r-(P i).card+1=3 ∨ r-(P i).card+1=2 := by omega
    rcases q with e|e <;> rw [e] <;> norm_num [Nat.choose] <;> omega

end Erdos617
