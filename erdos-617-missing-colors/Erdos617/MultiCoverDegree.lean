import Erdos617.OddBags

namespace Erdos617

open Finset SimpleGraph

variable {V ι : Type*} [DecidableEq V] [Fintype ι] [DecidableEq ι]

/-- Every row of an exact q-fold monochromatic cover by qt+1 rows contains
a vertex of induced degree at most r+t−2 in the covering color. -/
theorem exists_low_vertex_of_qfold_cover {r : ℕ} (c : Sym2 V → Fin r) (hb : Balanced c)
    (k : Fin r) (S : Finset V) (B : ι → Finset V) {q t : ℕ} (hr : 2 ≤ r)
    (hq : 2 ≤ q) (_ht : 2 ≤ t) (hn : Fintype.card ι = q*t+1) (hS : S.card=t*r+1)
    (hsub : ∀ i, B i ⊆ S) (hcl : ∀ i, (colorGraph c k).IsClique (B i : Set V))
    (hc : ∀ x ∈ S, (univ.filter fun i => x ∈ B i).card=q) (i : ι) :
    ∃ x ∈ B i, (S.filter ((colorGraph c k).Adj x)).card ≤ r+t-2 := by
  classical
  let G := colorGraph c k
  let A := B i
  let X := S \ A
  let K := univ.erase i
  have hK : K.card=q*t := by simp [K,hn]
  have nX : X.card+A.card = S.card := card_sdiff_add_card_eq_card (hsub _)
  -- Sum the union cardinalities by counting each outside vertex in its q other rows.
  have per (j : ι) : (A ∪ B j).card=A.card+(X.filter fun x => x∈B j).card := by
    have hu : A ∪ X.filter (fun x => x∈B j) = A ∪ B j := by
      ext x
      simp only [X,mem_union,mem_filter,mem_sdiff]
      have hy := @hsub j x
      tauto
    have hd : Disjoint A (X.filter fun x => x∈B j) :=
      disjoint_sdiff.mono_right (filter_subset ..)
    rw [←hu,card_union_of_disjoint hd]
  have xsum : (∑ j ∈ K, (X.filter fun x => x∈B j).card) = X.card*q := by
    have sum : (∑ j ∈ K, (X.filter fun x => x∈B j).card) =
        ∑ x ∈ X, (K.filter fun j => x∈B j).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
    have count (x : V) (hx : x ∈ X) : (K.filter fun j => x ∈ B j).card=q := by
      have hh : i ∉ univ.filter fun j => x ∈ B j := fun h => (mem_sdiff.mp hx).2 (mem_filter.mp h).2
      dsimp [K]
      rw [filter_erase,erase_eq_of_notMem hh,hc x (mem_sdiff.mp hx).1]
    simp only [sum,sum_congr rfl count,sum_const,nsmul_eq_mul,Nat.cast_id]
  have unions : (∑ j ∈ K,(A ∪ B j).card) = (q*t)*A.card + X.card*q := by
    simp_rw [per,sum_add_distrib]
    simp [hK,xsum]
  -- Each ordered foreign pair is counted once for each row through its second endpoint.
  let T (x : V) := (S.erase x).filter fun y => ¬ G.Adj x y
  let R := (A ×ˢ S).filter fun p => p.2 ∈ T p.1
  let P (j : ι) := R.filter fun p => p.2 ∈ B j
  have spec {x y : V} : (x,y) ∈ R ↔ x∈A ∧ y∈S ∧ x≠y ∧ ¬G.Adj x y := by
    simp [R,T,and_assoc,ne_comm]
    tauto
  have other {p : V × V} (hp : p ∈ R) : p.2∉A := by
    obtain ⟨x,y⟩ := p
    obtain ⟨hx,_,hne,ha⟩ := spec.mp hp
    exact fun hy => ha (hcl i hx hy hne)
  have sumP : (∑ j ∈ K,(P j).card) = R.card*q := by
    have sum : (∑ j ∈ K,(P j).card) = ∑ p ∈ R,(K.filter fun j => p.2∈B j).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
    have count (p : V × V) (hp : p ∈ R) : (K.filter fun j => p.2∈B j).card=q := by
      have hh : i ∉ univ.filter fun j => p.2∈B j := fun h => other hp (mem_filter.mp h).2
      dsimp [K]
      rw [filter_erase,erase_eq_of_notMem hh,hc p.2 (mem_product.mp (mem_filter.mp hp).1).2]
    simp only [sum,sum_congr rfl count,sum_const,nsmul_eq_mul,Nat.cast_id]
  have bound (j : ι) (_ : j∈K) : (r-1)*(A∪B j).card ≤ (r-1)*r+(P j).card := by
    apply foreign_pair_budget c hb k _ _
    intro x hx y hy hxy hcol
    have ha : ¬(x∈A ∧ y∈A) := fun h => hcol (hcl i h.1 h.2 hxy).2
    have hb' : ¬(x∈B j ∧ y∈B j) := fun h => hcol (hcl j h.1 h.2 hxy).2
    have cross : (x∈A ∧ y∈B j) ∨ (y∈A ∧ x∈B j) := by
      simp only [mem_union] at hx hy
      tauto
    rcases cross with ⟨hx,hy⟩ | ⟨hy,hx⟩
    · exact Or.inl (mem_filter.mpr ⟨spec.mpr ⟨hx,hsub j hy,hxy,fun e => hcol e.2⟩,hy⟩)
    · exact Or.inr (mem_filter.mpr ⟨spec.mpr ⟨hy,hsub j hx,hxy.symm,fun e => hcol e.symm.2⟩,hx⟩)
  have budget := sum_le_sum bound
  simp only [←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id,hK,unions,sumP] at budget
  have cardR : R.card=∑ x∈A,(T x).card := by
    dsimp [R]
    rw [card_filter,sum_product]
    apply sum_congr rfl
    intro x _
    rw [sum_boole]
    change (S.filter fun y => y ∈ T x).card = (T x).card
    rw [filter_mem_eq_inter,inter_eq_right.mpr ((filter_subset ..).trans (erase_subset ..))]
  have split (x : V) (hx : x∈A) : (T x).card+(S.filter (G.Adj x)).card+1=S.card := by
    have hh := card_filter_add_card_filter_not (s:=S.erase x) (G.Adj x)
    have no : x ∉ S.filter (G.Adj x) := fun he => (mem_filter.mp he).2.ne rfl
    rw [filter_erase,erase_eq_of_notMem no] at hh
    have size := card_erase_add_one (hsub i hx)
    change (S.filter (G.Adj x)).card + (T x).card = (S.erase x).card at hh
    omega
  by_contra! high
  have big (x : V) (hx : x∈A) : (T x).card+(r+t) ≤ S.card := by
    have hh := high x hx
    have he := split x hx
    change r+t-2 < (S.filter (G.Adj x)).card at hh
    omega
  have hh := sum_le_sum big
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id,←cardR] at hh
  have htotal := Nat.mul_le_mul_left q hh
  have hsize := congrArg (fun z => (r-1)*q*z) nX
  rw [hS] at hsize htotal
  have hr' : r-1+1=r := by omega
  have hcorr := congrArg (fun z => q*A.card*z) hr'
  have hcorr' := congrArg (fun z => q*t*A.card*z) hr'
  have positive := Nat.mul_pos (by omega : 0<q) (by omega : 0<r-1)
  nlinarith only [budget,htotal,hsize,hcorr,hcorr',positive]

end Erdos617
