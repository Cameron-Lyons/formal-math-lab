import Erdos617.FixedWitnessCapacity
import Erdos617.OddPrivateRows

namespace Erdos617

open Finset SimpleGraph
open scoped Classical

private theorem filter_bound {V : Type*} {S : Finset V} {p : V → Prop} {a b : DecidablePred p} {n : ℕ}
    (h : (@Finset.filter V p a S).card≤n) : (@Finset.filter V p b S).card≤n := by
  have e := @filter_congr_decidable _ S p a b
  rwa [←e]

/-- A pair of full lines cannot extend this rank partition. After excluding
the vertices that hit J or fill a cleaned row, each remaining ordered pair on
one line must fill a row jointly. Each row can account for at most eight. -/
theorem two_line_witness_capacity {V : Type*} [Fintype V] [DecidableEq V]
    {r n b : ℕ} {c : Sym2 V → Fin r} {i j k : Fin r}
    (hr : 145≤r) (large : 64*(b+1)+4≤r) (hb : Balanced c) (ki : k≠i) (kj : k≠j)
    (C D U J : Finset V) (P O : Fin n → Finset V)
    (fullC : (colorGraph c i).IsNClique r C) (fullD : (colorGraph c j).IsNClique r D)
    (meet : (C∩D).card=1) (out : Disjoint U (C∪D))
    (jU : J⊆U) (indJ : (colorGraph c k).IsIndepSet (J : Set V))
    (size : n+J.card=r-1) (smallJ : J.card≤2*(b+1))
    (row : ∀ a,O a⊆U ∧ (colorGraph c k).IsClique (O a : Set V) ∧ (O a).card≤r-1 ∧ P a⊆O a ∧ (P a).Nonempty)
    (dis : Pairwise fun a d => Disjoint (P a) (P d)) (apart : ∀ a,Disjoint (P a) J)
    (sep : ∀ a d,a≠d → ∀ u∈P a,∀ v∈P d,¬(colorGraph c k).Adj u v)
    (sepJ : ∀ a,∀ u∈P a,∀ v∈J,¬(colorGraph c k).Adj u v)
    (budget : (∑ a, if (O a).card=r-1 ∧ 2*((O a).card-(P a).card)+1<r-1 then 1 else 4)≤r+24*(b+1)) : False := by
  classical
  let G := colorGraph c k
  let X := C∪D
  have cx : C⊆X := subset_union_left
  have dx : D⊆X := subset_union_right
  have spokes {L : Finset V} {l : Fin r} (lk : k≠l) (full : (colorGraph c l).IsNClique r L)
      (ls : L⊆X) (v : V) (hv : v∈U) : (L.filter fun w => G.Adj w v).card≤2 := by
    have eq : (L.filter fun w => G.Adj w v)=L.filter (G.Adj v) := by ext; simp only [mem_filter,adj_comm]
    rw [eq]
    exact other_clique_spokes_le_two hb lk full (fun h => disjoint_left.mp out hv (ls h))
  have pu (a : Fin n) : P a⊆U := (row a).2.2.2.1.trans (row a).1
  let pay (a : Fin n) := X.filter fun w => ∀ z∈P a,G.Adj w z
  have paid (a : Fin n) : (pay a).card≤
      if (O a).card=r-1 ∧ 2*((O a).card-(P a).card)+1<r-1 then 1 else 4 := by
    dsimp only [pay,X,G]
    apply filter_bound
    exact cleaned_row_two_line_capacity (by omega) hb (O a) (P a) C D (row a).2.2.2.1 (row a).2.2.2.2
      (row a).2.1 (out.mono_left (row a).1)
      (fun u hu => filter_bound (spokes ki fullC cx u (pu a hu)))
      (fun u hu => filter_bound (spokes kj fullD dx u (pu a hu)))
  let neigh (u : V) := X.filter fun w => G.Adj w u
  have near (u : V) (hu : u∈J) : (neigh u).card≤4 := by
    dsimp only [neigh,X]
    rw [filter_union]
    exact (card_union_le ..).trans (Nat.add_le_add (spokes ki fullC cx u (jU hu)) (spokes kj fullD dx u (jU hu)))
  let used := (univ.biUnion pay)∪J.biUnion neigh
  let W := X \ used
  have wX : W⊆X := sdiff_subset
  have sizeUsed : used.card≤r+32*(b+1) := by
    have one := (card_biUnion_le (s:=univ) (t:=pay)).trans (sum_le_sum fun a _ => paid a)
    have two := (card_biUnion_le (s:=J) (t:=neigh)).trans (sum_le_sum near)
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at two
    have total := card_union_le (univ.biUnion pay) (J.biUnion neigh)
    change used.card≤_ at total
    omega
  have count : X.card=2*r-1 := by
    have eq := card_union_add_card_inter C D
    rw [meet,fullC.card_eq,fullD.card_eq] at eq
    change (C∪D).card=2*r-1
    omega
  have many : 2*r-1≤r+32*(b+1)+(W∩C).card+(W∩D).card := by
    have cover : X⊆used∪W := by
      intro z hz
      by_cases h : z∈used
      · exact mem_union_left _ h
      · exact mem_union_right _ (mem_sdiff.mpr ⟨hz,h⟩)
    have total := (card_le_card cover).trans (card_union_le ..)
    have dc := card_union_le (W∩C) (W∩D)
    rw [←inter_union_distrib_left,inter_eq_left.mpr wX] at dc
    omega
  have line {l : Fin r} (L : Finset V) (lk : k≠l) (full : (colorGraph c l).IsNClique r L) (ls : L⊆X) :
      (W∩L).card*(W∩L).card≤(W∩L).card+8*n := by
    let A := W∩L
    have sub : A⊆L := inter_subset_right
    have off : Disjoint A U := out.symm.mono_left (sub.trans ls)
    apply fixed_witness_line_capacity hb J P size (by omega) indJ (fun a => (row a).2.2.2.2) dis apart sep sepJ A
      (fun _ hx _ hy h e => lk (e.2.symm.trans (full.isClique (sub hx) (sub hy) h).2))
      (fun a => off.mono_right (pu a)) (off.mono_right jU)
    · intro w hw u hu e
      apply (mem_sdiff.mp (mem_inter.mp hw).1).2
      exact mem_union_right _ (mem_biUnion.mpr ⟨u,hu,mem_filter.mpr ⟨ls (sub hw),e⟩⟩)
    · intro a u hu
      apply (card_le_card (filter_subset_filter _ sub)).trans
      exact filter_bound (spokes lk full ls u (pu a hu))
    · intro a w hw
      by_contra! empty
      have all (v : V) (hv : v∈P a) : G.Adj w v := by
        by_contra non
        have hmem : v∈nonneighborRemainder G (P a) {w} := (mem_nonneighborRemainder _).mpr ⟨hv,by simpa using non⟩
        change nonneighborRemainder G (P a) {w}=∅ at empty
        rw [empty] at hmem
        exact notMem_empty _ hmem
      exact (mem_sdiff.mp (mem_inter.mp hw).1).2 (mem_union_left _ (mem_biUnion.mpr
        ⟨a,mem_univ _,mem_filter.mpr ⟨ls (sub hw),all⟩⟩))
  have few (a : ℕ) (ha : a≤r) (pairs : a*a≤a+8*n) : 4*a<r := by
    by_contra! big
    have sq := Nat.mul_le_mul big big
    have grow := Nat.mul_le_mul_right r (show 145≤r by omega)
    have nr : n≤r := by omega
    nlinarith only [pairs,sq,grow,ha,nr,show 0<r by omega]
  have ca := few _ ((card_le_card (inter_subset_right (s₁:=W) (s₂:=C))).trans_eq fullC.card_eq) (line C ki fullC cx)
  have da := few _ ((card_le_card (inter_subset_right (s₁:=W) (s₂:=D))).trans_eq fullD.card_eq) (line D kj fullD dx)
  omega

end Erdos617
