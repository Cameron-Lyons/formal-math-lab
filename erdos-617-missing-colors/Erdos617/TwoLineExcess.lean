module

public import Erdos617.GoodSquareBlocks
public import Erdos617.TwoLineCapacity
public import Erdos617.ExteriorPairCounts

@[expose] public section

namespace Erdos617

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ} {c : Sym2 V → Fin r}

omit [Fintype V] [DecidableEq V] in
private theorem redecide_filter {S : Finset V} {p : V → Prop} {a b : DecidablePred p} {n : ℕ}
    (h : (@Finset.filter V p a S).card≤n) : (@Finset.filter V p b S).card≤n := by
  have eq : @Finset.filter V p a S = @Finset.filter V p b S := @filter_congr_decidable _ S p a b
  rwa [←eq]

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
/-- A good foreign color on the complement of two intersecting full lines
costs strictly more than the refined Turán minimum plus three quarters of r. -/
theorem two_line_good_color_excess (hr : 100000≤r) (hb : Balanced c) {i j k : Fin r}
    (ki : k≠i) (kj : k≠j) (C D U : Finset V)
    (fullC : (colorGraph c i).IsNClique r C) (fullD : (colorGraph c j).IsNClique r D)
    (meet : (C∩D).card=1) (out : Disjoint U (C∪D)) (sz : U.card=(r-1)^2+1)
    (cap : rankOn (colorGraph c k) U≤r-1) (no : ∀ S⊆U, ¬(colorGraph c k).IsNClique r S) :
    (r-1)*(r-1).choose 2+2*(r-1)-1+(3*r)/4 < blockEdges (colorGraph c k) U := by
  classical
  by_contra! budget
  let g := (3*r)/4
  let G := colorGraph c k
  obtain ⟨H,P,hU,ord,_,row,dis,apart,sep,sepH,deficit⟩ :=
    good_square_clean_blocks c k (by omega) hb U sz cap no (g:=g) (by dsimp [g]; omega) budget
  let X := C∪D
  have cx : C⊆X := subset_union_left
  have dx : D⊆X := subset_union_right
  have spokes {L : Finset V} {l : Fin r} (lk : k≠l) (full : (colorGraph c l).IsNClique r L)
      (ls : L⊆X) (v : V) (hv : v∈U) : (L.filter fun w => G.Adj w v).card≤2 := by
    have outside : v∉L := fun h => disjoint_left.mp out hv (ls h)
    have equal : (L.filter fun w => G.Adj w v) = L.filter (G.Adj v) := by
      ext w; simp only [mem_filter,adj_comm]
    rw [equal]
    exact other_clique_spokes_le_two hb lk full outside
  have clcap (S : Finset V) (sh : S⊆H) (cl : G.IsClique (S : Set V)) : S.card≤r-1 := by
    by_contra! large
    obtain ⟨T,sub,n⟩ := exists_subset_card_eq (s:=S) (show r≤S.card by omega)
    exact no T (sub.trans (sh.trans hU)) ⟨cl.subset sub,n⟩
  let pay (p : Fin (r-3)) := X.filter fun w => ∀ u∈P p,G.Adj w u
  have paid (p : Fin (r-3)) : (pay p).card≤r-(P p).card := by
    dsimp only [pay,X,G]
    apply redecide_filter
    exact complete_on_two_lines (by omega) hb (P p) C D (row p).2.1 (by have z := (row p).2.2.2; omega)
      (row p).2.2.1 (out.mono_left (row p).1)
      (fun v hv => spokes ki fullC cx v ((row p).1 hv)) (fun v hv => spokes kj fullD dx v ((row p).1 hv))
  let dead (L : Finset V) := L.filter fun w => G.IsClique (nonneighborRemainder G H {w} : Set V)
  have corePaid {L : Finset V} {l : Fin r} (lk : k≠l) (full : (colorGraph c l).IsNClique r L) (ls : L⊆X) :
      (dead L).card≤8 := by
    dsimp only [dead]
    apply redecide_filter
    exact (exterior_core_blocked_singletons G L H (by omega : 0<r) ord clcap (fun u hu => redecide_filter (spokes lk full ls u (hU hu)))).trans (by decide : 3≤8)
  let used := (univ.biUnion pay) ∪ (dead C ∪ dead D)
  let W := X \ used
  have wX : W⊆X := sdiff_subset
  have sizeUsed : used.card≤(r-3)+g+16 := by
    have one := (card_biUnion_le (s:=univ) (t:=pay)).trans (sum_le_sum fun p _ => paid p)
    have both := (card_union_le (dead C) (dead D)).trans (Nat.add_le_add (corePaid ki fullC cx) (corePaid kj fullD dx))
    exact (card_union_le ..).trans (Nat.add_le_add (one.trans deficit) both)
  have sizeX : X.card=2*r-1 := by
    have count := card_union_add_card_inter C D
    rw [meet,fullC.card_eq,fullD.card_eq] at count
    change (C∪D).card=2*r-1
    omega
  have many : 2*r-1≤r-3+g+16+(W∩C).card+(W∩D).card := by
    have cu : X⊆used∪W := by
      intro w hw
      by_cases h : w∈used
      · exact mem_union_left _ h
      · exact mem_union_right _ (mem_sdiff.mpr ⟨hw,h⟩)
    have est := (card_le_card cu).trans (card_union_le ..)
    have dc := card_union_le (W∩C) (W∩D)
    rw [←inter_union_distrib_left,inter_eq_left.mpr wX] at dc
    omega
  have limit {L : Finset V} {l : Fin r} (lk : k≠l) (full : (colorGraph c l).IsNClique r L)
      (ls : L⊆X) (dd : dead L⊆dead C∪dead D) :
      (W∩L).card*(W∩L).card≤(W∩L).card+16*(r-3)+64 := by
    let A := W∩L
    have asub : A⊆L := inter_subset_right
    have ow : Disjoint A U := out.symm.mono_left (asub.trans ls)
    have sp (u : V) (hu : u∈U) : (A.filter fun w => G.Adj w u).card≤2 :=
      (card_le_card (filter_subset_filter _ asub)).trans (spokes lk full ls u hu)
    have uncore (w : V) (hw : w∈A) : ¬G.IsClique (nonneighborRemainder G H {w} : Set V) := by
      intro stuck
      exact (mem_sdiff.mp (mem_inter.mp hw).1).2 (mem_union_right _ (dd (mem_filter.mpr ⟨asub hw,stuck⟩)))
    have unrow (p : Fin (r-3)) (w : V) (hw : w∈A) : (nonneighborRemainder G (P p) {w}).Nonempty := by
      by_contra! empty
      have all (v : V) (hv : v∈P p) : G.Adj w v := by
        by_contra non
        have mem : v∈nonneighborRemainder G (P p) {w} := mem_nonneighborRemainder _ |>.mpr ⟨hv,by simpa using non⟩
        simp [empty] at mem
      have ppaid : w∈pay p := mem_filter.mpr ⟨ls (asub hw),all⟩
      exact (mem_sdiff.mp (mem_inter.mp hw).1).2 (mem_union_left _ (mem_biUnion.mpr ⟨p,mem_univ _,ppaid⟩))
    apply line_unassigned_pair_capacity (by omega) hb H P dis apart sep sepH A
      (fun _ hx _ hy hxy e => lk (e.2.symm.trans (full.isClique (asub hx) (asub hy) hxy).2))
      (ow.mono_right hU) (fun p => ow.mono_right (row p).1)
    · exact fun p => redecide_filter ((exterior_row_blocked_pairs G A (P p) (row p).2.1 (fun u hu => redecide_filter (sp u ((row p).1 hu))) (unrow p)).trans (by decide : 8≤16))
    · exact redecide_filter ((exterior_core_blocked_pairs G A H (by omega : 0<r) ord clcap (fun u hu => redecide_filter (sp u (hU hu))) uncore).trans (by decide : 32≤64))
  exact two_line_capacity_numeric hr (by dsimp [g]; omega) many
    (limit ki fullC cx subset_union_left) (limit kj fullD dx subset_union_right)

end Erdos617
