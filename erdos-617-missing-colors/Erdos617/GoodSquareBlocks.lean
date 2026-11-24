import Erdos617.SquareLinearExcess
import Erdos617.DeletionRank

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] {r : ℕ}

/-- A near-minimum good color splits into a rank-two part and full rows of size r−1. -/
private theorem near_good_rank_partition
    (c : Sym2 V → Fin r) (k : Fin r) (hr : 6≤r) (hb : Balanced c)
    (U : Finset V) (sz : U.card=(r-1)^2+1) (cap : rankOn (colorGraph c k) U≤r-1)
    (no : ∀ A⊆U, ¬(colorGraph c k).IsNClique r A) {g : ℕ} (small : g<r-2)
    (budget : blockEdges (colorGraph c k) U≤(r-1)*(r-1).choose 2+2*(r-1)-1+g) :
    let G := colorGraph c k
    ∃ Q : Finset (Finset V), ∃ H∈Q, Q.biUnion id=U ∧
      (↑Q : Set (Finset V)).PairwiseDisjoint id ∧ (Q.erase H).card=r-3 ∧
      H.card=2*r-1 ∧ rankOn G H=2 ∧ (∀ A∈Q.erase H, G.IsNClique (r-1) A) ∧
      (inducedEdgeSet G U \ Q.biUnion (inducedEdgeSet G)).card≤g := by
  classical
  let G := colorGraph c k
  let s := r-1
  have sr : s+1=r := by dsimp [s]; omega
  have sU : U.card=s*s+1 := by simpa [s,pow_two] using sz
  change rankOn G U≤s at cap
  change blockEdges G U≤s*s.choose 2+2*s-1+g at budget
  obtain ⟨Q,hu,hd,hi,hs⟩ := exists_rank_partition G U
  let F := inducedEdgeSet G U \ Q.biUnion (inducedEdgeSet G)
  let D (A : Finset V) := blockEdges G A+(s.choose 2+1)*rankOn G A+(s-1)-s*A.card
  have ident (A : Finset V) (ha : A∈Q) :
      D A+s*A.card=blockEdges G A+(s.choose 2+1)*rankOn G A+(s-1) :=
    Nat.sub_add_cancel (rank_density G A (hi A ha) s)
  have total := sum_congr (s₁:=Q) rfl ident
  have cut := boundary_edge_count G U Q hu.le hd
  change F.card+(∑ A∈Q,blockEdges G A)=blockEdges G U at cut
  have count := card_biUnion hd
  simp only [id_eq,hu] at count
  simp only [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,Nat.cast_id,←count,hs] at total
  have lower (A : Finset V) (ha : A∈Q) : 1≤rankOn G A := (hi A ha).rank_pos
  have ones := sum_le_sum lower
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,hs] at ones
  have pc := ones.trans cap
  have ac := Nat.mul_le_mul_left (s.choose 2+1) cap
  have eqQ := congrArg ((s-1)*·) (Nat.sub_add_cancel pc)
  rw [Nat.mul_add,Nat.mul_comm (s-1) Q.card] at eqQ
  have numeric : s*U.card+s*s.choose 2+s=(s.choose 2+1)*s+(s-1)*s+2*(s*s.choose 2+s) := by
    have mulch := congrArg (s*·) (twice_choose_two s)
    have mp := congrArg (·*s) (show s-1+1=s by omega)
    rw [sU]
    nlinarith only [mulch,mp]
  have spos : 0<s := by omega
  have money : F.card+(∑ A∈Q,D A)+(s-1)*(s-Q.card)≤s-1+g := by omega
  have many : s≤Q.card+1 := by
    by_contra! low
    have mult := Nat.mul_le_mul_left (s-1) (show 2≤s-Q.card by omega)
    omega
  have inside (A : Finset V) (ha : A∈Q) : A⊆U := (biUnion_subset.mp hu.le) A ha
  have short (A : Finset V) (ha : A∈Q) (one : rankOn G A=1) : A.card≤s := by
    by_contra! big
    obtain ⟨B,sub,card⟩ := exists_subset_card_eq (show r≤A.card by omega)
    exact no B (sub.trans (inside A ha)) ⟨fun _ hx _ hy ne => rank_one_clique G one (sub hx) (sub hy) ne,card⟩
  have some : ∃ H∈Q,2≤rankOn G H := by
    by_contra! all
    have sum := sum_le_sum (fun A ha => short A ha (by have := lower A ha; have := all A ha; omega))
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id,←count] at sum
    have mult := Nat.mul_le_mul_right s pc
    omega
  obtain ⟨H,hh,large⟩ := some
  let R := Q.erase H
  have subsetR : R⊆Q := erase_subset ..
  have sizeR : R.card=Q.card-1 := card_erase_of_mem hh
  have posQ := card_pos.mpr ⟨H,hh⟩
  have lowR := sum_le_sum (s:=R) (fun A ha => lower A (subsetR ha))
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at lowR
  have split := sum_erase_add Q (rankOn G) hh
  change (∑ A∈R,rankOn G A)+rankOn G H=_ at split
  rw [hs] at split
  have qcard : Q.card+1=s := by omega
  have rk : rankOn G H=2 := by omega
  have one (A : Finset V) (ha : A∈R) : rankOn G A=1 := by
    symm
    apply (sum_eq_sum_iff_of_le (fun A hA => lower A (subsetR hA))).mp _ A ha
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one]
    omega
  have Hsmall := rank_two_clique_free_card_lt hb hr (k:=k) (A:=H)
    (fun C sub => no C (sub.trans (inside H hh))) (by change rankOn G H≤2; omega)
  have sumSizes := sum_erase_add Q card hh
  change (∑ A∈R,A.card)+H.card=_ at sumSizes
  rw [←count] at sumSizes
  have caps (A : Finset V) (ha : A∈R) : A.card≤s := short _ (subsetR ha) (one A ha)
  have sumCaps := sum_le_sum caps
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at sumCaps
  have rows : R.card+2=s := by omega
  have prod := congrArg (·*s) rows
  have twice : 2*r-1+1=2*r := Nat.sub_add_cancel (by omega)
  have bigH : H.card=2*r-1 := by nlinarith only [sumSizes,sumCaps,sU,sr,prod,Hsmall,twice]
  have full (A : Finset V) (ha : A∈R) : G.IsNClique (r-1) A := by
    refine ⟨rank_one_clique G (one _ ha), (sum_eq_sum_iff_of_le caps).mp ?_ A ha⟩
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id]
    nlinarith only [sumSizes,bigH,sU,sr,prod,Nat.sub_add_cancel (show 1≤2*r by omega)]
  refine ⟨Q,H,hh,hu,hd,by change R.card=r-3; omega,bigH,rk,full,?_⟩
  change F.card≤g
  rw [show s-Q.card=1 by omega,Nat.mul_one] at money
  omega

/-- Removing at most one endpoint per cross edge isolates all the rank-one rows
from each other and from the untouched rank-two block. -/
theorem good_square_clean_blocks_originals
    (c : Sym2 V → Fin r) (k : Fin r) (hr : 6≤r) (hb : Balanced c)
    (U : Finset V) (sz : U.card=(r-1)^2+1) (cap : rankOn (colorGraph c k) U≤r-1)
    (no : ∀ A⊆U, ¬(colorGraph c k).IsNClique r A) {g : ℕ} (small : g<r-2)
    (budget : blockEdges (colorGraph c k) U≤(r-1)*(r-1).choose 2+2*(r-1)-1+g) :
    let G := colorGraph c k
    ∃ H : Finset V, ∃ P O : Fin (r-3) → Finset V,
      H⊆U ∧ H.card=2*r-1 ∧ rankOn G H=2 ∧
      (∀ i, P i⊆U ∧ (P i).Nonempty ∧ G.IsClique (P i : Set V) ∧ (P i).card≤r-1) ∧
      Pairwise (fun i j => Disjoint (P i) (P j)) ∧ (∀ i, Disjoint (P i) H) ∧
      (∀ i j, i≠j → ∀ x∈P i, ∀ y∈P j, ¬G.Adj x y) ∧
      (∀ i, ∀ x∈P i, ∀ y∈H, ¬G.Adj x y) ∧
      (∑ i, (r-(P i).card)) ≤ r-3+g ∧
      (∀ i,O i⊆U ∧ G.IsNClique (r-1) (O i) ∧ P i⊆O i) ∧
      ∑ i,(r-1-(P i).card) ≤ g := by
  classical
  let G := colorGraph c k
  obtain ⟨Q,H,hh,hu,hd,nR,nH,rk,full,few⟩ := near_good_rank_partition c k hr hb U sz cap no small budget
  let R := Q.erase H
  let F := inducedEdgeSet G U \ Q.biUnion (inducedEdgeSet G)
  change F.card≤g at few
  have inside (A : Finset V) (ha : A∈Q) : A⊆U := (biUnion_subset.mp hu.le) A ha
  have outside (e : Sym2 V) (he : e∈F) : ∃ z : V, z∈e ∧ z∉H := by
    induction e using Sym2.inductionOn with | _ x y =>
      obtain ⟨ein,eout⟩ := mem_sdiff.mp he
      have pair := (mem_inducedEdgeSet G).mp ein
      by_cases h : x∈H
      · by_cases h' : y∈H
        · exact (eout (mem_biUnion.mpr ⟨H,hh,(mem_inducedEdgeSet G).mpr ⟨h,h',pair.2.2⟩⟩)).elim
        · exact ⟨y,by simp,h'⟩
      · exact ⟨x,by simp,h⟩
  choose f fm fo using (fun e : F => outside e.val e.prop)
  let D := univ.image f
  have dcap : D.card≤g := by
    have le : D.card≤(univ : Finset F).card := card_image_le
    simpa using le.trans (by simpa using few)
  have dH : Disjoint D H := by
    apply Finset.disjoint_left.mpr
    intro x hx
    obtain ⟨e,_,rfl⟩ := mem_image.mp hx
    exact fo e
  have cover {x y : V} (he : s(x,y)∈F) : x∈D ∨ y∈D := by
    let e : F := ⟨s(x,y),he⟩
    have del : f e∈D := mem_image_of_mem f (mem_univ e)
    rcases Sym2.mem_iff.mp (show f e∈s(x,y) from fm e) with eq | eq
    · exact Or.inl (eq ▸ del)
    · exact Or.inr (eq ▸ del)
  have unique {A B : Finset V} (ha : A∈Q) (hb' : B∈Q) {x : V} (hx : x∈A) (hx' : x∈B) : A=B :=
    by_contra (fun h => Finset.disjoint_left.mp (hd ha hb' h) hx hx')
  have cross {A B : Finset V} (ha : A∈Q) (hb' : B∈Q) (ne : A≠B) {x y : V} (hx : x∈A)
      (hy : y∈B) (e : G.Adj x y) : x∈D ∨ y∈D := by
    apply cover
    refine mem_sdiff.mpr ⟨(mem_inducedEdgeSet G).mpr ⟨inside _ ha hx,inside _ hb' hy,e⟩,?_⟩
    intro h
    obtain ⟨C,hc,edge⟩ := mem_biUnion.mp h
    obtain ⟨xc,yc,_⟩ := (mem_inducedEdgeSet G).mp edge
    exact ne ((unique ha hc hx xc).trans (unique hc hb' yc hy))
  let rep : Fin (r-3) ≃ R := (Fintype.equivFinOfCardEq ((Fintype.card_coe _).trans nR)).symm
  let B (i : Fin (r-3)) := (rep i).val
  let P (i : Fin (r-3)) := B i \ D
  let L (i : Fin (r-3)) := B i ∩ D
  have memR (i) : B i∈Q.erase H := (rep i).prop
  have memQ (i) : B i∈Q := (mem_erase.mp (memR i)).2
  have neq (i) : B i≠H := (mem_erase.mp (memR i)).1
  have diff {i j} (ij : i≠j) : B i≠B j := fun eq => ij (rep.injective (Subtype.ext eq))
  have nB (i) : (B i).card=r-1 := (full _ (memR i)).card_eq
  have split (i) : (P i).card+(L i).card=r-1 := (card_sdiff_add_card_inter _ _).trans (nB i)
  have subL (i) : L i⊆D := inter_subset_right
  have subP (i) : P i⊆B i := sdiff_subset
  have row (i) : P i⊆U ∧ (P i).Nonempty ∧ G.IsClique (P i : Set V) ∧ (P i).card≤r-1 := by
    have n := split i
    have loss := (card_le_card (subL i)).trans dcap
    refine ⟨(subP i).trans (inside _ (memQ i)),card_pos.mp (by omega),?_,by omega⟩
    exact fun _ hx _ hy ne => (full _ (memR i)).isClique (subP i hx) (subP i hy) ne
  have ld : (↑(univ : Finset (Fin (r-3))) : Set _).PairwiseDisjoint L :=
    fun i _ j _ ne => (hd (memQ i) (memQ j) (diff ne)).mono inter_subset_left inter_subset_left
  have lt := card_biUnion ld
  have lcap := card_le_card (biUnion_subset.mpr (fun i _ => subL i) : univ.biUnion L⊆D)
  rw [lt] at lcap
  have sum := sum_congr (s₁:=univ) rfl (fun i _ => (show r-(P i).card=1+(L i).card by have := split i; omega))
  simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at sum
  refine ⟨H,P,B,inside _ hh,nH,rk,row,(fun i j ne => (hd (memQ i) (memQ j) (diff ne)).mono (subP i) (subP j)),
    (fun i => (hd (memQ i) hh (neq i)).mono_left (subP i)),?_,?_,by omega,fun i => ⟨inside _ (memQ i),full _ (memR i),subP i⟩,?_⟩
  · intro i j ne x hx y hy e
    exact (cross (memQ i) (memQ j) (diff ne) (subP i hx) (subP j hy) e).elim (mem_sdiff.mp hx).2 (mem_sdiff.mp hy).2
  · intro i x hx y hy e
    exact (cross (memQ i) hh (neq i) (subP i hx) hy e).elim (mem_sdiff.mp hx).2 (fun yd => Finset.disjoint_left.mp dH yd hy)

  · have eq := sum_congr (s₁:=univ) rfl (fun i _ => (show r-1-(P i).card=(L i).card by have := split i; omega))
    omega

/-- Removing at most one endpoint per cross edge isolates all the rank-one rows
from each other and from the untouched rank-two block. -/
theorem good_square_clean_blocks
    (c : Sym2 V → Fin r) (k : Fin r) (hr : 6≤r) (hb : Balanced c)
    (U : Finset V) (sz : U.card=(r-1)^2+1) (cap : rankOn (colorGraph c k) U≤r-1)
    (no : ∀ A⊆U, ¬(colorGraph c k).IsNClique r A) {g : ℕ} (small : g<r-2)
    (budget : blockEdges (colorGraph c k) U≤(r-1)*(r-1).choose 2+2*(r-1)-1+g) :
    let G := colorGraph c k
    ∃ H : Finset V, ∃ P : Fin (r-3) → Finset V,
      H⊆U ∧ H.card=2*r-1 ∧ rankOn G H=2 ∧
      (∀ i, P i⊆U ∧ (P i).Nonempty ∧ G.IsClique (P i : Set V) ∧ (P i).card≤r-1) ∧
      Pairwise (fun i j => Disjoint (P i) (P j)) ∧ (∀ i, Disjoint (P i) H) ∧
      (∀ i j, i≠j → ∀ x∈P i, ∀ y∈P j, ¬G.Adj x y) ∧
      (∀ i, ∀ x∈P i, ∀ y∈H, ¬G.Adj x y) ∧
      ∑ i, (r-(P i).card) ≤ r-3+g := by
  obtain ⟨H,P,_,sub,ord,rk,row,dis,apart,sep,sepH,bound,_,_⟩ :=
    good_square_clean_blocks_originals c k hr hb U sz cap no small budget
  exact ⟨H,P,sub,ord,rk,row,dis,apart,sep,sepH,bound⟩

end Erdos617
