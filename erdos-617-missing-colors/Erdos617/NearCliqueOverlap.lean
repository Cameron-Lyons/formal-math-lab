import Erdos617.OddBags

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] {r : ℕ} {c : Sym2 V → Fin r} {k : Fin r}

/-- Two monochromatic cliques of order r−1 in the same color are either nearly
identical or meet in at most one vertex. -/
theorem near_clique_overlap (hr : 6≤r) (hb : Balanced c) {A B : Finset V}
    (hA : (colorGraph c k).IsNClique (r-1) A) (hB : (colorGraph c k).IsNClique (r-1) B) :
    (A∩B).card≤1 ∨ (A\B).card≤1 := by
  classical
  by_contra! bad
  let q := (A∩B).card
  let p := (A\B).card
  have hs : p+q=r-1 := (card_sdiff_add_card_inter A B).trans hA.card_eq
  have hs' : (B\A).card+q=r-1 := by rw [← hB.card_eq,← card_sdiff_add_card_inter B A,inter_comm B A]
  have hu : (A∪B).card=q+p+p := by
    have := card_union_add_card_inter A B
    rw [hA.card_eq,hB.card_eq] at this
    omega
  have cap := foreign_pair_budget c hb k (A∪B) ((A\B) ×ˢ (B\A)) (by
    intro x hx y hy hxy he
    have l : ¬(x∈A ∧ y∈A) := fun h => he (hA.isClique h.1 h.2 hxy).2
    have m : ¬(x∈B ∧ y∈B) := fun h => he (hB.isClique h.1 h.2 hxy).2
    simp only [mem_union,mem_product,mem_sdiff] at *
    tauto)
  have rform : r=q+p+1 := by omega
  rw [hu,card_product,show (A\B).card=p by rfl,show (B\A).card=p by omega,
    ←hs,rform] at cap
  have hp : 2≤p := bad.2
  have hq : 2≤q := bad.1
  obtain ⟨a,ha⟩ := Nat.exists_eq_add_of_le hp
  obtain ⟨b,hb'⟩ := Nat.exists_eq_add_of_le hq
  rw [ha,hb'] at cap rform
  nlinarith only [cap,rform,hr,Nat.zero_le (a*b)]

/-- A monochromatic clique of order r−2 has at most two common neighbors
outside it. In particular three cliques of order r−1 cannot share this core. -/
theorem near_clique_common_neighbors (hr : 5≤r) (hb : Balanced c) {C : Finset V}
    (hC : (colorGraph c k).IsNClique (r-2) C) (W : Finset V)
    (apart : Disjoint W C) (edges : ∀ w∈W, ∀ x∈C, (colorGraph c k).Adj w x) :
    W.card≤2 := by
  classical
  by_contra! many
  obtain ⟨a,b,d,ha,hb',hd,hab,had,hbd⟩ := two_lt_card_iff.mp many
  let T : Finset V := {a,b,d}
  let P : Finset (V×V) := {(a,b),(a,d),(b,d)}
  have sub : T⊆W := by
    intro v hv
    simp only [T,mem_insert,mem_singleton] at hv
    rcases hv with rfl|rfl|rfl <;> assumption
  have cap := foreign_pair_budget c hb k (C∪T) P (by
    intro x hx y hy hxy ne
    have l : x∉C := by
      intro hxC
      rcases mem_union.mp hy with hyC | hyT
      · exact ne (hC.isClique hxC hyC hxy).2
      · exact ne (edges y (sub hyT) x hxC).symm.2
    have m : y∉C := by
      intro hyC
      rcases mem_union.mp hx with hxC | hxT
      · exact ne (hC.isClique hxC hyC hxy).2
      · exact ne (edges x (sub hxT) y hyC).2
    have hxT := (mem_union.mp hx).resolve_left l
    have hyT := (mem_union.mp hy).resolve_left m
    simp only [T,mem_insert,mem_singleton] at hxT hyT
    rcases hxT with rfl|rfl|rfl <;> rcases hyT with rfl|rfl|rfl <;> simp_all [P])
  have count : T.card=3 := by simp [T,hab,had,hbd]
  have pairs : P.card≤3 := card_le_three
  rw [card_union_of_disjoint (apart.symm.mono_right sub),hC.card_eq,count,
    show r-2+3=r+1 by omega,Nat.mul_add,Nat.mul_one] at cap
  omega

private theorem one_vertex_swap {A B : Finset V} (hc : A.card=B.card) (hne : A≠B)
    (one : (A \ B).card≤1) :
    ∃ a∈A, ∃ b∉A, b∈B ∧ (∀ x, x∈B ↔ x=b ∨ (x∈A ∧ x≠a)) := by
  classical
  have pos : 0<(A \ B).card := card_pos.mpr (sdiff_nonempty.mpr (fun h => hne (eq_of_subset_of_card_le h hc.ge)))
  have n : (A \ B).card=1 := by omega
  obtain ⟨a,ea⟩ := card_eq_one.mp n
  obtain ⟨b,eb⟩ := card_eq_one.mp ((card_sdiff_comm hc.symm).trans n)
  have fa (x : V) : x∈A ∧ x∉B ↔ x=a := by rw [←mem_sdiff,ea,mem_singleton]
  have fb (x : V) : x∈B ∧ x∉A ↔ x=b := by rw [←mem_sdiff,eb,mem_singleton]
  obtain ⟨ha,_⟩ := (fa a).mpr rfl
  obtain ⟨hb,nb⟩ := (fb b).mpr rfl
  refine ⟨a,ha,b,nb,hb,fun x => ?_⟩
  grind

/-- In the distinguished color of a minimal obstruction, a clique of order
r−1 has at most one distinct clique of the same size meeting it in two or
more vertices. -/
theorem MinimalObstruction.unique_near_clique_partner {t : ℕ} {S A B D : Finset V}
    (h : MinimalObstruction c k t S) (hr : 6≤r) (hb : Balanced c) (htr : t<r)
    (hAS : A⊆S) (hBS : B⊆S)
    (hA : (colorGraph c k).IsNClique (r-1) A) (hB : (colorGraph c k).IsNClique (r-1) B)
    (hD : (colorGraph c k).IsNClique (r-1) D) (hAB : A≠B) (hAD : A≠D)
    (bigh : 2≤(A∩B).card) (bigd : 2≤(A∩D).card) : B=D := by
  classical
  obtain ⟨a,ha,b,hbA,hbB,memB⟩ := one_vertex_swap (hA.card_eq.trans hB.card_eq.symm) hAB
    ((near_clique_overlap hr hb hA hB).resolve_left (by omega))
  obtain ⟨u,hu,v,hvA,hvD,memD⟩ := one_vertex_swap (hA.card_eq.trans hD.card_eq.symm) hAD
    ((near_clique_overlap hr hb hA hD).resolve_left (by omega))
  by_cases av : a=u
  · subst u
    by_cases bv : b=v
    · ext x
      simp only [memB,memD,bv]
    have core : (colorGraph c k).IsNClique (r-2) (A.erase a) :=
      ⟨hA.isClique.subset (erase_subset ..),by rw [card_erase_of_mem ha,hA.card_eq]; omega⟩
    let W : Finset V := {a,b,v}
    have ab : a≠b := by rintro rfl; exact hbA ha
    have au : a≠v := by rintro rfl; exact hvA ha
    have n : W.card=3 := by simp [W,ab,au,bv]
    have small := near_clique_common_neighbors (by omega : 5≤r) hb core W (by
      apply Finset.disjoint_left.mpr
      intro z hz he
      obtain ⟨ne,hA'⟩ := mem_erase.mp he
      simp only [W,mem_insert,mem_singleton] at hz
      grind) (by
      intro z hz y hy
      obtain ⟨ne,hyA⟩ := mem_erase.mp hy
      simp only [W,mem_insert,mem_singleton] at hz
      rcases hz with eq|eq|eq
      · subst z; exact hA.isClique ha hyA ne.symm
      · subst z; exact hB.isClique hbB ((memB y).mpr (Or.inr ⟨hyA,ne⟩)) (fun eq => hbA (eq ▸ hyA))
      · subst z; exact hD.isClique hvD ((memD y).mpr (Or.inr ⟨hyA,ne⟩)) (fun eq => hvA (eq ▸ hyA)))
    omega
  by_cases bv : b=v
  · subst v
    apply False.elim
    apply h.no_clique hb htr (insert b A) (insert_subset (hBS hbB) hAS)
    refine ⟨?_,by rw [card_insert_of_notMem hbA,hA.card_eq]; omega⟩
    rw [coe_insert]
    apply hA.isClique.insert
    intro y hy ne
    by_cases e : y=a
    · exact hD.isClique hvD ((memD y).mpr (Or.inr ⟨hy,e ▸ av⟩)) ne
    · exact hB.isClique hbB ((memB y).mpr (Or.inr ⟨hy,e⟩)) ne
  have common : (A.erase a).erase u ⊆ B∩D := by
    intro z hz
    obtain ⟨zu,za⟩ := mem_erase.mp hz
    obtain ⟨zne,hzA⟩ := mem_erase.mp za
    exact mem_inter.mpr ⟨(memB z).mpr (Or.inr ⟨hzA,zne⟩),(memD z).mpr (Or.inr ⟨hzA,zu⟩)⟩
  have many := card_le_card common
  rw [card_erase_of_mem (mem_erase.mpr ⟨Ne.symm av,hu⟩),card_erase_of_mem ha,hA.card_eq] at many
  have single := (near_clique_overlap hr hb hB hD).resolve_left (by omega)
  have bu : b≠u := fun eq => hbA (eq ▸ hu)
  have cut : ({b,u} : Finset V)⊆B \ D := by
    intro z hz
    simp only [mem_insert,mem_singleton] at hz
    rw [mem_sdiff,memB,memD]
    grind
  have pairs := card_le_card cut
  rw [card_pair bu] at pairs
  omega

end Erdos617
