import Erdos617.GlobalCliqueEnergy

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- For two different cliques of maximum order, a missing edge in their
union has their entire intersection as common neighbors. -/
theorem max_clique_inter_le_codegree {s b : ℕ} (cap : ∀ x, pointClique G x≤s)
    (codeg : ∀ x y : V, x≠y → ¬G.Adj x y → (G.neighborFinset x∩G.neighborFinset y).card≤b)
    {A B : Finset V} (ha : G.IsNClique s A) (hb : G.IsNClique s B) (hne : A≠B) :
    (A∩B).card≤b := by
  classical
  have nonsub : ¬B⊆A := fun inc => hne ((eq_of_subset_of_card_le inc
    (by rw [ha.card_eq,hb.card_eq])).symm)
  obtain ⟨w,hw,hwA⟩ := not_subset.mp nonsub
  have bad : ¬G.IsClique (↑(A∪B) : Set V) := by
    intro cl
    have greater := card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨subset_union_left,fun eq => hwA (eq ▸ mem_union_right A hw)⟩ : A ⊂ A∪B)
    have le := (card_le_pointClique G (A∪B) cl w (mem_union_right A hw)).trans (cap w)
    rw [ha.card_eq] at greater
    omega
  have nonedge : ∃ u∈A, ∃ v∈B, u≠v ∧ ¬G.Adj u v := by
    by_contra! all
    apply bad
    intro u hu v hv ne
    rcases mem_union.mp hu with hu|hu <;> rcases mem_union.mp hv with hv|hv
    · exact ha.isClique hu hv ne
    · exact all u hu v hv ne
    · exact (all v hv u hu ne.symm).symm
    · exact hb.isClique hu hv ne
  obtain ⟨u,hu,v,hv,ne,no⟩ := nonedge
  have huB : u∉B := fun hh => no (hb.isClique hh hv ne)
  have hvA : v∉A := fun hh => no (ha.isClique hu hh ne)
  apply (card_le_card ?_).trans (codeg u v ne no)
  intro z hz
  obtain ⟨za,zb⟩ := mem_inter.mp hz
  exact mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr (ha.isClique hu za (fun eq => huB (eq ▸ zb))),
    (G.mem_neighborFinset _ _).mpr (hb.isClique hv zb (fun eq => hvA (eq ▸ za)))⟩

/-- A common point of two cliques is adjacent to every other vertex in
their union. -/
theorem clique_union_le_degree {A B : Finset V} (ha : G.IsClique (A : Set V))
    (hb : G.IsClique (B : Set V)) {x : V} (hx : x∈A∩B) : (A∪B).card ≤ G.degree x+1 := by
  have inside : x∈A∪B := mem_union_left _ (mem_inter.mp hx).1
  have inc : (A∪B).erase x ⊆ G.neighborFinset x := by
    intro z hz
    obtain ⟨ne,hm⟩ := mem_erase.mp hz
    apply (G.mem_neighborFinset ..).mpr
    exact (mem_union.mp hm).elim (fun hh => ha (mem_inter.mp hx).1 hh ne.symm)
      (fun hh => hb (mem_inter.mp hx).2 hh ne.symm)
  have le := card_le_card inc
  rw [card_neighborFinset_eq_degree] at le
  have eq := card_erase_add_one inside
  omega

/-- On 33 vertices the degree, codegree and local clique bounds force four
disjoint 7-cliques. Each of the five remaining vertices belongs to a 6-clique. -/
theorem eight_clique_rows (hn : Fintype.card V=33) (deg : ∀ x,G.degree x≤9)
    (codeg : ∀ x y : V, x≠y → ¬G.Adj x y → (G.neighborFinset x∩G.neighborFinset y).card≤2)
    (cap : ∀ x,pointClique G x ≤ 7) (cost : (∑ x,(7-pointClique G x)) ≤ 5) :
    ∃ Q : Finset (Finset V), Q.card=4 ∧
      (∀ A∈Q,G.IsNClique 7 A) ∧ (Q : Set (Finset V)).PairwiseDisjoint id ∧
      (Q.biUnion id)ᶜ.card=5 ∧ ∀ x∉Q.biUnion id, pointClique G x=6 := by
  classical
  let Q := univ.filter (G.IsNClique 7)
  let X := (Q.biUnion id)ᶜ
  have cl (A : Finset V) (ha : A∈Q) : G.IsNClique 7 A := (mem_filter.mp ha).2
  have dis : (Q : Set (Finset V)).PairwiseDisjoint id := by
    intro A ha B hb ne
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have cu := clique_union_le_degree G (cl A ha).isClique (cl B hb).isClique (mem_inter.mpr ⟨hx,hy⟩)
    have ci := max_clique_inter_le_codegree G cap codeg (cl A ha) (cl B hb) ne
    have eq := card_union_add_card_inter A B
    rw [(cl A ha).card_eq,(cl B hb).card_eq] at eq
    have := deg x
    omega
  have count := card_biUnion dis
  change (Q.biUnion id).card=∑ A∈Q,A.card at count
  rw [sum_congr rfl (fun A hA => (cl A hA).card_eq),sum_const,nsmul_eq_mul,Nat.cast_id] at count
  have sizes : X.card+(Q.biUnion id).card=33 := by simp [X,hn]
  have low (x : V) (hx : x∈X) : 1≤7-pointClique G x := by
    by_contra! small
    have top : pointClique G x=7 := by have := cap x; omega
    obtain ⟨A,ha,hA⟩ := exists_pointClique G x
    rw [top] at hA
    exact (mem_compl.mp hx) (mem_biUnion.mpr ⟨A,mem_filter.mpr ⟨mem_univ _,hA⟩,ha⟩)
  have per := sum_le_sum low
  have total := sum_le_sum_of_subset (f:=fun x => 7-pointClique G x) (subset_univ X)
  rw [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at per
  have nX : X.card=5 := by omega
  refine ⟨Q,by omega,cl,dis,nX,?_⟩
  intro x hx
  have hx' : x∈X := mem_compl.mpr hx
  have eq : (∑ _x∈X,1) = ∑ x∈X,(7-pointClique G x) := by simp; omega
  have hit := (sum_eq_sum_iff_of_le low).mp eq x hx'
  omega

end Erdos617
