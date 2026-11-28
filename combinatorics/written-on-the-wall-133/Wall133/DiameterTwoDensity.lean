module

public import Wall133.RegularAll
public import Wall133.IndependentContacts

@[expose] public section

namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- If all vertices are within two steps of v, independent neighbors of
a nonneighbor w can be assigned to distinct neighbors of v. -/
theorem indep_le_degree_of_two_step_center (h4 : NoFourCycle G) {v w : V}
    (reach : ∀ y, y≠v → ¬G.Adj v y → ∃ x,G.Adj v x ∧ G.Adj y x)
    (vw : ¬G.Adj v w) : G.indepNeighborsCard w ≤ G.degree v := by
  classical
  let H := G.induce (G.neighborSet w)
  obtain ⟨I,hI⟩ := exists_isNIndepSet_indepNum (G:=H)
  let val (i : I) : V := i.val.val
  have edge (i : I) : G.Adj w (val i) := i.val.property
  have choose (i : I) : ∃ x : G.neighborSet v, val i=x.val ∨ G.Adj (val i) x.val := by
    by_cases h : G.Adj v (val i)
    · exact ⟨⟨_,h⟩,Or.inl rfl⟩
    obtain ⟨x,vx,ix⟩ := reach (val i) (fun e => vw (e ▸ (edge i).symm)) h
    exact ⟨⟨x,vx⟩,Or.inr ix⟩
  choose f hf using choose
  have inj : Function.Injective f := by
    intro i j eq
    by_contra ne
    have distinct : val i≠val j := fun h => ne (Subtype.ext (Subtype.ext h))
    have ind : ¬G.Adj (val i) (val j) := hI.isIndepSet i.property j.property
      (fun h => ne (Subtype.ext h))
    have centerNe : w≠(f i).val := fun e => vw (e ▸ (f i).property)
    have jh := hf j
    rw [←eq] at jh
    rcases hf i with ai|ai <;> rcases jh with aj|aj
    · exact distinct (ai.trans aj.symm)
    · exact ind (ai ▸ aj.symm)
    · exact ind (aj ▸ ai)
    · exact distinct (h4 centerNe (edge i) ai.symm (edge j) aj.symm)
  have le := Fintype.card_le_of_injective f inj
  rw [Fintype.card_coe,G.card_neighborSet_eq_degree,hI.card_eq] at le
  exact le

/-- Vertices outside the closed two-step neighborhood are unavailable
in the count of independent neighbors along edges from v. -/
theorem neighbor_independence_sum_add_far (h4 : NoFourCycle G) (v : V) (T : Finset V)
    (far : ∀ x∈T, x≠v ∧ ¬G.Adj v x ∧ ∀ w, G.Adj v w → ¬G.Adj w x) :
    (∑ w∈G.neighborFinset v,G.indepNeighborsCard w) + T.card < Fintype.card V := by
  classical
  let N := G.neighborFinset v
  let B := (insert v N)ᶜ \ T
  have mem {w} : w∈N ↔ G.Adj v w := G.mem_neighborFinset _ _
  have outside {x} : x∈B ↔ (x≠v ∧ ¬G.Adj v x) ∧ x∉T := by simp [B,N]
  have vertex : v∉N := fun h => (mem.mp h).ne rfl
  have estimate (w) (hw : w∈N) : G.indepNeighborsCard w ≤ (Finset.bipartiteAbove G.Adj B w).card+1 := by
    apply (eligible_neighbors_card h4 (mem.mp hw).symm _ _).1
    intro u
    simp only [Finset.mem_bipartiteAbove,outside]
    have avoid : G.Adj w u → u∉T := fun adj inT => (far u inT).2.2 w (mem.mp hw) adj
    tauto
  have budget : ∑ w∈N,(Finset.bipartiteAbove G.Adj B w).card ≤ B.card := by
    rw [Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    calc
      _ ≤ ∑ _x∈B, 1 := Finset.sum_le_sum (fun x hx => Finset.card_le_one.mpr (by
        intro y hy z hz
        obtain ⟨ny,ay⟩ := Finset.mem_filter.mp hy
        obtain ⟨nz,az⟩ := Finset.mem_filter.mp hz
        exact h4 (outside.mp hx).1.1.symm (mem.mp ny) ay.symm (mem.mp nz) az.symm))
      _ = _ := by simp
  have total := Finset.sum_le_sum estimate
  rw [Finset.sum_add_distrib] at total
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at total
  change ∑ i∈N,G.indepNeighborsCard i ≤ (∑ i∈N,(Finset.bipartiteAbove G.Adj B i).card)+N.card at total
  have subset : T ⊆ (insert v N)ᶜ := by
    intro x hx
    exact Finset.mem_compl.mpr (fun h => (Finset.mem_insert.mp h).elim (far x hx).1
      (fun nx => (far x hx).2.1 (mem.mp nx)))
  have bc := Finset.card_sdiff_add_card_eq_card subset
  change B.card+T.card=((insert v N)ᶜ).card at bc
  rw [Finset.card_compl,Finset.card_insert_of_notMem vertex] at bc
  have nc : N.card+1 ≤ Fintype.card V := by
    simpa [Finset.card_insert_of_notMem vertex] using (Finset.card_le_univ (insert v N))
  change (∑ w∈N,G.indepNeighborsCard w)+T.card < Fintype.card V
  omega

/-- In a four-cycle-free graph the sum of neighborhood independence over
the neighbors of any v is strictly less than the order of the graph. -/
theorem neighbor_independence_sum_lt_order (h4 : NoFourCycle G) (v : V) :
    ∑ w∈G.neighborFinset v,G.indepNeighborsCard w < Fintype.card V := by
  simpa using neighbor_independence_sum_add_far h4 v ∅ (by simp)

/-- The degree of any vertex of eccentricity at most two bounds the floor
of the average neighborhood independence. -/
theorem floor_le_degree_of_two_step_center [Nonempty V] (h4 : NoFourCycle G) (v : V)
    (reach : ∀ y, y≠v → ¬G.Adj v y → ∃ x,G.Adj v x ∧ G.Adj y x) :
    ⌊l G⌋₊ ≤ G.degree v := by
  classical
  let N := G.neighborFinset v
  have low : ∑ w∈Nᶜ,G.indepNeighborsCard w ≤ ∑ _w∈Nᶜ,G.degree v := by
    apply Finset.sum_le_sum
    intro w hw
    exact indep_le_degree_of_two_step_center h4 reach
      (fun h => Finset.mem_compl.mp hw ((G.mem_neighborFinset _ _).2 h))
  have small : ∑ w∈N,G.indepNeighborsCard w < Fintype.card V := neighbor_independence_sum_lt_order h4 v
  have join := Finset.sum_add_sum_compl N (fun w => G.indepNeighborsCard w)
  simp only [Finset.sum_const,nsmul_eq_mul] at low
  change (∑ w∈Nᶜ,G.indepNeighborsCard w) ≤ (Nᶜ : Finset V).card * G.degree v at low
  have bound := Nat.mul_le_mul_right (G.degree v) (Finset.card_le_univ (Nᶜ : Finset V))
  by_contra! large
  have real := Nat.floor_le (a:=l G) (div_nonneg
    (Finset.sum_nonneg (fun w _ => Nat.cast_nonneg (G.indepNeighborsCard w))) (Nat.cast_nonneg _))
  have demand := le_average_iff_sum_indep.mp real
  have bigger := Nat.mul_le_mul_right (Fintype.card V) large
  rw [Nat.succ_mul,Nat.mul_comm (G.degree v)] at bigger
  omega

/-- In a graph of diameter at most two, every vertex meets the degree
lower bound coming from the average neighborhood independence. -/
theorem floor_le_min_degree_of_diameter_two [Nonempty V] (hc : G.Connected)
    (h4 : NoFourCycle G) (diam : G.diam≤2) (v : V) : ⌊l G⌋₊ ≤ G.degree v := by
  apply floor_le_degree_of_two_step_center h4
  intro y yv vy
  have finite := (G.connected_iff_ediam_ne_top.mp hc)
  have upper := (G.dist_le_diam (u:=v) (v:=y) finite).trans diam
  have positive := hc.pos_dist_of_ne yv.symm
  have one : G.dist v y ≠ 1 := fun h => vy (dist_eq_one_iff_adj.mp h)
  have two : G.dist v y=2 := by omega
  have ext : G.edist v y=2 := by rw [←(hc v y).coe_dist_eq_edist,two]; rfl
  obtain ⟨x,hx⟩ := (edist_eq_two_iff.mp ext).2.2
  exact ⟨x,(G.mem_commonNeighbors.mp hx).1,(G.mem_commonNeighbors.mp hx).2⟩

end Wall133
