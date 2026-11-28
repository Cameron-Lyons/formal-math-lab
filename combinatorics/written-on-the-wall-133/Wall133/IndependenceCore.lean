module

public import Wall133.RegularAll
public import Wall133.NeighborhoodTriangles
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

@[expose] public section

/-!
# Peeling by neighborhood independence

Give an edge weight one if it is in a triangle and two otherwise.
In a four-cycle-free graph the weighted degree is twice the neighborhood
independence number. Restricting to an induced subgraph can only increase
the weight of each retained edge. These two facts let us peel vertices while
retaining the original independence average in the surviving subgraph.
-/
namespace Wall133
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

noncomputable def triangleWeight (G : SimpleGraph V) (x y : V) : ℕ := by
  classical
  exact if G.Adj x y then (if ∃ z,G.Adj x z ∧ G.Adj y z then 1 else 2) else 0

lemma weight_symm (x y : V) : triangleWeight G x y=triangleWeight G y x := by
  classical
  simp only [triangleWeight,G.adj_comm x y,and_comm (a := G.Adj x _)]

lemma weight_induce_le (s : Finset V) (x y : s) :
    triangleWeight G x.val y.val ≤ triangleWeight (G.induce (s : Set V)) x y := by
  classical
  unfold triangleWeight
  change (if G.Adj x.val y.val then _ else 0) ≤ (if G.Adj x.val y.val then _ else 0)
  by_cases he : G.Adj x.val y.val
  · simp only [ite_eq_left he]
    have lift : (∃ z:s, (G.induce (s:Set V)).Adj x z ∧ (G.induce (s:Set V)).Adj y z) →
        ∃ z,G.Adj x.val z ∧ G.Adj y.val z := fun ⟨z,hx,hy⟩ => ⟨z.val,hx,hy⟩
    split_ifs <;> first | decide | (expose_names; exact False.elim (‹¬_› (lift ‹_›)))
  · simp only [ite_eq_right he,le_refl]

theorem weight_of_triangle_edge {x y : V} (ha : G.Adj x y)
    (h : ∃ z,G.Adj x z ∧ G.Adj y z) : triangleWeight G x y = 1 := by simp [triangleWeight,ha,h]

theorem weighted_degree_eq_twice_indep [Fintype V] [DecidableRel G.Adj] (h4 : NoFourCycle G)
    (x : V) : (∑ y, triangleWeight G x y) = 2*G.indepNeighborsCard x := by
  classical
  let H := G.induce (G.neighborSet x)
  have eq (y : G.neighborSet x) : triangleWeight G x y.val + H.degree y = 2 := by
    have hxy : G.Adj x y.val := y.property
    by_cases ht : ∃ z,G.Adj x z ∧ G.Adj y.val z
    · obtain ⟨z,hxz,hyz⟩ := ht
      let w : G.neighborSet x := ⟨z,hxz⟩
      have h1 : H.degree y=1 := degree_eq_one_iff_existsUnique_adj.mpr
        ⟨w,hyz,fun u hu => neighborhood_adj_unique h4 x hu (show H.Adj y w from hyz)⟩
      simp [h1,triangleWeight,hxy,show ∃ z,G.Adj x z ∧ G.Adj y.val z from ⟨z,hxz,hyz⟩]
    · have h0 : H.degree y=0 := by
        by_contra! h
        obtain ⟨z,hz⟩ := (H.degree_pos_iff_exists_adj y).mp (by omega)
        exact ht ⟨z.val,z.property,hz⟩
      simp [h0,triangleWeight,hxy,ht]
  have only : (∑ y∈G.neighborFinset x,triangleWeight G x y) = ∑ y,triangleWeight G x y := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro y _ hy
    have h : ¬G.Adj x y := fun ha => hy ((G.mem_neighborFinset _ _).2 ha)
    simp [triangleWeight,h]
  have convertSum : (∑ y∈G.neighborFinset x,triangleWeight G x y) =
      ∑ y : G.neighborSet x, triangleWeight G x y.val :=
    Finset.sum_subtype _ (fun y => G.mem_neighborFinset x y) _
  have total := Finset.sum_congr (s₁ := Finset.univ) rfl (fun y _ => eq y)
  rw [Finset.sum_add_distrib,H.sum_degrees_eq_twice_card_edges] at total
  have indep := indepNum_add_edge_card_of_adj_unique (G := H) (fun ha hb => neighborhood_adj_unique h4 x ha hb)
  change (∑ y,triangleWeight G x y) = 2*H.indepNum
  rw [← only,convertSum]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at total
  change (∑ y : G.neighborSet x, triangleWeight G x y.val) + 2*H.edgeFinset.card =
    Fintype.card (G.neighborSet x)*2 at total
  omega

/-- If every edge is in a triangle, each incident triangle contributes
two neighbors and one independent choice. -/
theorem twice_indep_eq_degree_of_edges_in_triangles [Fintype V] [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (tri : ∀ {u v},G.Adj u v → ∃ z,G.Adj u z ∧ G.Adj v z) (v : V) :
    2*G.indepNeighborsCard v = G.degree v := by
  classical
  rw [← weighted_degree_eq_twice_indep h4 v, ← G.card_neighborFinset_eq_degree]
  have eq : (∑ w∈G.neighborFinset v,triangleWeight G v w) = ∑ w, triangleWeight G v w := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro w _ hw
    have no : ¬G.Adj v w := fun a => hw ((G.mem_neighborFinset _ _).2 a)
    simp [triangleWeight,no]
  rw [← eq]
  calc
    _ = ∑ _w∈G.neighborFinset v,1 := Finset.sum_congr rfl (fun w hw =>
      weight_of_triangle_edge ((G.mem_neighborFinset _ _).mp hw) (tri ((G.mem_neighborFinset _ _).mp hw)))
    _ = _ := by simp

def mass (w : V → V → ℕ) (s : Finset V) : ℕ := ∑ x∈s, ∑ y∈s,w x y

theorem mass_insert {w : V → V → ℕ} (hsym : ∀ x y,w x y=w y x)
    (hzero : ∀ x,w x x=0) [DecidableEq V] {u : V} {s : Finset V} (hu : u ∉ s) :
    mass w (insert u s) = mass w s+2*(∑ y∈s,w u y) := by
  simp only [mass,Finset.sum_insert hu,hzero,Nat.zero_add,Finset.sum_add_distrib]
  have e := Finset.sum_congr (s₁ := s) rfl (fun y _ => hsym y u)
  rw [e]
  ring

private theorem peel_weighted [DecidableEq V] (w : V → V → ℕ)
    (hsym : ∀ x y,w x y=w y x) (hzero : ∀ x,w x x=0) (s : Finset V)
    (hs : s.Nonempty) {k : ℕ} (hk : 0<k) (hd : 2*k*s.card ≤ mass w s) :
    ∃ t : Finset V, t.Nonempty ∧ (∀ x∈t,k < ∑ y∈t,w x y) ∧ 2*k*t.card ≤ mass w t := by
  classical
  by_cases ht : ∀ x∈s,k < ∑ y∈s,w x y
  · exact ⟨s,hs,ht,hd⟩
  push Not at ht
  obtain ⟨x,hx,hsmall⟩ := ht
  let t := s.erase x
  have hxt : x ∉ t := Finset.notMem_erase _ _
  have ins : insert x t=s := Finset.insert_erase hx
  have m := mass_insert hsym hzero hxt
  rw [ins] at m
  have card : s.card=t.card+1 := by rw [← ins,Finset.card_insert_of_notMem hxt]
  have deg : (∑ y∈s,w x y)=∑ y∈t,w x y := by rw [← ins,Finset.sum_insert hxt,hzero,Nat.zero_add]
  have hd' : 2*k*t.card ≤ mass w t := by
    rw [card,Nat.mul_succ] at hd
    omega
  have nonempty : t.Nonempty := by
    by_contra! empty
    have e : t=∅ := empty
    have m0 : mass w s=0 := by simpa only [e,mass,Finset.sum_empty,mul_zero,add_zero] using m
    rw [e] at card
    simp at card
    rw [card,Nat.mul_one] at hd
    omega
  exact peel_weighted w hsym hzero t nonempty hk hd'
termination_by s.card
decreasing_by exact Finset.card_erase_lt_of_mem hx

variable [Fintype V] [Nonempty V] [DecidableEq V] [DecidableRel G.Adj]

theorem exists_independence_core (h4 : NoFourCycle G) {k : ℕ} (hk : 0<k) (hav : (k:ℝ) ≤ l G) :
    ∃ S : Finset V, S.Nonempty ∧ (∀ v:S,k/2+1 ≤ (G.induce (S:Set V)).indepNeighborsCard v) ∧
       k*S.card ≤ ∑ v:S,(G.induce (S:Set V)).indepNeighborsCard v := by
  classical
  let w := triangleWeight G
  have zero (x) : w x x=0 := by simp [w,triangleWeight]
  have budget : 2*k*Fintype.card V ≤ mass w Finset.univ := by
    unfold mass
    simp only [w,weighted_degree_eq_twice_indep h4,← Finset.mul_sum]
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (le_average_iff_sum_indep.mp hav)
  obtain ⟨S,hs,hmin,hden⟩ := peel_weighted w (fun x y => weight_symm x y) zero
    Finset.univ Finset.univ_nonempty hk (by simpa using budget)
  let H := G.induce (S : Set V)
  have h4' : NoFourCycle H := by
    rintro x y a b hxy hxa hya hxb hyb
    exact Subtype.ext (h4 (fun e => hxy (Subtype.ext e)) hxa hya hxb hyb)
  have localBound (x:S) : (∑ y∈S,w x.val y) ≤ 2*H.indepNeighborsCard x := by
    rw [← weighted_degree_eq_twice_indep (G := H) h4' x, ← Finset.sum_attach S (w x.val)]
    exact Finset.sum_le_sum (fun y _ => weight_induce_le S x y)
  refine ⟨S,hs,fun x => ?_,?_⟩
  · change k/2+1 ≤ H.indepNeighborsCard x
    have := localBound x; have := hmin x.val x.property; omega
  · change k*S.card ≤ ∑ v:S,H.indepNeighborsCard v
    have u := Finset.sum_le_sum (s := Finset.univ) (fun (x:S) _ => localBound x)
    rw [← Finset.mul_sum] at u
    have e : mass w S = ∑ x:S, ∑ y∈S,w x.val y := (Finset.sum_attach S _).symm
    rw [← e] at u
    rw [Nat.mul_assoc] at hden
    omega

end Wall133
