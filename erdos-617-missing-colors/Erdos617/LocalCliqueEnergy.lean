module

public import Erdos617.LocalCliqueWeights
public import Erdos617.SimplexEnergy
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
The local clique quadratic inequality below is Theorem 2.2 of
[Localization of the Caro–Wei bound and its applications to bipartiteness](https://arxiv.org/abs/2609.00210).
We use its uniform-weight specialization to count cliques in every color at once.
-/

namespace Erdos617

open Finset SimpleGraph Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Maximum order of a clique containing a prescribed vertex. -/
noncomputable def pointClique (G : SimpleGraph V) (v : V) : ℕ := by
  classical
  exact (univ.filter fun C : Finset V => v ∈ C ∧ G.IsClique (C : Set V)).sup card

theorem exists_pointClique (G : SimpleGraph V) (v : V) :
    ∃ C : Finset V, v∈C ∧ G.IsNClique (pointClique G v) C := by
  classical
  let P := univ.filter fun C : Finset V => v∈C ∧ G.IsClique (C : Set V)
  have hn : P.Nonempty := ⟨{v},by simp [P]⟩
  obtain ⟨C,hC,eq⟩ := exists_mem_eq_sup P hn card
  exact ⟨C,(mem_filter.mp hC).2.1,(mem_filter.mp hC).2.2,eq.symm⟩

theorem card_le_pointClique (G : SimpleGraph V) (C : Finset V) (h : G.IsClique (C : Set V))
    (v : V) (hv : v∈C) : C.card ≤ pointClique G v := by
  classical
  exact le_sup (f:=card) (mem_filter.mpr ⟨mem_univ _,hv,h⟩)

/-- The local clique energy bound on a probability vector. -/
theorem local_clique_energy (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → ℕ)
    (hcap : ∀ C : Finset V, G.IsClique (C : Set V) → ∀ v ∈ C, C.card ≤ c v)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hs : ∑ v,w v=1) :
    2 ≤ (G.indepNum : ℝ)*(∑ v,w v*(((c v : ℝ)+1)*w v + ∑ u ∈ G.neighborFinset v, w u)) := by
  let A : Matrix V V ℝ := fun i j => (if i=j then (c i : ℝ)+1 else 0)+(if G.Adj i j then 1 else 0)
  have symm : Aᵀ=A := by
    ext i j
    change (if j=i then (c j : ℝ)+1 else 0)+(if G.Adj j i then 1 else 0)=_
    by_cases e : i=j
    · subst j; rfl
    · simp [A,e,Ne.symm e,G.adj_comm]
  have row (x : V → ℝ) (i : V) : (A *ᵥ x) i = ((c i : ℝ)+1)*x i+∑ j∈G.neighborFinset i,x j := by
    change ∑ j, (((if i=j then (c i : ℝ)+1 else 0)+(if G.Adj i j then 1 else 0))*x j)=_
    simp_rw [add_mul,ite_mul,zero_mul,one_mul]
    rw [sum_add_distrib,G.neighborFinset_eq_filter,sum_filter]
    simp [add_mul]
  obtain ⟨x,hx,hsum,heq,hle⟩ := simplex_energy_equilibrium A symm w hw hs
  have bound := equilibrium_local_clique_bound G c hcap x hx hsum (x ⬝ᵥ (A *ᵥ x))
    (fun i hi => (row x i).symm.trans (heq i hi))
  apply bound.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  simpa only [dotProduct,row] using hle

/-- A uniform-weight bound using the sizes of cliques through individual vertices. -/
theorem card_square_le_local_clique_energy (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → ℕ)
    (hcap : ∀ C : Finset V, G.IsClique (C : Set V) → ∀ v ∈ C, C.card ≤ c v) :
    2*(Fintype.card V)^2 ≤ G.indepNum*((∑ v,G.degree v)+Fintype.card V+(∑ v,c v)) := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · simp
  let N : ℝ := Fintype.card V
  have hp : 0<N := by dsimp [N]; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card V)
  have sumW : (∑ _v : V, (1/N : ℝ))=1 := by
    simp only [sum_const,card_univ,nsmul_eq_mul]
    change N*(1/N)=1
    field_simp
  have b := local_clique_energy G c hcap (fun _ => 1/N) (fun _ => by positivity) sumW
  have per (v : V) : 1/N*(((c v : ℝ)+1)*(1/N)+∑ _u∈G.neighborFinset v, (1/N:ℝ)) =
      ((G.degree v:ℝ)+1+c v)/N^2 := by
    simp only [sum_const,nsmul_eq_mul,card_neighborFinset_eq_degree]
    field_simp
    ring
  simp_rw [per] at b
  simp_rw [div_eq_mul_inv] at b
  rw [←sum_mul, sum_add_distrib,sum_add_distrib] at b
  simp only [sum_const,card_univ,nsmul_eq_mul,mul_one] at b
  rw [←mul_assoc, ←div_eq_mul_inv] at b
  have le := (le_div_iff₀ (sq_pos_of_pos hp)).mp b
  dsimp only [N] at le
  exact_mod_cast le

end Erdos617
