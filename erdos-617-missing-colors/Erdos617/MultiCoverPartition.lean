module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

/-- A q-clique through a vertex of degree at most q−1 is its entire closed
neighborhood. If every vertex lies in such a clique, their sizes divide the order. -/
theorem no_partition_into_q_cliques {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [DecidableRel G.Adj] {q t : ℕ} (hq : 2 ≤ q)
    (hn : Fintype.card ι=q*t+1) (hdeg : ∀ i, G.degree i ≤ q-1)
    (hclq : ∀ i, ∃ C : Finset ι, i∈C ∧ G.IsNClique q C) : False := by
  classical
  let N (i : ι) := insert i (G.neighborFinset i)
  have full {C : Finset ι} (hc : G.IsNClique q C) {i : ι} (hi : i∈C) : C=N i := by
    have incl : C ⊆ N i := by
      intro j hj
      by_cases he : j=i
      · exact mem_insert.mpr (Or.inl he)
      · exact mem_insert_of_mem ((G.mem_neighborFinset i j).mpr (hc.isClique hi hj (Ne.symm he)))
    apply eq_of_subset_of_card_le incl
    have cap := card_insert_le i (G.neighborFinset i)
    rw [card_neighborFinset_eq_degree] at cap
    rw [hc.card_eq]
    change (insert i (G.neighborFinset i)).card ≤ q
    have := hdeg i
    omega
  have nc (i : ι) : G.IsNClique q (N i) := by
    obtain ⟨C, hi, hc⟩ := hclq i
    exact full hc hi ▸ hc
  let P := univ.image N
  have dis : (P : Set (Finset ι)).PairwiseDisjoint id := by
    intro A hA B hB hne
    obtain ⟨i, _, rfl⟩ := mem_image.mp hA
    obtain ⟨j, _, rfl⟩ := mem_image.mp hB
    exact disjoint_left.mpr (fun x hx hy => hne ((full (nc i) hx).trans (full (nc j) hy).symm))
  have cover : P.biUnion id=univ := eq_univ_of_forall fun i =>
    mem_biUnion.mpr ⟨N i,mem_image.mpr ⟨i,mem_univ _,rfl⟩,mem_insert_self ..⟩
  have count := card_biUnion dis
  rw [cover,card_univ,hn] at count
  have sizes (A : Finset ι) (ha : A∈P) : A.card=q := by
    obtain ⟨i,_,rfl⟩ := mem_image.mp ha
    exact (nc i).card_eq
  simp only [id_eq, sum_congr rfl sizes, sum_const, nsmul_eq_mul, Nat.cast_id] at count
  have hdiv : q ∣ 1 := (Nat.dvd_add_iff_right (dvd_mul_right q t)).mpr
    (show q ∣ q*t+1 from ⟨P.card,by simpa only [Nat.mul_comm P.card q] using count⟩)
  have := Nat.le_of_dvd (by decide : 0<1) hdiv
  omega

end Erdos617
