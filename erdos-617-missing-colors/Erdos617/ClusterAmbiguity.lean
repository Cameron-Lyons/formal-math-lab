import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Erdos617

open Finset SimpleGraph

/-- Each vertex close to a different row contributes d incident cross edges.
Counting their endpoints charges each stored edge at most twice. -/
theorem ambiguous_incidence_bound {V ι : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : ι → Finset V) (A : Finset V)
    (F : Finset (Sym2 V)) {d q : ℕ} (hrow : ∀ j, d+q ≤ (B j).card)
    (hf : ∀ i j, i ≠ j → ∀ x ∈ B i, ∀ y ∈ B j, G.Adj x y → s(x,y) ∈ F)
    (hA : ∀ x ∈ A, ∃ i j, i ≠ j ∧ x ∈ B i ∧
      ((B j).filter (fun y => ¬G.Adj x y)).card ≤ q) :
    A.card*d ≤ 2*F.card := by
  classical
  have per (x : V) (hx : x ∈ A) : d ≤ (F.filter (fun e => x ∈ e)).card := by
    obtain ⟨i,j,hij,hBi,hclose⟩ := hA x hx
    have hsplit := (B j).card_filter_add_card_filter_not (G.Adj x)
    have hsize := hrow j
    have mapped : ((B j).filter (G.Adj x)).map (Sym2.mkEmbedding x) ⊆
        F.filter (fun e => x ∈ e) := by
      intro e he
      obtain ⟨y,hy,rfl⟩ := mem_map.mp he
      obtain ⟨hyB,hxy⟩ := mem_filter.mp hy
      exact mem_filter.mpr ⟨hf i j hij x hBi y hyB hxy,by simp⟩
    have hc := card_le_card mapped
    rw [card_map] at hc
    omega
  have perEdge (e : Sym2 V) : (A.filter (fun x => x ∈ e)).card ≤ 2 := by
    have sub : A.filter (fun x => x ∈ e) ⊆ e.toFinset :=
      fun _ hx => (Sym2.mem_toFinset).mpr (mem_filter.mp hx).2
    have hc := card_le_card sub
    rw [Sym2.card_toFinset] at hc
    split at hc <;> omega
  calc
    A.card*d = ∑ _ ∈ A, d := by simp
    _ ≤ ∑ x ∈ A, (F.filter (fun e => x ∈ e)).card := sum_le_sum per
    _ = ∑ e ∈ F, (A.filter (fun x => x ∈ e)).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun x e => x ∈ e)
    _ ≤ ∑ _ ∈ F, 2 := sum_le_sum fun e _ => perEdge e
    _ = 2*F.card := by simp [Nat.mul_comm]

end Erdos617
