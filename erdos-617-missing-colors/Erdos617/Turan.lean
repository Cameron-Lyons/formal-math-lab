import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Linarith

namespace Erdos617

open SimpleGraph
open scoped BigOperators

/-- Every `r`-coloring on more than `(r - 1)^2` vertices has `r` vertices
on whose edges a color is missing. -/
theorem missing_color_on_r_vertices (r : ℕ) (hr : 2 ≤ r)
    {V : Type*} [Fintype V] [DecidableEq V] (hV : (r - 1)^2 < Fintype.card V)
    (coloring : Sym2 V → Fin r) :
    ∃ (S : Finset V) (k : Fin r), S.card = r ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k := by
  classical
  obtain ⟨a, rfl⟩ : ∃ a, r = a + 2 := ⟨r - 2, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card V = m + 1 :=
    ⟨Fintype.card V - 1, by omega⟩
  let E := (⊤ : SimpleGraph V).edgeFinset
  let G (k : Fin (a + 2)) : SimpleGraph V := fromEdgeSet {e | coloring e ≠ k}
  by_contra h
  have hfree (k : Fin (a + 2)) : (G k).CliqueFree (a + 2) := by
    intro S hS
    exact h ⟨S, k, hS.2, fun _ hu _ hv huv ↦ (hS.1 hu hv huv).1⟩
  have hlimit (k : Fin (a + 2)) :
      E.card ≤ (E.filter fun e ↦ coloring e = k).card + turanNumber (m + 1) (a + 1) := by
    have hfilter : E.filter (fun e ↦ coloring e ≠ k) = (G k).edgeFinset := by
      ext e
      induction e using Sym2.inductionOn with
      | _ u v =>
        simp [E, G, Finset.mem_filter, mem_edgeFinset, and_comm]
    have hcard := Finset.card_filter_add_card_filter_not (s := E) (fun e ↦ coloring e = k)
    rw [hfilter] at hcard
    have hbound := (hfree k).card_edgeFinset_le
    rw [hm] at hbound
    rw [← hcard]
    apply Nat.add_le_add_left
    convert! hbound using 1
    congr 2
    apply Subsingleton.elim
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun k _ ↦ hlimit k)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Finset.sum_card_fiberwise_eq_card_filter, Finset.mem_univ, Finset.filter_true]
    at hsum
  have hE : E.card = (m + 1).choose 2 := by
    rw [← hm, ← card_edgeFinset_top_eq_card_choose_two]
  rw [hE] at hsum
  have ht := mul_turanNumber_le (n := m + 1) (r := a + 1)
  simp only [Nat.add_sub_cancel] at ht
  have he : (m + 1) * m = (m + 1).choose 2 * 2 := by
    simpa using Nat.add_one_mul_choose_eq m 1
  have hsmall : (a + 1) * (m + 1).choose 2 ≤ (a + 2) * turanNumber (m + 1) (a + 1) := by
    nlinarith only [hsum]
  have hscaled := Nat.mul_le_mul_left (2 * (a + 1)) hsmall
  have hupper := Nat.mul_le_mul_left (a + 2) ht
  have hbad : (m + 1) * (m + 1) ≤ (m + 1) * (a + 1)^2 := by
    nlinarith only [hscaled, hupper, congrArg (fun t ↦ (a + 1)^2 * t) he]
  have := Nat.le_of_mul_le_mul_left hbad (Nat.succ_pos m)
  rw [hm, show a + 2 - 1 = a + 1 by omega] at hV
  omega

end Erdos617
