import Erdos617.ColorGraph
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace Erdos617

open SimpleGraph

theorem twice_choose_two (n : ℕ) : 2 * n.choose 2 + n = n * n := by
  cases n with
  | zero => decide
  | succ n =>
    have H := Nat.add_one_mul_choose_eq n 1
    simp only [Nat.choose_one_right] at H
    nlinarith only [H]

private theorem choose_two_add (n r : ℕ) :
    (n+r).choose 2 = n.choose 2 + n*r + r.choose 2 := by
  nlinarith only [twice_choose_two n, twice_choose_two r, twice_choose_two (n+r)]

/-- At order tr+1 the complement of the Turán graph comprises one clique of
order t+1 and r−1 cliques of order t. -/
private theorem turan_complement_count (r t : ℕ) (hr : 0 < r) :
    (t*r+1).choose 2 = turanNumber (t*r+1) r + r*t.choose 2 + t := by
  obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  induction t with
  | zero =>
    have h := (turanGraph 1 (s+1)).card_edgeFinset_le_card_choose_two
    change turanNumber 1 (s+1) ≤ (Fintype.card (Fin 1)).choose 2 at h
    simp only [Fintype.card_fin] at h
    have hzero : turanNumber 1 (s+1) = 0 := Nat.eq_zero_of_le_zero h
    simp [hzero]
  | succ t ih =>
    rw [Nat.succ_mul, Nat.add_right_comm _ (s+1) 1, turanNumber_add, choose_two_add,
      Nat.choose_succ_succ' t 1, Nat.choose_one_right, ih, Nat.add_sub_cancel]
    ring

/-- Every color in a balanced coloring of tr+1 vertices has at least
r * choose(t,2) + t edges. -/
theorem color_edge_count_of_balanced {r t : ℕ} (hr : 0 < r)
    {V : Type*} [Fintype V] [DecidableEq V] (hV : Fintype.card V = t*r+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r) :
    r*t.choose 2 + t ≤ (colorGraph c k).edgeFinset.card := by
  classical
  let G := colorGraph c k
  have hfree : Gᶜ.CliqueFree (r+1) := by
    intro S hS
    obtain ⟨u, hu, v, hv, huv, hcol⟩ := hb S hS.card_eq k
    exact (hS.isClique hu hv huv).2 ⟨huv, hcol⟩
  have hupper := hfree.card_edgeFinset_le
  have hdisj : Disjoint G.edgeFinset Gᶜ.edgeFinset :=
    disjoint_edgeFinset.mpr disjoint_compl_right
  have hcount := Finset.card_union_of_disjoint hdisj
  have hunion : G.edgeFinset ∪ Gᶜ.edgeFinset = (⊤ : SimpleGraph V).edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | _ a b =>
      by_cases h : G.Adj a b
      · simp [Finset.mem_union, mem_edgeFinset, h, h.ne]
      · simp [Finset.mem_union, mem_edgeFinset, h]
  rw [hunion, card_edgeFinset_top_eq_card_choose_two, hV,
    turan_complement_count r t hr] at hcount
  rw [hV] at hupper
  change r*t.choose 2 + t ≤ G.edgeFinset.card
  omega

/-- The bound applies to each induced coloring of a tr+1 vertex set in a balanced coloring. -/
theorem induced_color_edge_count_of_balanced {r t : ℕ} (hr : 0 < r)
    {V : Type*} [DecidableEq V] (c : Sym2 V → Fin r) (hb : Balanced c)
    (S : Finset V) (hS : S.card = t*r+1) (k : Fin r) :
    r*t.choose 2 + t ≤ (colorGraph (fun e : Sym2 S => c (Sym2.map Subtype.val e)) k).edgeFinset.card := by
  exact color_edge_count_of_balanced hr ((Fintype.card_coe S).trans hS) _
    (balanced_pullback c hb (Function.Embedding.subtype (· ∈ S))) k

private theorem color_edges_eq_filter {r : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (c : Sym2 V → Fin r) (j : Fin r) :
    (colorGraph c j).edgeFinset = (⊤ : SimpleGraph V).edgeFinset.filter (fun e => c e = j) := by
  ext e
  induction e using Sym2.inductionOn with
  | _ x y => simp [mem_edgeFinset, Finset.mem_filter]

theorem sum_color_edges {r : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (c : Sym2 V → Fin r) :
    ∑ j, (colorGraph c j).edgeFinset.card = (Fintype.card V).choose 2 := by
  simp_rw [color_edges_eq_filter, Finset.sum_card_fiberwise_eq_card_filter]
  rw [Finset.filter_true_of_mem (fun _ _ => Finset.mem_univ _), card_edgeFinset_top_eq_card_choose_two]

/-- The complement of the graph of color k is the disjoint union of the other colors. -/
theorem sum_other_color_edges {r : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (c : Sym2 V → Fin r) (k : Fin r) :
    ∑ j ∈ Finset.univ.erase k, (colorGraph c j).edgeFinset.card =
      (colorGraph c k)ᶜ.edgeFinset.card := by
  simp_rw [color_edges_eq_filter, Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
    by_cases h : x = y <;> simp [mem_edgeFinset, Finset.mem_filter, compl_adj, h]

/-- A lower bound on each other color's edge count forces a high-degree
vertex in the complement of color k. -/
theorem exists_compl_degree_ge {r n a d : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (c : Sym2 V → Fin r) (k : Fin r) (hn : Fintype.card V = n)
    (hl : ∀ j, j ≠ k → a ≤ (colorGraph c j).edgeFinset.card)
    (hcount : n*d < 2*((r-1)*a)) : ∃ x, d < (colorGraph c k)ᶜ.degree x := by
  by_contra! h
  have he := Finset.sum_le_sum (s := Finset.univ.erase k)
    (fun j hj => hl j (Finset.mem_erase.mp hj).1)
  rw [sum_other_color_edges] at he
  simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ k),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at he
  have hd := Finset.sum_le_sum (s := Finset.univ) (fun x _ => h x)
  rw [sum_degrees_eq_twice_card_edges] at hd
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hn] at hd
  exact hcount.not_ge ((Nat.mul_le_mul_left 2 he).trans hd)

end Erdos617
