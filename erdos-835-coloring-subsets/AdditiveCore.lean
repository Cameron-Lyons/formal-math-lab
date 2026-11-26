module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-! # The zero-sum partial quadruple system on 17 points

Some triples on the 17 finite points have no distinct fourth point making
the sum zero modulo 17. To complete these triples in a Steiner quadruple
system on 20 points would require a choice among the three extra points.
Two different triples sharing a pair must make different choices.
The following induced subgraph of the triple-overlap graph already
has chromatic number greater than three. -/

namespace Erdos835
namespace AdditiveCore

open Finset

private abbrev V := Fin 20
private abbrev Index := Fin 36

private def triples : Vector (Finset V) 36 :=
  #v[{1, 2, 7}, {1, 2, 12}, {1, 2, 13},
    {1, 3, 10}, {1, 5, 10}, {1, 5, 14},
    {1, 7, 8}, {1, 7, 13}, {1, 10, 13},
    {2, 3, 10}, {2, 5, 8}, {2, 8, 12},
    {2, 8, 16}, {2, 10, 11}, {2, 10, 12},
    {3, 10, 11}, {4, 7, 16}, {4, 10, 16},
    {4, 15, 16}, {5, 8, 16}, {5, 10, 14},
    {5, 14, 16}, {5, 15, 16}, {7, 8, 12},
    {7, 12, 16}, {8, 11, 16}, {10, 11, 15},
    {10, 13, 14}, {10, 13, 15}, {10, 15, 16},
    {11, 12, 14}, {11, 12, 16}, {11, 13, 14},
    {11, 13, 16}, {11, 14, 15}, {12, 13, 14}]

private def tr (i : Index) : Finset V := triples.get i

/-- Each row names a vertex and some earlier vertices it must differ from. -/
private def plan : List (Index × List Index) :=
  [(8, []), (4, [8]), (3, [8, 4]), (2, [8]),
    (7, [8, 2]), (0, [2, 7]), (1, [2, 0]), (6, [7, 0]),
    (15, [3]), (9, [3, 15]), (14, [1, 9]), (13, [15, 9, 14]),
    (26, [15, 13]), (11, [1, 14]), (28, [8, 26]), (27, [8, 28]),
    (20, [4, 27]), (29, [26, 28]), (5, [4, 20]), (21, [20, 5]),
    (22, [29, 21]), (19, [21, 22]), (10, [11, 19]), (12, [11, 19, 10]),
    (18, [29, 22]), (25, [19, 12]), (23, [6, 11]), (17, [29, 18]),
    (16, [18, 17]), (24, [23, 16]), (31, [25, 24]), (33, [25, 31]),
    (32, [27, 33]), (35, [27, 32]), (30, [31, 32, 35]), (34, [26, 32, 30])]

private def legal (row : Index × List Index) (a : Fin 3)
    (history : List (Index × Fin 3)) : Bool :=
  history.all fun e => !(e.2 == a && row.2.contains e.1)

private def search : List (Index × List Index) → List (Index × Fin 3) → Bool
  | [], _ => true
  | row :: rest, history =>
    ([0,1,2] : List (Fin 3)).any fun a =>
      legal row a history && search rest ((row.1, a) :: history)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2500000 in
private theorem closed_search : search plan [] = false := by decide +kernel

private def checked (rows : List (Index × List Index)) : Bool :=
  rows.all fun e => e.2.all fun j => decide (((tr e.1) ∩ (tr j)).card = 2)

set_option maxRecDepth 100000 in
private theorem plan_valid : checked plan = true := by decide +kernel

private theorem search_complete (f : Index → Fin 3)
    (proper : ∀ i j : Index, ((tr i) ∩ (tr j)).card = 2 → f i ≠ f j)
    (rows : List (Index × List Index)) (valid : checked rows = true)
    (hist : List (Index × Fin 3)) (agree : ∀ e ∈ hist, f e.1 = e.2) :
    search rows hist = true := by
  induction rows generalizing hist with
  | nil => rfl
  | cons row rest ih =>
    have hrow := (List.all_eq_true.mp valid) row (List.mem_cons_self ..)
    have hrest : checked rest = true := List.all_eq_true.mpr
      (fun v hv => List.all_eq_true.mp valid v (List.mem_cons_of_mem _ hv))
    apply List.any_eq_true.mpr
    have memColors : ∀ a : Fin 3, a ∈ ([0,1,2] : List (Fin 3)) := by decide
    refine ⟨f row.1, memColors _, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
    · apply List.all_eq_true.mpr
      intro e he
      simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne]
      by_cases h : e.1 ∈ row.2
      · exact Or.inl (fun eq => (proper _ _ (of_decide_eq_true (List.all_eq_true.mp hrow e.1 h)))
          ((agree e he).trans eq).symm)
      · exact Or.inr (by simpa using h)
    · apply ih hrest
      intro e he
      rcases List.mem_cons.mp he with rfl | h
      · rfl
      · exact agree _ h

private def closeTriple (T : Finset V) : Finset V :=
  insert (⟨(17 - (T.sum Fin.val % 17)) % 17, by omega⟩ : V) T

set_option maxRecDepth 100000 in
private theorem sizes : ∀ i : Index, (tr i).card = 3 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2500000 in
/-- Every possible finite partner conflicts with a required zero-sum block. -/
private theorem conflicts : ∀ (i : Index) (x : V), x.val < 17 → x ∉ tr i →
    ∃ d ∈ insert x (tr i),
      let Q := insert x (tr i)
      let B := closeTriple (Q.erase d)
      B.card = 4 ∧ (∀ y ∈ B, y.val < 17) ∧ B.sum Fin.val % 17 = 0 ∧ B ≠ Q := by
  decide +kernel

/-- Two distinct triples sharing a pair cannot be completed with the same
external point. Both resulting blocks would cover that pair plus the point. -/
private theorem partners_differ (D : Finset V → Prop)
    (covers : ∀ T : Finset V, T.card = 3 → ∃! B, D B ∧ T ⊆ B)
    (i j : Index) (edge : ((tr i) ∩ (tr j)).card = 2) (x : V)
    (hi : x ∉ tr i) (hj : x ∉ tr j)
    (Bi : D (insert x (tr i))) (Bj : D (insert x (tr j))) : False := by
  let T := insert x (tr i ∩ tr j)
  have ht : T.card = 3 := by simp [T, hi, edge]
  have heq : insert x (tr i) = insert x (tr j) :=
    (covers T ht).unique ⟨Bi, insert_subset_insert _ inter_subset_left⟩
      ⟨Bj, insert_subset_insert _ inter_subset_right⟩
  have htr : tr i = tr j := by
    simpa [hi, hj] using congrArg (fun B : Finset V => B.erase x) heq
  rw [htr, inter_self, sizes] at edge
  contradiction

end AdditiveCore

open Finset AdditiveCore

/-- No Steiner quadruple system on 20 points can contain all the quadruples
on the first seventeen points whose ordinary label sum is 0 modulo 17. -/
theorem no_additive_quadruple_extension (D : Finset (Fin 20) → Prop)
    (uniform : ∀ B, D B → B.card = 4)
    (covers : ∀ T : Finset (Fin 20), T.card = 3 → ∃! B, D B ∧ T ⊆ B)
    (additive : ∀ B : Finset (Fin 20), B.card = 4 → (∀ x ∈ B, x.val < 17) →
      B.sum Fin.val % 17 = 0 → D B) : False := by
  classical
  have partner (i : Index) : ∃ x : V, x ∉ tr i ∧ D (insert x (tr i)) := by
    obtain ⟨B, ⟨hB, hsub⟩, _⟩ := covers (tr i) (sizes i)
    obtain ⟨x, hx, he⟩ := exists_eq_insert_iff.mpr ⟨hsub, by rw [uniform B hB, sizes]⟩
    exact ⟨x, hx, he ▸ hB⟩
  choose p hp hD using partner
  have outside (i : Index) : 17 ≤ (p i).val := by
    by_contra! inside
    obtain ⟨d, hd, hc, hfin, hsum, hne⟩ := conflicts i (p i) inside (hp i)
    let Q := insert (p i) (tr i)
    let S := Q.erase d
    have hQ := uniform Q (hD i)
    have hS : S.card = 3 := by rw [card_erase_of_mem hd, hQ]
    exact hne ((covers S hS).unique
      ⟨additive (closeTriple S) hc hfin hsum, subset_insert _ _⟩
      ⟨hD i, erase_subset _ _⟩)
  let color (i : Index) : Fin 3 := ⟨(p i).val - 17, by have := (p i).isLt; omega⟩
  have proper (i j : Index) (overlap : ((tr i) ∩ (tr j)).card = 2) : color i ≠ color j := by
    intro h
    have eq := congrArg Fin.val h
    change (p i).val - 17 = (p j).val - 17 at eq
    have peq : p i = p j := Fin.ext (by have := outside i; have := outside j; omega)
    exact partners_differ D covers i j overlap (p i) (hp i) (peq ▸ hp j)
      (hD i) (peq ▸ hD j)
  have good := search_complete color proper plan plan_valid [] (by simp)
  rw [closed_search] at good
  contradiction

end Erdos835
