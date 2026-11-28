import Ramsey39

namespace Ramsey310

/-- Every triangle-free simple graph on n vertices has an independent set of at least ten. -/
def RamseyProperty (n : Nat) : Prop :=
  ∀ edge : Fin n → Fin n → Bool, Simple edge → TriangleFree edge →
    ∃ s, Independent edge s ∧ 10 ≤ orderOf s

/-- The ordinary Ramsey number is the least order with the Ramsey property. -/
def IsRamseyNumber (n : Nat) : Prop :=
  RamseyProperty n ∧ ∀ m, RamseyProperty m → n ≤ m

/-- A concrete adjacency table can refute the Ramsey property by computation. -/
theorem refute_with_witness {n : Nat} {edge : Fin n → Fin n → Bool}
    (simple : Simple edge) (free : TriangleFree edge)
    (pass : excludesIndependentTen edge = true) : ¬ RamseyProperty n := by
  intro h
  obtain ⟨s, ind, size⟩ := h edge simple free
  exact Nat.not_lt_of_ge size (excludesIndependentTen_sound pass s ind)

/-- Restrict a graph to the last n vertices, then use the same independent set. -/
private theorem ramsey_succ {n : Nat} (h : RamseyProperty n) : RamseyProperty (n+1) := by
  intro edge simple triangleFree
  let restricted (u v : Fin n) := edge u.succ v.succ
  obtain ⟨s, independent, size⟩ := h restricted
    ⟨fun v => simple.1 v.succ, fun v w => simple.2 v.succ w.succ⟩
    (fun u v w => triangleFree u.succ v.succ w.succ)
  refine ⟨Fin.cases false s, ?_, ?_⟩
  · intro u v
    refine Fin.cases (by simp) (fun a => ?_) u
    refine Fin.cases (by simp) (fun b => ?_) v
    simpa [restricted] using independent a b
  · simpa [orderOf, List.finRange_succ, List.filter_map, Function.comp_def] using size

private theorem ramsey_mono {n m : Nat} (h : n ≤ m) (hr : RamseyProperty n) :
    RamseyProperty m := by
  induction h with
  | refl => exact hr
  | step _ ih => exact ramsey_succ ih

theorem ramsey_lower_bound {n : Nat} (h : RamseyProperty n) : 40 ≤ n := by
  apply Nat.le_of_not_gt
  intro smaller
  have at39 := ramsey_mono (Nat.le_of_lt_succ (n := 39) smaller) h
  obtain ⟨s, independent, ten⟩ := at39 adjacent exoo_simple exoo_triangleFree
  exact Nat.not_lt_of_ge ten (exoo_independence_bound s independent)

/-- The only missing hypothesis for the value 40 is the unrestricted order-40 property. -/
theorem forty_iff : IsRamseyNumber 40 ↔ RamseyProperty 40 :=
  ⟨And.left, fun h => ⟨h, fun _ => ramsey_lower_bound⟩⟩

/-- Given the published upper bound, a counterexample at order 40 settles the value at 41. -/
theorem fortyOne_iff (upper : RamseyProperty 41) : IsRamseyNumber 41 ↔ ¬ RamseyProperty 40 := by
  constructor
  · intro h h40
    have := h.2 40 h40
    omega
  · intro h40
    refine ⟨upper, fun m hm => ?_⟩
    apply Nat.le_of_not_gt
    intro smaller
    exact h40 (ramsey_mono (Nat.le_of_lt_succ smaller) hm)

end Ramsey310
