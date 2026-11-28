import ThreeStacks.Model

namespace ThreeStacks

/-- Consecutive pushes place a block on the stack in reverse arrival order. -/
private theorem push_block (xs : List Nat) {i s o : List Nat}
    (h : Pass i (xs.reverse ++ s) o) : Pass (xs ++ i) s o := by
  induction xs generalizing s with
  | nil => simpa using h
  | cons x xs ih =>
    apply Pass.push
    apply ih
    simpa [List.reverse_cons, List.append_assoc] using h

/-- Consecutive pops send the block at the top to the output in stack order. -/
private theorem pop_block (xs : List Nat) {i s o : List Nat} (h : Pass i s o) :
    Pass i (xs ++ s) (xs ++ o) := by
  induction xs with
  | nil => exact h
  | cons x xs ih => exact Pass.pop ih

/-- Replacing each card by a block reverses that block in a single stack. -/
theorem pass_expand {i s o : List Nat} (h : Pass i s o) (f : Nat → List Nat) :
    Pass (i.flatMap f) (s.flatMap (fun x => (f x).reverse))
      (o.flatMap (fun x => (f x).reverse)) := by
  induction h with
  | done => exact .done
  | @push x i s o _ ih =>
    rw [List.flatMap_cons]
    exact push_block (f x) (by simpa using ih)
  | @pop x i s o _ ih => exact pop_block (f x).reverse ih

/-- Following the same schedule through three stacks reverses every block. -/
theorem sortsTo_expand {p q : List Nat} (h : SortsTo p q) (f : Nat → List Nat) :
    SortsTo (p.flatMap f) (q.flatMap (fun x => (f x).reverse)) := by
  obtain ⟨a, b, h₁, h₂, h₃⟩ := h
  refine ⟨a.flatMap (fun x => (f x).reverse), b.flatMap f, pass_expand h₁ f, ?_, pass_expand h₃ f⟩
  simpa using pass_expand h₂ (fun x => (f x).reverse)

/-- Split label k into k+1,k, increasing every greater label to make room. -/
def descendingPair (k x : Nat) : List Nat :=
  if x < k then [x] else if x = k then [k+1,k] else [x+1]

private theorem expand_after (k s n : Nat) (h : k < s) :
    (List.range' s n).flatMap (fun x => (descendingPair k x).reverse) =
      List.range' (s+1) n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have hs : ¬ s < k := by omega
    have hne : s ≠ k := by omega
    simp only [List.range'_succ, List.flatMap_cons, descendingPair, hs, hne, ↓reduceIte,
      List.reverse_singleton, List.singleton_append, List.cons.injEq, true_and]
    exact ih (s+1) (by omega)

private theorem expand_through (k s n : Nat) (lo : s ≤ k) (hi : k < s+n) :
    (List.range' s n).flatMap (fun x => (descendingPair k x).reverse) =
      List.range' s (n+1) := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
    by_cases eq : s = k
    · subst s
      rw [List.range'_succ (s := k) (n := n), List.flatMap_cons,
        expand_after k (k+1) n (by omega)]
      simp [descendingPair, List.range'_succ]
    · have hs : s < k := by omega
      rw [List.range'_succ (s := s) (n := n), List.flatMap_cons,
        ih (s+1) (by omega) (by omega)]
      simp [descendingPair, hs, List.range'_succ]

/-- A sorting run for the contracted deck supplies one for the expanded deck. -/
theorem sortable_expand_descending_pair {n k : Nat} {p : List Nat}
    (h : Sortable n p) (lo : 1 ≤ k) (hi : k ≤ n) :
    Sortable (n+1) (p.flatMap (descendingPair k)) := by
  have route := sortsTo_expand h (descendingPair k)
  unfold target at route
  rw [expand_through k 1 n lo (by omega)] at route
  exact route

end ThreeStacks
