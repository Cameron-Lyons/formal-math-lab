import Ramsey556.Cert16.Basic

namespace Ramsey556.Cert16

/-- Low-to-high nibbles give the images of the extended graph's vertices. -/
def permDigit (p i : Nat) : Nat := (p >>> (4*i)) &&& 15

private def tri (i : Nat) : Nat := i*(i-1)/2

private def allBelow (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n+1 => p n && allBelow p n

private theorem allBelow_true {p : Nat → Bool} {n : Nat} (h : allBelow p n = true) :
    ∀ i, i < n → p i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    obtain ⟨top, rest⟩ := Bool.and_eq_true_iff.mp h
    intro i lt
    by_cases e : i = n
    · simpa [e] using top
    · exact ih rest i (by omega)

/-- Check each pair below the diagonal against a row of the extended graph.
Comparing the image labels also detects collisions in the permutation. -/
def isoOK (n g m h p : Nat) : Bool :=
  allBelow (fun i =>
    let u := permDigit p i
    let start := tri u
    let row := if i = n then m else g >>> tri i
    u ≤ n && allBelow (fun j =>
      let v := permDigit p j
      if u < v then h.testBit (tri v + u) == row.testBit j
      else if v < u then h.testBit (start + v) == row.testBit j
      else false) i) (n+1)

private theorem edge_comm (g i j : Nat) : edge g i j = edge g j i := by
  simp only [edge, (bne_comm (a := i) (b := j)), Nat.max_comm i j, Nat.min_comm i j]

private theorem extend_comm (n g m i j : Nat) :
    extendEdge n g m i j = extendEdge n g m j i := by
  by_cases h : i = j
  · subst j; rfl
  · by_cases hi : i = n <;> by_cases hj : j = n <;> simp [extendEdge, h, Ne.symm h, hi, hj, edge_comm g j i] <;> omega

theorem isoOK_sound {n g m h p : Nat} (hc : isoOK n g m h p = true) :
    ExtendsTo n g m h := by
  have raw := allBelow_true hc
  have hc (i : Nat) (hi : i < n+1) : permDigit p i ≤ n ∧
      ∀ j, j < i → permDigit p i ≠ permDigit p j ∧
        edge h (permDigit p i) (permDigit p j) = extendEdge n g m i j := by
    have ⟨bound, inner⟩ := Bool.and_eq_true_iff.mp (raw i hi)
    refine ⟨of_decide_eq_true bound, ?_⟩
    intro j hj
    have q := allBelow_true inner j hj
    have r : (if i = n then m else g >>> tri i).testBit j = extendEdge n g m i j := by
      by_cases e : i = n
      · simp [e, extendEdge, show n ≠ j by omega]
      · simp [e, extendEdge, show i ≠ j by omega, show j ≠ n by omega, edge, tri,
          Nat.max_eq_left (Nat.le_of_lt hj), Nat.min_eq_right (Nat.le_of_lt hj)]
    by_cases e : permDigit p i < permDigit p j
    · have ne := Nat.ne_of_lt e
      refine ⟨ne, ?_⟩
      rw [← r]
      simpa [e, edge, bne_iff_ne.mpr ne, tri, Nat.max_eq_right (Nat.le_of_lt e),
        Nat.min_eq_left (Nat.le_of_lt e)] using q
    · by_cases e' : permDigit p j < permDigit p i
      · have ne := Nat.ne_of_gt e'
        refine ⟨ne, ?_⟩
        rw [← r]
        simpa [e, e', edge, bne_iff_ne.mpr ne, tri, Nat.max_eq_left (Nat.le_of_lt e'),
          Nat.min_eq_right (Nat.le_of_lt e')] using q
      · simp [e, e'] at q
  let f (i : Fin (n+1)) : Fin (n+1) := ⟨permDigit p i.val, Nat.lt_succ_of_le (hc _ i.isLt).1⟩
  have row {i j : Fin (n+1)} (lt : j.val < i.val) := (hc i.val i.isLt).2 j.val lt
  refine ⟨f, ?_, ?_⟩
  · intro i j eq
    have e := congrArg Fin.val eq
    change permDigit p i.val = permDigit p j.val at e
    apply Fin.ext
    apply Classical.byContradiction
    intro diff
    by_cases lt : j.val < i.val
    · exact (row lt).1 e
    · exact (row (i := j) (j := i) (by omega)).1 e.symm
  · intro i j
    by_cases eq : i = j
    · subst j; simp [edge, extendEdge]
    · by_cases lt : j.val < i.val
      · exact (row lt).2
      · rw [edge_comm, extend_comm]
        exact (row (i := j) (j := i) (by have ne := fun h => eq (Fin.ext h); omega)).2

end Ramsey556.Cert16
