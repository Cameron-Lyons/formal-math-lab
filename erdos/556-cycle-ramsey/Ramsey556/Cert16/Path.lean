import Ramsey556.Cert16.Basic

namespace Ramsey556.Cert16
/-- Vertex at position `i` of the path stored in four-bit fields. -/
private def vertex (code i : Nat) : Nat := (code >>> (4*i)) &&& 15

/-- Check successive vertices, marking each in a bit set to enforce injectivity. -/
private def walk (n g code : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | i+1, seen =>
    let a := vertex code i
    a < n && !seen.testBit a && (i == 0 || edge g (vertex code (i-1)) a) &&
      walk n g code i (seen ||| (1 <<< a))

def pathOK (n g x y code : Nat) : Bool :=
  vertex code 0 == x && vertex code 7 == y && walk n g code 8 0

private theorem walk_spec {n g c len seen : Nat} (ok : walk n g c len seen = true) :
    (∀ i, i < len → vertex c i < n ∧ seen.testBit (vertex c i) = false) ∧
    (∀ i j, i < j → j < len → vertex c i ≠ vertex c j) ∧
    (∀ i, i+1 < len → edge g (vertex c i) (vertex c (i+1)) = true) := by
  induction len generalizing seen with
  | zero => exact ⟨by omega, by omega, by omega⟩
  | succ k ih =>
    simp only [walk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.or_eq_true,
      beq_iff_eq] at ok
    obtain ⟨⟨⟨small, fresh⟩, adj⟩, tail⟩ := ok
    obtain ⟨bounds, distinct, consecutive⟩ := ih tail
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      by_cases e : i = k
      · simpa [e] using And.intro small fresh
      · obtain ⟨b, old⟩ := bounds i (by omega)
        rw [Nat.testBit_or, Bool.or_eq_false_iff] at old
        exact ⟨b,old.1⟩
    · intro i j hi hj
      by_cases e : j = k
      · subst j
        intro eq
        have f := (bounds i hi).2
        rw [eq, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow_self] at f
        simp at f
      · exact distinct i j hi (by omega)
    · intro i hi
      by_cases e : i+1 = k
      · subst k
        exact adj.resolve_left (by omega)
      · exact consecutive i (by omega)

theorem pathOK_safe {n g m x y code : Nat} (hp : pathOK n g x y code = true)
    (safe : Safe n g m) (hx : m.testBit x = true) (hy : m.testBit y = true) : False := by
  simp only [pathOK, Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨h0,h7⟩, ok⟩ := hp
  obtain ⟨bounds,distinct,adj⟩ := walk_spec ok
  let p (i : Fin 8) : Fin n := ⟨vertex code i.val,(bounds i.val i.isLt).1⟩
  have inj : ∀ ⦃i j⦄, p i = p j → i = j := by
    intro i j eq
    have eq' : vertex code i.val = vertex code j.val := congrArg Fin.val eq
    rcases Nat.lt_trichotomy i.val j.val with lt|e|gt
    · exact (distinct _ _ lt j.isLt eq').elim
    · exact Fin.ext e
    · exact (distinct _ _ gt i.isLt eq'.symm).elim
  apply safe p inj _ (by change m.testBit (vertex code 0) = true; rwa [h0])
    (by change m.testBit (vertex code 7) = true; rwa [h7])
  intro i
  change edge g (vertex code i.val) (vertex code (i.val+1)) = true
  exact adj i.val (by omega)

end Ramsey556.Cert16
