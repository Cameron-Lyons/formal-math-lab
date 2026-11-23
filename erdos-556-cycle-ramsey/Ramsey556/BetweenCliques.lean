import Ramsey556.Extension

namespace Ramsey556

/-- Relabel an octet so that the first and last positions can be prescribed. -/
private def swapIndex (a b x : Fin 8) : Fin 8 :=
  if x = a then b else if x = b then a else x

private def orderOctet (a b i : Fin 8) : Fin 8 :=
  swapIndex 0 a (swapIndex 7 (swapIndex 0 a b) i)

private theorem order_spec : ∀ a b : Fin 8, a ≠ b →
    orderOctet a b 0 = a ∧ orderOctet a b 7 = b ∧
    ∀ i j, orderOctet a b i = orderOctet a b j → i = j := by decide

/-- A vertex outside a monochromatic eight-clique can meet it in its own
color at most once if the coloring avoids a monochromatic nine-cycle. -/
theorem clique_spokes_unique {n : Nat} (c : Coloring n) (k : Fin 3)
    (A : Fin 8 → Fin n) (z : Fin n)
    (hA : ∀ ⦃i j⦄, A i = A j → i = j) (disj : ∀ i, A i ≠ z)
    (inside : ∀ i j, i ≠ j → c.edge (A i) (A j) = k)
    (free : ¬ HasMonoC9 c) {a b : Fin 8}
    (e : c.edge z (A a) = k) (e' : c.edge z (A b) = k) : a = b := by
  apply Classical.byContradiction
  intro different
  obtain ⟨first, last, injective⟩ := order_spec a b different
  apply free
  apply closeC9Through c k (fun i => A (orderOctet a b i)) z
  · exact fun {_ _} h => injective _ _ (hA h)
  · exact fun _ => disj _
  · intro i h
    apply inside
    intro eq
    have := congrArg Fin.val (injective _ _ eq)
    simp at this
  · simpa only [first] using e
  · simpa only [last] using e'

/-- In a coloring with no monochromatic C₉, two disjoint K₈'s of the
same color have at most one edge of that color between them. This gives
uniqueness at the first end. Interchanging the cliques gives the other end. -/
theorem clique_cross_unique {n : Nat} (c : Coloring n) (k : Fin 3) (A B : Fin 8 → Fin n)
    (hA : ∀ ⦃i j⦄, A i = A j → i = j) (hB : ∀ ⦃i j⦄, B i = B j → i = j)
    (disj : ∀ i j, A i ≠ B j)
    (insideA : ∀ i j, i ≠ j → c.edge (A i) (A j) = k)
    (insideB : ∀ i j, i ≠ j → c.edge (B i) (B j) = k)
    (free : ¬ HasMonoC9 c) {a a' b b' : Fin 8}
    (e : c.edge (A a) (B b) = k) (e' : c.edge (A a') (B b') = k) : a = a' := by
  apply Classical.byContradiction
  intro different
  obtain ⟨first, last, injective⟩ := order_spec a a' different
  apply free
  by_cases same : b = b'
  · -- The common endpoint closes a Hamiltonian path through A.
    subst b'
    have unique := clique_spokes_unique c k A (B b) hA (fun i => disj i b) insideA free
      (c.symm _ _ |>.trans e) (c.symm _ _ |>.trans e')
    exact False.elim (different unique)
  · -- Use seven vertices of A, the two cross edges, and the edge inside B.
    let q (i : Fin 7) : Fin 8 := if i = 6 then 7 else i.castSucc
    have iq : ∀ i j, q i = q j → i = j := by decide
    let p : Fin 8 → Fin n := Fin.lastCases (B b') (fun i => A (orderOctet a a' (q i)))
    apply closeC9Through c k p (B b)
    · intro i j
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · exact fun _ => rfl
      · intro h
        exact (disj _ _ (by simpa only [p, Fin.lastCases_last, Fin.lastCases_castSucc] using h.symm)).elim
      · intro h
        exact (disj _ _ (by simpa only [p, Fin.lastCases_last, Fin.lastCases_castSucc] using h)).elim
      · intro h
        simp only [p, Fin.lastCases_castSucc] at h
        exact congrArg Fin.castSucc (iq _ _ (injective _ _ (hA h)))
    · intro i
      induction i using Fin.lastCases with
      | last => exact fun h => same ((hB (by simpa only [p, Fin.lastCases_last] using h)).symm)
      | cast i => simpa only [p, Fin.lastCases_castSucc] using disj (orderOctet a a' (q i)) b
    · intro i hi
      by_cases h : i.val < 6
      · let u : Fin 7 := ⟨i.val, by omega⟩
        let v : Fin 7 := ⟨i.val + 1, by omega⟩
        change c.edge (p u.castSucc) (p v.castSucc) = k
        simp only [p, Fin.lastCases_castSucc]
        apply insideA
        intro eq
        have := congrArg Fin.val (iq _ _ (injective _ _ eq))
        simp [u, v] at this
      · have hi6 : i = 6 := Fin.ext (by change i.val = 6; omega)
        subst i
        change c.edge (p (6 : Fin 7).castSucc) (p (Fin.last 7)) = k
        simpa only [p, Fin.lastCases_castSucc, Fin.lastCases_last, show q 6 = 7 by decide, last] using e'
    · change c.edge (B b) (p (0 : Fin 7).castSucc) = k
      rw [c.symm]
      simpa only [p, Fin.lastCases_castSucc, show q 0 = 0 by decide, first] using e
    · change c.edge (B b) (p (Fin.last 7)) = k
      simpa only [p, Fin.lastCases_last] using insideB b b' same

end Ramsey556
