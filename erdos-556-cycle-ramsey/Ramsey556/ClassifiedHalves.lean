import Ramsey556.AlignedOctets
import Ramsey556.Deletion
import Ramsey556.MixedOctets
import Ramsey556.TwoColor

namespace Ramsey556

/-- Two two-colored halves of K₃₃ − z, each expressed as a pair of disjoint
monochromatic octets. Each half may choose its own octet color. -/
structure ClassifiedHalves (c : Coloring 33) (z : Fin 33) where
  color : Fin 2 → Fin 3
  nonzero : ∀ h, color h ≠ 0
  vertex : Fin 2 → Fin 2 → Fin 8 → Fin 33
  inj : ∀ ⦃h g a b i j⦄, vertex h a i = vertex g b j → h = g ∧ a = b ∧ i = j
  away : ∀ h a i, vertex h a i ≠ z
  inside : ∀ h a i j, i ≠ j → c.edge (vertex h a i) (vertex h a j) = color h
  between : ∀ h, ∃ u v : Fin 8, ∀ i j, (i,j) ≠ (u,v) →
    c.edge (vertex h 0 i) (vertex h 1 j) = otherNonzero (color h)
  noZero : ∀ h a b i j, (a,i) ≠ (b,j) → c.edge (vertex h a i) (vertex h b j) ≠ 0

namespace ClassifiedHalves

private def rename (k x : Fin 3) : Fin 3 := if x = 0 then 0 else if x = k then 2 else 1

private theorem rename_inj : ∀ k : Fin 3, k ≠ 0 →
    ∀ x y, rename k x = rename k y → x = y := by decide

private theorem nonzero_names : ∀ k : Fin 3, k ≠ 0 →
    rename k k = 2 ∧ rename k (otherNonzero k) = 1 := by decide

private def unpack (u : Fin 32) : Fin 2 × Fin 2 × Fin 8 :=
  (⟨u.val / 16, by omega⟩, ⟨u.val / 8 % 2, by omega⟩, ⟨u.val % 8, by omega⟩)

private def half (b : Fin 4) : Fin 2 := ⟨b.val / 2, by omega⟩
private def side (b : Fin 4) : Fin 2 := ⟨b.val % 2, by omega⟩

private theorem unpack_sq : ∀ b i, unpack (squareVertex b i) = (half b, side b, i) := by decide

/-- In the aligned case normalize the crossing color to 1 and read the 32
vertices in square order. The aligned-octet theorem gives a second bipartition. -/
private theorem alignedCase (c : Coloring 33) (z : Fin 33) (S : ClassifiedHalves c z)
    (same : ∀ h, S.color h = S.color 0) : HasMonoC9 c := by
  classical
  let g := rename (S.color 0)
  have hg : ∀ ⦃i j⦄, g i = g j → i = j := fun {_ _} => rename_inj _ (S.nonzero 0) _ _
  have names := nonzero_names _ (S.nonzero 0)
  let old (u : Fin 32) := S.vertex (unpack u).1 (unpack u).2.1 (unpack u).2.2
  have uninj : ∀ i j, unpack i = unpack j → i = j := by decide
  have hi : ∀ ⦃u v⦄, old u = old v → u = v := by
    intro u v e
    obtain ⟨a, b, d⟩ := S.inj e
    exact uninj _ _ (Prod.ext a (Prod.ext b d))
  let d := c.recolor g
  let q := d.induce old
  have oldSq (b i) : old (squareVertex b i) = S.vertex (half b) (side b) i := by
    simp only [old, unpack_sq]
  have edge (a b i j) :
      q.edge (squareVertex a i) (squareVertex b j) =
        g (c.edge (S.vertex (half a) (side a) i) (S.vertex (half b) (side b) j)) := by
    change g (c.edge (old _) (old _)) = _
    rw [oldSq, oldSq]
  have noRed : IsBipartiteColor q 0 := by
    refine ⟨fun u => decide ((unpack u).1 = 0), ?_⟩
    intro u v ne e eq
    have boolInj : ∀ a b : Fin 2, decide (a = 0) = decide (b = 0) → a = b := by decide
    have h := boolInj _ _ eq
    have ds : (unpack u).2 ≠ (unpack v).2 := fun se => ne (uninj _ _ (Prod.ext h se))
    have nz := S.noZero (unpack v).1 (unpack u).2.1 (unpack v).2.1 _ _ ds
    apply nz
    change g (c.edge (S.vertex (unpack u).1 _ _) (S.vertex (unpack v).1 _ _)) = 0 at e
    rw [h] at e
    exact hg e
  have square : AlignedGreenHalves q := by
    constructor
    · intro b i j diff e
      rw [edge, S.inside _ _ _ _ diff, same] at e
      exact (by decide : (2 : Fin 3) ≠ 1) (names.1.symm.trans e)
    · let u (h) := (S.between h).choose
      let v (h) := (S.between h).choose_spec.choose
      have edgeAB (h) (i j) (ne : (i,j) ≠ (u h, v h)) :
          g (c.edge (S.vertex h 0 i) (S.vertex h 1 j)) = 1 := by
        rw [(S.between h).choose_spec.choose_spec i j ne, same]
        exact names.2
      let bad (b) := if side b = 0 then u (half b) else v (half b)
      refine ⟨bad, ?_⟩
      intro a b i j diff sameHalf allowed
      have hab : half a = half b := Fin.ext sameHalf
      have sides : ∀ a b : Fin 4, a ≠ b → half a = half b →
          (side a = 0 ∧ side b = 1) ∨ (side a = 1 ∧ side b = 0) := by decide
      rcases sides _ _ diff hab with ⟨sa, sb⟩ | ⟨sa, sb⟩
      · rw [edge, hab, sa, sb]
        apply edgeAB
        intro e
        rcases allowed with left | right
        · apply left
          simpa [bad, sa, hab] using congrArg Prod.fst e
        · apply right
          simpa [bad, sb] using congrArg Prod.snd e
      · rw [edge, hab, sa, sb, c.symm]
        apply edgeAB
        intro e
        rcases allowed with left | right
        · apply left
          simpa [bad, sa, hab] using congrArg Prod.snd e
        · apply right
          simpa [bad, sb] using congrArg Prod.fst e
  by_cases free : HasMonoC9 q
  · exact hasMonoC9_of_copy c old g hi hg free
  · have green := aligned_halves_bipartite q square free
    have on33 := hasMonoC9_of_two_bipartite_on_32 d old hi (by decide : (0 : Fin 3) ≠ 1) noRed green
    exact hasMonoC9_of_copy c id g (fun {_ _} e => e) hg on33

end ClassifiedHalves

/-- All one-vertex extensions of two classified halves contain a monochromatic C₉.
The cliques in the two halves can use the same or different colors. -/
theorem hasMonoC9_of_classifiedHalves (c : Coloring 33) (z : Fin 33) (S : ClassifiedHalves c z) :
    HasMonoC9 c := by
  by_cases h : S.color 0 = S.color 1
  · apply ClassifiedHalves.alignedCase c z S
    intro i
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl
    · rfl
    · exact h.symm
  · let g := ClassifiedHalves.rename (S.color 1)
    have hg : ∀ ⦃i j⦄, g i = g j → i = j :=
      fun {_ _} => ClassifiedHalves.rename_inj _ (S.nonzero 1) _ _
    have names : ∀ a b : Fin 3, a ≠ 0 → b ≠ 0 → a ≠ b →
        ClassifiedHalves.rename b a = 1 ∧ ClassifiedHalves.rename b b = 2 ∧
        ClassifiedHalves.rename b (otherNonzero a) = 2 ∧
        ClassifiedHalves.rename b (otherNonzero b) = 1 := by decide
    obtain ⟨hA, hB, hA', hB'⟩ := names _ _ (S.nonzero 0) (S.nonzero 1) h
    apply hasMonoC9_of_copy c id g (fun {_ _} e => e) hg
    apply hasMonoC9_of_mixedOctets _ z S.vertex S.inj S.away
    · intro h s i j ij
      change g (c.edge _ _) = _
      rw [S.inside _ _ _ _ ij]
      have cases : h = 0 ∨ h = 1 := by omega
      rcases cases with rfl | rfl
      · exact hA
      · exact hB
    · intro h
      obtain ⟨u, v, between⟩ := S.between h
      refine ⟨u, v, fun i j ne => ?_⟩
      change g (c.edge _ _) = _
      rw [between _ _ ne]
      have cases : h = 0 ∨ h = 1 := by omega
      rcases cases with rfl | rfl
      · exact hA'
      · exact hB'

end Ramsey556
