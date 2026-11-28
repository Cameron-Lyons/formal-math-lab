import Ramsey556.BetweenCliques

namespace Ramsey556

/-- Enumerate four slots, starting at `a`. The other three go clockwise or
counterclockwise from it, whichever keeps the exceptional slot out. -/
private def fourSlots (a exceptional : Fin 8) (i : Fin 4) : Fin 8 :=
  let step : Fin 8 := ⟨i.val, by omega⟩
  if exceptional = a + 1 ∨ exceptional = a + 2 ∨ exceptional = a + 3 then
    a - step
  else a + step

private theorem fourSlots_spec : ∀ a x : Fin 8,
    fourSlots a x 0 = a ∧
    (∀ i j, fourSlots a x i = fourSlots a x j → i = j) ∧
    ∀ i, i ≠ 0 → fourSlots a x i ≠ x := by decide

/-- Alternating positions in two octets. The two endpoints have slot 0 and
the interior positions have nonzero slots. -/
private def alternatingSlots : Vector (Fin 2 × Fin 4) 8 := #v[
  (0,0), (1,1), (0,1), (1,2), (0,2), (1,3), (0,3), (1,0)]

private theorem alternatingSlots_inj :
    ∀ i j : Fin 8, alternatingSlots[i] = alternatingSlots[j] → i = j := by decide

private theorem both_sides_close {n : Nat} (c : Coloring n) (z : Fin n)
    (A : Fin 2 → Fin 8 → Fin n) (l : Fin 3)
    (inj : ∀ ⦃s t i j⦄, A s i = A t j → s = t ∧ i = j)
    (away : ∀ s i, A s i ≠ z)
    (between : ∃ u v : Fin 8, ∀ i j, (i,j) ≠ (u,v) → c.edge (A 0 i) (A 1 j) = l)
    {a b : Fin 8} (ha : c.edge z (A 0 a) = l) (hb : c.edge z (A 1 b) = l) :
    HasMonoC9 c := by
  obtain ⟨u, v, between⟩ := between
  let slots (s : Fin 2) := if s = 0 then fourSlots a u else fourSlots b v
  let point (s : Fin 2) (i : Fin 4) := A s (slots s i)
  let p (i : Fin 8) := point alternatingSlots[i].1 alternatingSlots[i].2
  have si (s : Fin 2) (i j : Fin 4) (he : slots s i = slots s j) : i = j := by
    by_cases hs : s = 0
    · exact (fourSlots_spec a u).2.1 _ _ (by simpa [slots, hs] using he)
    · exact (fourSlots_spec b v).2.1 _ _ (by simpa [slots, hs] using he)
  have edge (i j : Fin 4) (good : i ≠ 0 ∨ j ≠ 0) :
      c.edge (point 0 i) (point 1 j) = l := by
    apply between
    rintro e
    rcases good with hi | hj
    · exact (fourSlots_spec a u).2.2 i hi (congrArg Prod.fst e)
    · exact (fourSlots_spec b v).2.2 j hj (congrArg Prod.snd e)
  apply closeC9Through c l p z
  · intro i j eq
    obtain ⟨hs, hi⟩ := inj eq
    have hindex : alternatingSlots[i].2 = alternatingSlots[j].2 :=
      si _ _ _ (by simpa only [hs] using hi)
    exact alternatingSlots_inj _ _ (Prod.ext hs hindex)
  · exact fun i => away _ _
  · intro i h
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact edge 0 1 (by decide)
    · exact (c.symm _ _).trans (edge 1 1 (by decide))
    · exact edge 1 2 (by decide)
    · exact (c.symm _ _).trans (edge 2 2 (by decide))
    · exact edge 2 3 (by decide)
    · exact (c.symm _ _).trans (edge 3 3 (by decide))
    · exact edge 3 0 (by decide)
  · change c.edge z (A 0 (fourSlots a u 0)) = l
    rwa [(fourSlots_spec a u).1]
  · change c.edge z (A 1 (fourSlots b v 0)) = l
    rwa [(fourSlots_spec b v).1]

/-- Avoid one marked slot in an eight-clique. -/
private def skipSlot (x : Fin 8) (i : Fin 7) : Fin 8 :=
  ⟨if i.val < x.val then i.val else i.val+1, by split <;> omega⟩

/-- One whole octet, except for at most one slot, has spokes in the third color. -/
theorem all_but_one_spokes_of_octet_pair {n : Nat} (c : Coloring n) (z : Fin n)
    (A : Fin 2 → Fin 8 → Fin n) (k l : Fin 3) (hk : k ≠ 0) (hl : l ≠ 0) (hkl : k ≠ l)
    (inj : ∀ ⦃s t i j⦄, A s i = A t j → s = t ∧ i = j) (away : ∀ s i, A s i ≠ z)
    (inside : ∀ s i j, i ≠ j → c.edge (A s i) (A s j) = k)
    (between : ∃ u v : Fin 8, ∀ i j, (i,j) ≠ (u,v) → c.edge (A 0 i) (A 1 j) = l)
    (free : ¬ HasMonoC9 c) :
    ∃ s x, ∀ i, i ≠ x → c.edge z (A s i) = 0 := by
  classical
  have missing : ∃ s : Fin 2, ∀ i, c.edge z (A s i) ≠ l := by
    by_cases ex : ∃ a, c.edge z (A 0 a) = l
    · obtain ⟨a, ha⟩ := ex
      exact ⟨1, fun b hb => free (both_sides_close c z A l inj away between ha hb)⟩
    · exact ⟨0, fun a ha => ex ⟨a, ha⟩⟩
  obtain ⟨s, noL⟩ := missing
  have exceptional : ∃ x, ∀ j, c.edge z (A s j) = k → j = x := by
    by_cases ex : ∃ a, c.edge z (A s a) = k
    · obtain ⟨a, ha⟩ := ex
      exact ⟨a, fun j hj => clique_spokes_unique c k (A s) z
        (fun {_ _} e => (inj e).2) (away s) (inside s) free hj ha⟩
    · exact ⟨0, fun j hj => (ex ⟨j, hj⟩).elim⟩
  obtain ⟨x, hx⟩ := exceptional
  refine ⟨s,x,?_⟩
  intro i ne
  have h1 := noL i
  have h2 : c.edge z (A s i) ≠ k := fun e => ne (hx i e)
  omega

/-- For two monochromatic eight-cliques, with all but one edge between them
in a second color, a new vertex must send at least seven edges of the third
color into a single clique or lie on a monochromatic nine-cycle. -/
theorem seven_spokes_of_octet_pair {n : Nat} (c : Coloring n) (z : Fin n)
    (A : Fin 2 → Fin 8 → Fin n) (k l : Fin 3) (hk : k ≠ 0) (hl : l ≠ 0) (hkl : k ≠ l)
    (inj : ∀ ⦃s t i j⦄, A s i = A t j → s = t ∧ i = j) (away : ∀ s i, A s i ≠ z)
    (inside : ∀ s i j, i ≠ j → c.edge (A s i) (A s j) = k)
    (between : ∃ u v : Fin 8, ∀ i j, (i,j) ≠ (u,v) → c.edge (A 0 i) (A 1 j) = l)
    (free : ¬ HasMonoC9 c) :
    ∃ (s : Fin 2) (f : Fin 7 → Fin 8),
      (∀ ⦃i j⦄, f i = f j → i = j) ∧ ∀ i, c.edge z (A s (f i)) = 0 := by
  classical
  obtain ⟨s,x,red⟩ := all_but_one_spokes_of_octet_pair c z A k l hk hl hkl inj away inside between free
  have skip : ∀ x : Fin 8, (∀ i j, skipSlot x i = skipSlot x j → i = j) ∧
      ∀ i, skipSlot x i ≠ x := by decide
  refine ⟨s, skipSlot x, fun {_ _} => (skip x).1 _ _, ?_⟩
  exact fun i => red _ ((skip x).2 i)

end Ramsey556
