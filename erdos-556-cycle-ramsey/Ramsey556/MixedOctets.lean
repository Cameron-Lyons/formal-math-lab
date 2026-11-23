import Ramsey556.OctetPair
import Ramsey556.DensePath

namespace Ramsey556

/-- Two pairs of octets with opposite internal colors. The crossing color in
each pair may have one exception. Edges between the two pairs and all edges at
`z` are arbitrary. -/
theorem hasMonoC9_of_mixedOctets {n : Nat} (c : Coloring n) (z : Fin n)
    (A : Fin 2 → Fin 2 → Fin 8 → Fin n)
    (inj : ∀ ⦃h g s t i j⦄, A h s i = A g t j → h = g ∧ s = t ∧ i = j)
    (away : ∀ h s i, A h s i ≠ z)
    (inside : ∀ (h s : Fin 2) (i j : Fin 8), i ≠ j →
      c.edge (A h s i) (A h s j) = if h = 0 then 1 else 2)
    (between : ∀ h : Fin 2, ∃ u v : Fin 8, ∀ i j, (i,j) ≠ (u,v) →
      c.edge (A h 0 i) (A h 1 j) = if h = 0 then 2 else 1) :
    HasMonoC9 c := by
  apply Classical.byContradiction
  intro free
  have injective (h : Fin 2) : ∀ ⦃s t i j⦄, A h s i = A h t j → s = t ∧ i = j :=
    fun {_ _ _ _} e => (inj e).2
  obtain ⟨s, f, hf, redA⟩ := seven_spokes_of_octet_pair c z (A 0) 1 2
    (by decide) (by decide) (by decide) (injective 0) (away 0)
    (inside 0) (between 0) free
  obtain ⟨t, g, hg, redB⟩ := seven_spokes_of_octet_pair c z (A 1) 2 1
    (by decide) (by decide) (by decide) (injective 1) (away 1)
    (inside 1) (between 1) free
  apply free
  apply dense_mixed_octets_cycle c (fun i => A 0 s (f i)) (fun j => A 1 t (g j)) z
    (fun {_ _} e => hf (inj e).2.2) (fun {_ _} e => hg (inj e).2.2)
    (fun _ _ e => (show (0 : Fin 2) ≠ 1 by decide) (inj e).1)
    (fun _ => away _ _ _) (fun _ => away _ _ _) redA redB
  · intro i i' j e e'
    apply hf
    exact clique_spokes_unique c 1 (A 0 s) (A 1 t (g j))
      (fun {_ _} eq => (inj eq).2.2) (fun _ eq => (show (0 : Fin 2) ≠ 1 by decide) (inj eq).1)
      (inside 0 s) free ((c.symm _ _).trans e) ((c.symm _ _).trans e')
  · intro i j j' e e'
    apply hg
    exact clique_spokes_unique c 2 (A 1 t) (A 0 s (f i))
      (fun {_ _} eq => (inj eq).2.2) (fun _ eq => (show (1 : Fin 2) ≠ 0 by decide) (inj eq).1)
      (inside 1 t) free e e'

end Ramsey556
