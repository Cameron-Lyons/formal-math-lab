import Ramsey556.NearBipartite

namespace Ramsey556

/-- Any list of 32 vertices of K₃₃ misses a vertex. -/
theorem missingVertex (v : Fin 32 → Fin 33) : ∃ z, ∀ i, v i ≠ z := by
  classical
  apply Classical.byContradiction
  intro h
  have covers : List.finRange 33 ⊆ (List.finRange 32).map v := by
    intro z _
    apply Classical.byContradiction
    intro hm
    apply h
    exact ⟨z, fun i h => hm (List.mem_map.mpr ⟨i, List.mem_finRange i, h⟩)⟩
  have impossible := (List.nodup_finRange 33).length_le_of_subset covers
  simp at impossible

private def nameColors (r s x : Fin 3) : Fin 3 :=
  if x = r then 0 else if x = s then 1 else 2

/-- If two distinct colors are bipartite on the same 32 vertices of K₃₃, the
full coloring has a monochromatic nine-cycle. The edges to the omitted vertex
are arbitrary. -/
theorem hasMonoC9_of_two_bipartite_on_32 (c : Coloring 33) (v : Fin 32 → Fin 33)
    (hv : ∀ ⦃i j⦄, v i = v j → i = j) {r s : Fin 3} (hrs : r ≠ s)
    (hr : IsBipartiteColor (c.induce v) r) (hs : IsBipartiteColor (c.induce v) s) :
    HasMonoC9 c := by
  obtain ⟨z, hz⟩ := missingVertex v
  let w : Fin 33 → Fin 33 := Fin.lastCases z v
  have hw : ∀ ⦃i j⦄, w i = w j → i = j := by
    intro i j
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp only [w,
      Fin.lastCases_last, Fin.lastCases_castSucc, Fin.castSucc_inj]
    · exact id
    · exact fun h => (hz _ h.symm).elim
    · exact fun h => (hz _ h).elim
    · exact fun h => hv h
  have perm : ∀ (r s : Fin 3), r ≠ s → ∀ i j, nameColors r s i = nameColors r s j → i = j := by
    decide
  have hperm : ∀ ⦃i j⦄, nameColors r s i = nameColors r s j → i = j := fun {_ _} => perm _ _ hrs _ _
  let d := (c.induce w).recolor (nameColors r s)
  have old (u v' : Fin 32) : (dropLast d).edge u v' = nameColors r s ((c.induce v).edge u v') := by
    simp [d, dropLast, Coloring.induce, Coloring.recolor, w]
  apply hasMonoC9_of_copy c w (nameColors r s) hw hperm
  apply hasMonoC9_of_bipartite_dropLast d
  · obtain ⟨side, hside⟩ := hr
    refine ⟨side, fun u v' hne he => hside u v' hne (hperm ?_)⟩
    rw [← old]
    simpa [nameColors] using he
  · obtain ⟨side, hside⟩ := hs
    refine ⟨side, fun u v' hne he => hside u v' hne (hperm ?_)⟩
    rw [← old]
    simpa [nameColors, Ne.symm hrs] using he

end Ramsey556
