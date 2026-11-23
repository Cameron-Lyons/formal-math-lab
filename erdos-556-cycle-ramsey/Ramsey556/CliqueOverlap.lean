import Ramsey556.BetweenCliques

namespace Ramsey556.CliqueOverlap

private structure Octet (c : Coloring 15) where
  vertex : Fin 8 → Fin 15
  inj : Function.Injective vertex
  color : Fin 3
  edges : ∀ i j, i ≠ j → c.edge (vertex i) (vertex j) = color

private abbrev Octet.sites {c} (A : Octet c) := (List.finRange 8).map A.vertex

private theorem Octet.atSite {c} (A : Octet c) (i) : A.vertex i ∈ A.sites :=
  List.mem_map_of_mem (List.mem_finRange i)

private theorem Octet.nodup {c} (A : Octet c) : A.sites.Nodup :=
  (List.nodup_finRange _).map _ (fun _ _ => A.inj.ne)

private theorem Octet.inside {c} (A : Octet c) {x y} (hx : x ∈ A.sites) (hy : y ∈ A.sites) (ne : x ≠ y) :
    c.edge x y = A.color := by
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hy
  exact A.edges _ _ (fun h => ne (congrArg _ h))

/-- If B has a vertex outside A, they cannot share two vertices. The common
edge would identify their colors, and the outside vertex would then have two
spokes of that color into A. -/
private theorem unique_shared {c} (free : ¬ HasMonoC9 c) (A B : Octet c) {z}
    (outside : z ∈ B.sites) (away : z ∉ A.sites) {i j : Fin 8}
    (hi : A.vertex i ∈ B.sites) (hj : A.vertex j ∈ B.sites) : i = j := by
  apply Classical.byContradiction
  intro ne
  have same := (B.inside hi hj (A.inj.ne ne)).symm.trans (A.edges i j ne)
  have avoids (i) : A.vertex i ≠ z := fun e => away (e ▸ A.atSite i)
  apply ne
  apply clique_spokes_unique c A.color A.vertex z A.inj avoids A.edges free
  · exact (B.inside outside hi (avoids i).symm).trans same
  · exact (B.inside outside hj (avoids j).symm).trans same

/-- Two lists of distinct vertices of total length greater than 15 must meet. -/
private theorem meet {xs ys : List (Fin 15)} (nx : xs.Nodup) (ny : ys.Nodup)
    (large : 15 < xs.length + ys.length) : ∃ z, z ∈ xs ∧ z ∈ ys := by
  apply Classical.byContradiction
  intro disjoint
  have distinct : (xs ++ ys).Nodup := List.pairwise_append.mpr
    ⟨nx,ny,fun x hx _ hy eq => disjoint ⟨x,hx,eq ▸ hy⟩⟩
  have bound := distinct.length_le_of_subset (l₂ := List.finRange 15) (fun {_} _ => List.mem_finRange _)
  simp at bound
  omega

/-- Two distinct octets meet once and cover every vertex. -/
private theorem cover {c} (free : ¬ HasMonoC9 c) (A B : Octet c) {w}
    (wa : w ∈ A.sites) (wb : w ∉ B.sites) :
    ∃ z, z ∈ A.sites ∧ z ∈ B.sites ∧ ∀ x, x ∈ A.sites ∨ x ∈ B.sites := by
  obtain ⟨z,za,zb⟩ := meet A.nodup B.nodup (by simp [Octet.sites])
  refine ⟨z,za,zb,fun x => ?_⟩
  by_cases xb : x ∈ B.sites
  · exact Or.inr xb
  -- Replace the common vertex by x in B. Any new intersection with A must be x.
  have distinct : (x :: B.sites.erase z).Nodup :=
    List.nodup_cons.mpr ⟨fun h => xb (List.mem_of_mem_erase h), B.nodup.erase _⟩
  obtain ⟨y,ya,hit⟩ := meet A.nodup distinct (by simp [List.length_erase_of_mem zb, Octet.sites])
  rcases List.mem_cons.mp hit with rfl | old
  · exact Or.inl ya
  · obtain ⟨ne,yb⟩ := B.nodup.mem_erase_iff.mp old
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp yb
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp zb
    exact (ne (congrArg B.vertex (unique_shared free B A wa wb ya za))).elim

/-- In a C₉-free coloring of fifteen vertices, one vertex belongs to every
monochromatic K₈. Deleting it therefore destroys every monochromatic K₈. -/
theorem hitting_vertex (c : Coloring 15) (free : ¬ HasMonoC9 c) :
    ∃ z, ∀ (k : Fin 3) (v : Fin 8 → Fin 15), Function.Injective v →
      (∀ i j, i ≠ j → c.edge (v i) (v j) = k) → ∃ i, v i = z := by
  suffices common : ∃ z, ∀ C : Octet c, z ∈ C.sites by
    obtain ⟨z,hits⟩ := common
    exact ⟨z,fun k v vi edges => by simpa [Octet.sites] using hits ⟨v,vi,k,edges⟩⟩
  apply Classical.byContradiction
  intro noCommon
  simp only [not_exists, Classical.not_forall] at noCommon
  obtain ⟨A,_⟩ := noCommon 0
  obtain ⟨B,avoids⟩ := noCommon (A.vertex 0)
  obtain ⟨z,za,zb,coverAll⟩ := cover free A B (A.atSite 0) avoids
  obtain ⟨C,miss⟩ := noCommon z
  have first := coverAll (C.vertex 0)
  have second := coverAll (C.vertex 1)
  have third := coverAll (C.vertex 2)
  grind only [unique_shared free C A za miss, unique_shared free C B zb miss]

end Ramsey556.CliqueOverlap
