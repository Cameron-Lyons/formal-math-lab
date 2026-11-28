import ExactSymmetry

/-! Two corollaries of `ExactSymmetry.stabilizer_trivial`: a valid board has twelve distinct
images, and so a count of one board from each orbit must be multiplied by twelve. -/
namespace TBoards.ExactOrbit

/-- The twelve images of a valid board under the six color permutations and horizontal
reflection are pairwise different valid boards. -/
theorem twelve_distinct_images {b : Board} (h : Valid b) :
    (orbit b).length = 12 ∧ (orbit b).Nodup ∧ ∀ c ∈ orbit b, Valid c := by
  have valid : ∀ c ∈ orbit b, Valid c :=
    orbit_valid_of_valid_and_reverse h (Splice.valid_reverse h)
  -- The images are those under the twelve actions `(p, r)`: recolor by `p`, and reflect if `r`.
  rw [show orbit b = Splice.actions.map fun g => transform b g.1 g.2 from rfl] at valid ⊢
  -- Two different actions `(p, r)`, `(q, s)` differ by a nonidentity action `(u, r != s)`:
  -- recoloring by `p` and then by `u` is recoloring by `q`.
  have differ : Splice.actions.Pairwise fun (p, r) (q, s) => ∃ u ∈ colorPermutations,
      (∀ c < 3, u.getD (p.getD c 0) 0 = q.getD c 0) ∧
      ¬(u = [0,1,2] ∧ (r != s) = false) := by decide
  -- It remains to show that different actions give different images.
  refine ⟨rfl, List.pairwise_map.mpr (differ.imp_of_mem ?_), valid⟩
  intro (p, r) (q, s) hmem _ ⟨u, hu, comp, nontrivial⟩ (equal : transform b p r = transform b q s)
  -- Every color of `b` is below 3, so `(u, r != s)` carries the first image to the second.
  have cells : ∀ row ∈ b, ∀ c ∈ row, u.getD (p.getD c 0) 0 = q.getD c 0 :=
    fun row hrow c hc => comp c (h.1.2.2 row hrow c hc)
  have step : transform (transform b p r) u (r != s) = transform b q s := by
    cases r <;> cases s <;> simpa [transform] using cells
  -- If the images were equal, `(u, r != s)` would fix the first one, which is a valid board.
  have image_valid : Valid (transform b p r) := valid _ (List.mem_map_of_mem hmem)
  exact nontrivial (ExactSymmetry.stabilizer_trivial image_valid hu _ (step.trans equal.symm))

/-- If `d` is one of the twelve images of a valid board `b`, then `b` is one of those of `d`. -/
theorem orbit_symm {b d : Board} (h : Valid b) (hd : d ∈ orbit b) : b ∈ orbit d := by
  have mem (x y : Board) : y ∈ orbit x ↔ ∃ p ∈ colorPermutations, ∃ r, y = transform x p r := by
    simp [orbit]
  -- So `d` is `b` recolored by a palette `p`, and reflected if `r`. Some palette `q` undoes `p`.
  obtain ⟨p, hp, r, rfl⟩ := (mem b d).mp hd
  obtain ⟨q, hq, -, -, inverse, -⟩ := colorPermutations_have_inverse p hp
  have undo : ∀ c < 3, q.getD (p.getD c 0) 0 = c := fun c hc => inverse ⟨c, hc⟩
  -- Every color of `b` is below 3, so recoloring by `q` with the same reflection gives back `b`.
  have rows : ∀ row ∈ b, row.map (fun c => q.getD (p.getD c 0) 0) = row := fun row hrow =>
    (List.map_congr_left fun c hc => undo c (h.1.2.2 row hrow c hc)).trans (List.map_id' row)
  have back : transform (transform b p r) q r = b := by
    cases r <;> simpa [transform, Function.comp_def] using List.map_congr_left rows
  exact (mem (transform b p r) b).mpr ⟨q, hq, r, back.symm⟩

/-- A duplicate-free list of valid boards that contains all twelve images of each of its boards
is twelve times as long as its sublist of boards selected by `canon`, provided `canon` selects
exactly one of the twelve images of each board. -/
theorem length_eq_twelve_mul_canonical {L : List Board} (hn : L.Nodup)
    (hv : ∀ b ∈ L, Valid b) (hcl : ∀ b ∈ L, ∀ c ∈ orbit b, c ∈ L) (canon : Board → Bool)
    (hone : ∀ b ∈ L, ((orbit b).filter canon).length = 1) :
    L.length = 12 * (L.filter canon).length := by
  -- The selected images of a board `x` of `L` are a single board `a`.
  have rep : ∀ x ∈ L, ∃ a, ∀ c, (c ∈ orbit x ∧ canon c = true) ↔ c = a := by
    intro x hx
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (hone x hx)
    refine ⟨a, fun c => ?_⟩
    rw [← List.mem_filter, ha, List.mem_singleton]
  -- List the orbits of the selected boards one after another. No board is listed twice.
  have nodup : ((L.filter canon).flatMap orbit).Nodup := by
    refine List.pairwise_flatMap.mpr ⟨?_, (hn.filter canon).imp_of_mem ?_⟩
    · exact fun c hc => (twelve_distinct_images (hv c (List.mem_filter.mp hc).1)).2.1
    · -- Two selected boards `c`, `d` with a common image `x` are both the selected image of `x`.
      rintro c d hc hd hne x hxc _ hxd rfl
      rw [List.mem_filter] at hc hd
      obtain ⟨a, only⟩ := rep x (hcl c hc.1 x hxc)
      have hca : c = a := (only c).mp ⟨orbit_symm (hv c hc.1) hxc, hc.2⟩
      have hda : d = a := (only d).mp ⟨orbit_symm (hv d hd.1) hxd, hd.2⟩
      exact hne (hca.trans hda.symm)
  -- The boards listed are exactly the boards of `L`.
  have same (x : Board) : x ∈ L ↔ x ∈ (L.filter canon).flatMap orbit := by
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · -- `x` is an image of its selected image `a`, which is in `L`.
      obtain ⟨a, only⟩ := rep x hx
      obtain ⟨hax, hacanon⟩ := (only a).mpr rfl
      have ha : a ∈ L.filter canon := List.mem_filter.mpr ⟨hcl x hx a hax, hacanon⟩
      exact List.mem_flatMap.mpr ⟨a, ha, orbit_symm (hv x hx) hax⟩
    · obtain ⟨c, hc, hxc⟩ := List.mem_flatMap.mp hx
      exact hcl c (List.mem_filter.mp hc).1 x hxc
  -- So `L` is a rearrangement of that list, in which each orbit lists twelve boards.
  have perm : L.Perm ((L.filter canon).flatMap orbit) :=
    (List.perm_ext_iff_of_nodup hn nodup).mpr same
  calc L.length
    _ = ((L.filter canon).flatMap orbit).length := perm.length_eq
    _ = ((L.filter canon).map fun c => (orbit c).length).sum := List.length_flatMap
    _ = ((L.filter canon).map fun _ => 12).sum := rfl
    _ = 12 * (L.filter canon).length := by
      rw [List.map_const', List.sum_replicate_nat, Nat.mul_comm]

end TBoards.ExactOrbit

#print axioms TBoards.ExactOrbit.twelve_distinct_images
#print axioms TBoards.ExactOrbit.length_eq_twelve_mul_canonical
