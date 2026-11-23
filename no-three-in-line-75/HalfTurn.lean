import Grid75

namespace Grid75

/-- Half-turn about the center of the 75 by 75 grid. -/
def halfTurn (p : Point) : Point := (p.1.rev, p.2.rev)

@[simp] theorem halfTurn_halfTurn (p : Point) : halfTurn (halfTurn p) = p := by
  simp [halfTurn]

private theorem fixed_iff (p : Point) : halfTurn p = p ↔ p = (37, 37) := by
  rcases p with ⟨x, y⟩
  simp [halfTurn, Fin.ext_iff, Fin.rev]
  omega

private theorem rev_coord (i : Fin 75) : (i.rev.val : Int) = 74 - i.val := by
  simp [Fin.rev]
  omega

private theorem det_reflected (a b c : Point) :
    det (halfTurn a) b c = det a (halfTurn b) (halfTurn c) := by
  simp only [halfTurn, det, rev_coord]
  grind

private theorem det_antipodes (q p : Point) :
    det (halfTurn q) q p = det q p (halfTurn p) := by
  simp only [halfTurn, det, rev_coord]
  grind

/-- If one point extends a half-turn invariant set of at least two points,
its antipode gives a second simultaneous extension. -/
theorem halfTurn_complete_pair {s : List Point} {q : Point}
    (size : 2 ≤ s.length) (invariant : (s.map halfTurn).Perm s)
    (distinct : (q :: s).Nodup) (valid : NoThree (q :: s)) :
    (halfTurn q :: q :: s).Nodup ∧ NoThree (halfTurn q :: q :: s) := by
  obtain ⟨fresh, nd⟩ := List.nodup_cons.mp distinct
  have inv {p : Point} (hp : p ∈ s) : halfTurn p ∈ s :=
    invariant.mem_iff.mp (List.mem_map_of_mem hp)
  -- A selected fixed point would be collinear with every old antipodal pair.
  have noFixed {z : Point} (hz : z ∈ q :: s) : halfTurn z ≠ z := by
    intro fix
    have small : s ⊆ [z] := by
      intro p hp
      apply Classical.byContradiction
      intro eq
      have col : det z p (halfTurn p) = 0 := by rw [← det_antipodes, fix]; simp [det]
      apply valid.exclude_triple _ col hz (by simp [hp]) (by simp [inv hp])
      simp at eq ⊢
      grind [fixed_iff, halfTurn_halfTurn]
    have le := nd.length_le_of_subset small
    simp at le
    omega
  have admissible {a b : Point} (ha : a ∈ s) (hb : b ∈ s) (ne : a ≠ b) : det q a b ≠ 0 := by
    intro col
    apply valid.exclude_triple _ col (by simp) (by simp [ha]) (by simp [hb])
    simp [ne]; grind
  have mirrorFresh : halfTurn q ∉ s := fun h => fresh (by simpa using inv h)
  refine ⟨List.nodup_cons.mpr ⟨by simp [noFixed (by simp : q ∈ q :: s), mirrorFresh], distinct⟩, ?_⟩
  intro a b c sub
  cases sub with
  | cons _ sub => exact valid sub
  | cons_cons _ sub =>
    cases sub with
    | cons _ pair =>
      rw [det_reflected]
      have ne : b ≠ c := by simpa using pair.nodup nd
      exact admissible (inv (pair.subset (by simp))) (inv (pair.subset (by simp)))
        (fun h => ne (by simpa using congrArg halfTurn h))
    | cons_cons _ old =>
      have hc := old.subset (show c ∈ [c] by simp)
      rw [det_antipodes]
      exact admissible hc (inv hc) (noFixed (List.mem_cons_of_mem _ hc)).symm

/-- A valid 149-point extension of a half-turn invariant 148-point core
certifies the existence of 150 points on the same grid. -/
theorem achievable_150_of_halfTurn_extension {s : List Point} {q : Point}
    (size : s.length = 148) (invariant : (s.map halfTurn).Perm s)
    (distinct : (q :: s).Nodup) (valid : NoThree (q :: s)) : Achievable 150 := by
  obtain ⟨nd, nt⟩ := halfTurn_complete_pair (by omega) invariant distinct valid
  exact ⟨halfTurn q :: q :: s, by simp [size], nd, nt⟩

end Grid75
