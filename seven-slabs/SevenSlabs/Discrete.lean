module

public import SevenSlabs.Grid
public import SlabSearch.Enumerate
public import SlabSearch.Sections
meta import SlabSearch.Sections
meta import SlabSearch.Enumerate

/-! The computational core. The volume bound reduces the problem to sides at most 28. -/

@[expose] public section

namespace SevenSlabs

private theorem volume_bound {n k : Nat} {s : Shape} (h : s.Valid n k) :
    s.vol ≤ k * (n*n) := by
  obtain ⟨hk, _, _, hab, hbn, _, _⟩ := h
  have han := Nat.le_trans hab hbn
  simpa [Shape.vol, hk, Nat.mul_assoc] using
    Nat.mul_le_mul_left k (Nat.mul_le_mul han hbn)

private theorem total_bound {n : Nat} {ks : List Nat} {ss : List Shape}
    (h : LegalShapes n ks ss) : (ss.map Shape.vol).sum ≤ ks.sum * (n*n) := by
  induction ks generalizing ss with
  | nil => cases ss <;> simp_all [LegalShapes]
  | cons k ks ih =>
    cases ss with
    | nil => contradiction
    | cons s ss =>
      obtain ⟨h₁, h₂⟩ := h
      simpa only [List.map_cons, List.sum_cons, Nat.add_mul] using
        Nat.add_le_add (volume_bound h₁) (ih h₂)

theorem side_bound {n : Nat} {ss : List Shape}
    (h : LegalShapes n [1,2,3,4,5,6,7] ss) (v : (ss.map Shape.vol).sum = n^3) :
    0 < n ∧ n ≤ 28 := by
  have hn : 0 < n := by
    cases ss with
    | nil => contradiction
    | cons s ss =>
      obtain ⟨hk, _, hka, hab, hbn, _, _⟩ := h.1
      omega
  have hbound := total_bound h
  rw [v] at hbound
  change n^3 ≤ 28 * (n*n) at hbound
  have hcancel : n * (n*n) ≤ 28 * (n*n) := by simpa [Nat.pow_succ, Nat.mul_assoc] using hbound
  exact ⟨hn, Nat.le_of_mul_le_mul_right hcancel (Nat.mul_pos hn hn)⟩

theorem oriented_volume {s : Shape} {d : Triple} (h : d ∈ s.orientations) :
    s.vol = d.vol := by
  simp [Shape.orientations] at h
  rcases h with h | h | h | h | h | h <;> subst d <;>
    simp [Shape.vol, Triple.vol, Nat.mul_comm, Nat.mul_left_comm]

private theorem Matches.volume_eq {ss bs} (h : Matches ss bs) :
    (ss.map Shape.vol).sum = (bs.map (fun b : Box => b.size.vol)).sum := by
  induction h with
  | nil => rfl
  | cons hor _ ih => simp only [List.map_cons, List.sum_cons, ih, oriented_volume hor]

/-- The only computational step. Every volume-compatible tuple fails the axis tests. -/
private theorem finite_check :
    (List.range 29).all (fun n => (volumeShapes n).all (fun ss => !checkShapes n ss)) = true := by
  native_decide

/-- A partition into one slab of each order 1 through 7, allowing all axis permutations. -/
def SevenSlabsTile (n : Nat) : Prop :=
  ∃ (ss : List Shape) (bs : List Box),
    LegalShapes n [1,2,3,4,5,6,7] ss ∧ Matches ss bs ∧ Tiling n bs

/-- No cube of any side can be tiled by the seven slabs. -/
theorem seven_slabs_cannot_tile (n : Nat) : ¬ SevenSlabsTile n := by
  rintro ⟨ss, bs, legal, placed, tiled⟩
  have volume : (ss.map Shape.vol).sum = n^3 := by
    rw [placed.volume_eq, tiled.volume]
    simp [Nat.pow_succ]
  obtain ⟨hn, bound⟩ := side_bound legal volume
  have impossible := all_volumeShapes finite_check bound (mem_volumeShapes_of_legal legal volume)
  have necessary := checkShapes_of_boxes placed (tiled.oppositeFaces hn) tiled.lineThrough
  simp [necessary] at impossible

end SevenSlabs
