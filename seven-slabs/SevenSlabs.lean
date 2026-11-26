module

public import SevenSlabs.AxisAligned
public import SevenSlabs.Frame
public import SevenSlabs.Alignment
public import Mathlib.Data.List.OfFn

/-! Seven slabs cannot tile a cube. The main theorem is `SevenSlabs.no_seven_slab_tiling`.
It starts from arbitrary real positions and rotations, a set-theoretic cover, and
pairwise disjoint interiors. The finite check is in `SevenSlabs.Discrete`. -/

@[expose] public section

namespace SevenSlabs

open FaceGeometry

/-- The closed cube in ordinary Euclidean coordinates. -/
def cube (s : ℝ) : Set Point := Set.Icc (fun _ => 0) (fun _ => s)

/-- Exact geometric tiling: the union is the cube, and distinct tiles have
disjoint interiors. The coordinate frame of each cuboid is independent. -/
structure FillsCube (s : ℝ) (tiles : Fin 7 → Cuboid) : Prop where
  cover : cube s = ⋃ i, (tiles i).body
  disjoint : ∀ i j, i ≠ j → Disjoint (interior (tiles i).body) (interior (tiles j).body)

private theorem frames_tile {s : ℝ} {tiles : Fin 7 → Cuboid}
    (t : ∀ i, SignedFrame (tiles i)) (pos : ∀ i j, 0 < (tiles i).length j)
    (h : FillsCube s tiles) : ClosedTiling s (List.ofFn fun i => (t i).box) := by
  have sub (i : Fin 7) : (tiles i).body ⊆ cube s := by
    rw [h.cover]
    exact Set.subset_iUnion (fun j => (tiles j).body) i
  constructor
  · intro b hb a
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    simpa [SignedFrame.box] using pos i ((t i).axes.symm (finOfAxis a))
  · intro b hb a
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    exact ((t i).cube_bounds (sub i) a).1
  · intro b hb a
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    exact ((t i).cube_bounds (sub i) a).2
  · intro p hp
    let q : Point := fun j => p (axisOfFin j)
    have inside : q ∈ cube s := ⟨fun j => (hp (axisOfFin j)).1, fun j => (hp (axisOfFin j)).2⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (h.cover ▸ inside : q ∈ ⋃ i, (tiles i).body)
    exact ⟨_, List.mem_ofFn.mpr ⟨i,rfl⟩, by simpa [q] using ((t i).closed_iff q).mp hi⟩
  · apply List.pairwise_ofFn.mpr
    intro i j hij p hi hj
    let q : Point := fun z => p (axisOfFin z)
    have interior_mem (u : Fin 7)
        (hu : ∀ a, (t u).box.lo a < p a ∧ p a < (t u).box.lo a + (t u).box.size.along a) :
        q ∈ interior (tiles u).body := by
      rw [(tiles u).interior_body, (t u).open_iff]
      simpa [q] using hu
    exact Set.disjoint_left.mp (h.disjoint i j (ne_of_lt hij)) (interior_mem i hi) (interior_mem j hj)

private theorem orders_of_seven {boxes : Fin 7 → RealBox}
    (h : ∀ i : Fin 7, IsSlab (i.val+1) (boxes i).size) :
    SlabOrders [1,2,3,4,5,6,7] ((List.ofFn boxes).map RealBox.size) := by
  rw [List.map_ofFn]
  exact ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6, trivial⟩

/-- One rectangular slab of each order 1 to 7 cannot tile a cube, even with
arbitrary rotations, translations, and real cube side length. -/
theorem no_seven_slab_tiling (s : ℝ) (tiles : Fin 7 → Cuboid)
    (slabs : ∀ i, IsSlab (i.val + 1) (tripleOf (tiles i).length)) : ¬ FillsCube s tiles := by
  intro tiling
  have pos i := Cuboid.length_pos_of_slab (slabs i)
  have aligned := cuboid_alignment s tiles pos tiling.cover tiling.disjoint
  let frames i := Classical.choice (Cuboid.signed_frame (aligned i))
  have orders := orders_of_seven (fun i => (frames i).isSlab (slabs i))
  exact seven_slabs_cannot_tile_real_cube s _ orders (frames_tile frames pos tiling)

end SevenSlabs
