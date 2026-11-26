module

public import SevenSlabs.RealBoxes
public import SevenSlabs.Discrete

/-! From the physical edge lengths of a real slab to its canonical shape in the finite search. -/

@[expose] public section

namespace SevenSlabs

/-- An order-k slab has edge lengths k, k*u and k*v in any order. -/
def IsSlab (k : Nat) (d : Triple) : Prop :=
  0 < k ∧ ∃ u v : Nat, 0 < u ∧ 0 < v ∧ d ∈ (Shape.mk k (k*u) (k*v)).orientations

def SlabOrders : List Nat → List Triple → Prop
  | [], [] => True
  | k::ks, d::ds => IsSlab k d ∧ SlabOrders ks ds
  | _, _ => False

private theorem canonicalShape {k n : Nat} {d : Triple} (slab : IsSlab k d)
    (fits : ∀ a, d.along a ≤ n) : ∃ s : Shape, s.Valid n k ∧ d ∈ s.orientations := by
  obtain ⟨hk, u, v, hu, hv, hor⟩ := slab
  have sorted {p q : Nat} (hp : 0 < p) (hpq : p ≤ q)
      (h : d ∈ (Shape.mk k (k*p) (k*q)).orientations) :
      ∃ s : Shape, s.Valid n k ∧ d ∈ s.orientations := by
    have hq : k*q ≤ n := by
      have hx := fits .x
      have hy := fits .y
      have hz := fits .z
      simp only [Shape.orientations, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h | h | h <;> subst d <;> first | exact hx | exact hy | exact hz
    refine ⟨⟨k,k*p,k*q⟩, ⟨rfl, hk, ?_, Nat.mul_le_mul_left k hpq, hq, ⟨p,rfl⟩, ⟨q,rfl⟩⟩, h⟩
    simpa using Nat.mul_le_mul_left k (show 1 ≤ p from hp)
  by_cases huv : u ≤ v
  · exact sorted hu huv hor
  · apply sorted hv (Nat.le_of_not_ge huv)
    simpa [Shape.orientations, or_assoc, or_comm, or_left_comm] using hor

private theorem canonicalList {n : Nat} {ks : List Nat} {bs : List Box}
    (orders : SlabOrders ks (bs.map Box.size))
    (fits : ∀ b ∈ bs, ∀ a, b.size.along a ≤ n) :
    ∃ ss, LegalShapes n ks ss ∧ Matches ss bs := by
  induction ks generalizing bs with
  | nil =>
    cases bs with
    | nil => exact ⟨[], trivial, .nil⟩
    | cons => contradiction
  | cons k ks ih =>
    cases bs with
    | nil => contradiction
    | cons b bs =>
      obtain ⟨s, legal, pos⟩ := canonicalShape orders.1 (fits b (by simp))
      obtain ⟨ss, tailLegal, tailPos⟩ := ih orders.2 (fun c hc => fits c (by simp [hc]))
      exact ⟨s::ss, ⟨legal, tailLegal⟩, .cons pos tailPos⟩

/-- The cube side and all box positions may be arbitrary real numbers. -/
theorem no_real_tiling (s : ℝ) (bs : List RealBox)
    (orders : SlabOrders [1,2,3,4,5,6,7] (bs.map RealBox.size)) : ¬ RealTiling s bs := by
  intro h
  have grid := h.toGrid
  have sizes : (bs.map RealBox.grid).map Box.size = bs.map RealBox.size := by
    rw [List.map_map]
    rfl
  obtain ⟨ss, legal, placed⟩ := canonicalList (sizes ▸ orders : SlabOrders _ ((bs.map RealBox.grid).map Box.size))
    (fun b hb a => Nat.le_trans (Nat.le_add_left _ _) (grid.bound b hb a))
  exact seven_slabs_cannot_tile _ ⟨ss, _, legal, placed, grid⟩

/-- Seven slabs cannot cover a closed real cube with disjoint interiors. -/
theorem seven_slabs_cannot_tile_real_cube (s : ℝ) (bs : List RealBox)
    (orders : SlabOrders [1,2,3,4,5,6,7] (bs.map RealBox.size)) : ¬ ClosedTiling s bs :=
  fun h => no_real_tiling s bs orders h.toHalfOpen

end SevenSlabs
