module

public import SevenSlabs.Cuboid
public import SevenSlabs.RealBoxes
public import SevenSlabs.AxisAligned

/-! A cuboid aligned with the cube has a signed permutation of the coordinate axes. -/

@[expose] public section

namespace SevenSlabs.FaceGeometry

abbrev Point := Fin 3 → ℝ

/-- A signed coordinate permutation specifying each local face normal. -/
structure SignedFrame (b : Cuboid) where
  axes : Fin 3 ≃ Fin 3
  positive : Fin 3 → Bool
  coords : ∀ p i, b.chart p i = if positive i then p (axes i) else -p (axes i)

theorem Cuboid.signed_frame {b : Cuboid} (h : b.Aligned) : Nonempty (SignedFrame b) := by
  classical
  choose j c hc spec using h
  have inj : Function.Injective j := by
    intro i k eq
    by_contra ne
    let p := b.chart.symm (Pi.single i 1)
    have pi : b.chart p i = 1 := by simp [p]
    have pk : b.chart p k = 0 := by simp [p, Pi.single_eq_of_ne (Ne.symm ne)]
    rw [spec] at pi pk
    have zero := (mul_eq_zero.mp pk).resolve_left (hc k)
    rw [eq, zero, mul_zero] at pi
    exact zero_ne_one pi
  have sign (i : Fin 3) : c i = 1 ∨ c i = -1 := by
    have H := b.norm i
    simp_rw [spec] at H
    have simpl (k : Fin 3) : (c i * (Pi.single k 1 : Fin 3 → ℝ) (j i)) ^ 2 =
        if k = j i then (c i)^2 else 0 := by
      by_cases hk : k = j i
      · simp [hk]
      · simp [hk]
    simp_rw [simpl] at H
    simp at H
    exact H
  let e := Equiv.ofBijective j ⟨inj, Finite.surjective_of_injective inj⟩
  refine ⟨⟨e, fun i => decide (c i = 1), ?_⟩⟩
  intro p i
  rw [spec]
  change c i * p (j i) = if decide (c i = 1) then p (j i) else -p (j i)
  obtain h | h := sign i <;> norm_num [h]

def axisOfFin : Fin 3 → Axis | 0 => .x | 1 => .y | 2 => .z
def finOfAxis : Axis → Fin 3 | .x => 0 | .y => 1 | .z => 2
@[simp] theorem fin_axis (i : Fin 3) : finOfAxis (axisOfFin i) = i := by fin_cases i <;> rfl
@[simp] theorem axis_fin (a : Axis) : axisOfFin (finOfAxis a) = a := by cases a <;> rfl

def tripleOf (f : Fin 3 → Nat) : Triple := ⟨f 0, f 1, f 2⟩
@[simp] theorem tripleOf_along (f : Fin 3 → Nat) (a : Axis) :
    (tripleOf f).along a = f (finOfAxis a) := by cases a <;> rfl

def SignedFrame.lower {b : Cuboid} (t : SignedFrame b) (i : Fin 3) : ℝ :=
  if t.positive i then b.lo i else -(b.lo i + b.length i)

noncomputable def SignedFrame.box {b : Cuboid} (t : SignedFrame b) : RealBox where
  lo a := t.lower (t.axes.symm (finOfAxis a))
  size := tripleOf (fun j => b.length (t.axes.symm j))

theorem SignedFrame.closed_iff_at {b : Cuboid} (t : SignedFrame b) (p : Point) (i : Fin 3) :
    (b.lo i ≤ b.chart p i ∧ b.chart p i ≤ b.lo i + b.length i) ↔
      t.lower i ≤ p (t.axes i) ∧ p (t.axes i) ≤ t.lower i + b.length i := by
  rw [t.coords]
  cases h : t.positive i
  · simp [h, SignedFrame.lower]; constructor <;> intro hh <;> constructor <;> linarith
  · simp [h, SignedFrame.lower]

theorem SignedFrame.open_iff_at {b : Cuboid} (t : SignedFrame b) (p : Point) (i : Fin 3) :
    (b.lo i < b.chart p i ∧ b.chart p i < b.lo i + b.length i) ↔
      t.lower i < p (t.axes i) ∧ p (t.axes i) < t.lower i + b.length i := by
  rw [t.coords]
  cases h : t.positive i
  · simp [h, SignedFrame.lower]; constructor <;> intro hh <;> constructor <;> linarith
  · simp [h, SignedFrame.lower]

theorem SignedFrame.closed_iff {b : Cuboid} (t : SignedFrame b) (p : Point) :
    p ∈ b.body ↔ ∀ a, t.box.lo a ≤ p (finOfAxis a) ∧
                          p (finOfAxis a) ≤ t.box.lo a + t.box.size.along a := by
  constructor
  · intro hp a
    simpa [SignedFrame.box] using (t.closed_iff_at p _).mp (hp (t.axes.symm (finOfAxis a)))
  · intro hp i
    apply (t.closed_iff_at p i).mpr
    simpa [SignedFrame.box] using hp (axisOfFin (t.axes i))

theorem SignedFrame.open_iff {b : Cuboid} (t : SignedFrame b) (p : Point) :
    p ∈ b.openBody ↔ ∀ a, t.box.lo a < p (finOfAxis a) ∧
                          p (finOfAxis a) < t.box.lo a + t.box.size.along a := by
  constructor
  · intro hp a
    simpa [SignedFrame.box] using (t.open_iff_at p _).mp (hp (t.axes.symm (finOfAxis a)))
  · intro hp i
    apply (t.open_iff_at p i).mpr
    simpa [SignedFrame.box] using hp (axisOfFin (t.axes i))

/-- Containment of the two opposite corners gives coordinate-wise bounds. -/
theorem SignedFrame.cube_bounds {b : Cuboid} (t : SignedFrame b) {s : ℝ}
    (sub : b.body ⊆ Set.Icc (fun _ : Fin 3 => (0 : ℝ)) (fun _ => s)) (a : Axis) :
    0 ≤ t.box.lo a ∧ t.box.lo a + t.box.size.along a ≤ s := by
  let low : Point := fun j => t.box.lo (axisOfFin j)
  let high : Point := fun j => t.box.lo (axisOfFin j) + t.box.size.along (axisOfFin j)
  have hl : low ∈ b.body := (t.closed_iff low).mpr (by intro d; simp [low])
  have hh : high ∈ b.body := (t.closed_iff high).mpr (by intro d; simp [high])
  exact ⟨by simpa [low] using (sub hl).1 (finOfAxis a),
         by simpa [high] using (sub hh).2 (finOfAxis a)⟩

set_option maxHeartbeats 1200000 in
/-- Permuting the coordinate axes preserves membership in the six orientations. -/
private theorem permute_orientation (f : Fin 3 → Nat) (e : Equiv.Perm (Fin 3))
    {s : Shape} (hf : tripleOf f ∈ s.orientations) :
    tripleOf (fun j => f (e j)) ∈ s.orientations := by
  have three (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  have n01 : e 0 ≠ e 1 := e.injective.ne (by decide)
  have n02 : e 0 ≠ e 2 := e.injective.ne (by decide)
  have n12 : e 1 ≠ e 2 := e.injective.ne (by decide)
  simp only [tripleOf, Shape.orientations, List.mem_cons, List.not_mem_nil,
    or_false, Triple.mk.injEq] at hf ⊢
  rcases three (e 0) with h | h | h <;>
    rcases three (e 1) with j | j | j <;>
    rcases three (e 2) with l | l | l <;>
    first
    | exact (n01 (h.trans j.symm)).elim
    | exact (n02 (h.trans l.symm)).elim
    | exact (n12 (j.trans l.symm)).elim
    | rw [h, j, l]; grind

theorem SignedFrame.isSlab {b : Cuboid} (t : SignedFrame b) {k : Nat}
    (h : IsSlab k (tripleOf b.length)) : IsSlab k t.box.size := by
  obtain ⟨hk, u, v, hu, hv, hor⟩ := h
  exact ⟨hk, u, v, hu, hv, permute_orientation b.length t.axes.symm hor⟩

theorem Cuboid.length_pos_of_slab {b : Cuboid} {k : Nat}
    (h : IsSlab k (tripleOf b.length)) (j : Fin 3) : 0 < b.length j := by
  obtain ⟨hk, u, v, hu, hv, hor⟩ := h
  have hku := Nat.mul_pos hk hu
  have hkv := Nat.mul_pos hk hv
  simp only [tripleOf, Shape.orientations, List.mem_cons, List.not_mem_nil, or_false,
    Triple.mk.injEq] at hor
  fin_cases j <;> grind

end SevenSlabs.FaceGeometry
