module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Topology.Order.OrderClosed

/-! A cuboid in its own orthonormal frame, its interior, and its face parametrizations. -/

@[expose] public section

namespace SevenSlabs.FaceGeometry

/-- The rows of a cuboid's coordinate chart are orthonormal face normals. -/
structure Cuboid where
  chart : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)
  norm : ∀ i : Fin 3, ∑ j : Fin 3, (chart (Pi.single j 1) i)^2 = 1
  orthogonal : ∀ i k : Fin 3, i ≠ k →
    ∑ j : Fin 3, chart (Pi.single j 1) i * chart (Pi.single j 1) k = 0
  lo : Fin 3 → ℝ
  length : Fin 3 → Nat

def Cuboid.body (b : Cuboid) : Set (Fin 3 → ℝ) :=
  {p | ∀ i, b.lo i ≤ b.chart p i ∧ b.chart p i ≤ b.lo i + b.length i}

def Cuboid.openBody (b : Cuboid) : Set (Fin 3 → ℝ) :=
  {p | ∀ i, b.lo i < b.chart p i ∧ b.chart p i < b.lo i + b.length i}

def Cuboid.Aligned (b : Cuboid) : Prop :=
  ∀ i : Fin 3, ∃ j : Fin 3, ∃ c : ℝ, c ≠ 0 ∧ ∀ p, b.chart p i = c * p j

end SevenSlabs.FaceGeometry

open Set Topology

namespace SevenSlabs.FaceGeometry

private noncomputable def Cuboid.chartHomeomorph (b : Cuboid) :=
  b.chart.toContinuousLinearEquiv.toHomeomorph

private theorem body_preimage (b : Cuboid) :
    b.body = b.chartHomeomorph ⁻¹' (univ.pi fun i => Icc (b.lo i) (b.lo i + b.length i)) := by
  ext p
  simp [Cuboid.body, Cuboid.chartHomeomorph, Pi.le_def, forall_and]

private theorem openBody_preimage (b : Cuboid) :
    b.openBody = b.chartHomeomorph ⁻¹' (univ.pi fun i => Ioo (b.lo i) (b.lo i + b.length i)) := by
  ext p
  simp [Cuboid.openBody, Cuboid.chartHomeomorph]

theorem Cuboid.isClosed_body (b : Cuboid) : IsClosed b.body := by
  rw [body_preimage]
  apply IsClosed.preimage b.chartHomeomorph.continuous
  exact isClosed_set_pi (fun _ _ => isClosed_Icc)

theorem Cuboid.interior_body (b : Cuboid) : interior b.body = b.openBody := by
  rw [body_preimage, ← Homeomorph.preimage_interior, interior_pi_set (finite_univ),
      openBody_preimage]
  simp only [interior_Icc]

theorem Cuboid.closure_openBody (b : Cuboid) (pos : ∀ i, 0 < b.length i) :
    closure b.openBody = b.body := by
  rw [openBody_preimage, ← Homeomorph.preimage_closure, closure_pi_set, body_preimage]
  have h (i : Fin 3) : b.lo i ≠ b.lo i + b.length i := by
    have p : 0 < (b.length i : ℝ) := by exact_mod_cast pos i
    linarith
  simp only [closure_Ioo (h _)]

theorem Cuboid.face_of_frontier (b : Cuboid) {p : Fin 3 → ℝ} (hp : p ∈ frontier b.body) :
    ∃ i, b.chart p i = b.lo i ∨ b.chart p i = b.lo i + b.length i := by
  obtain ⟨h₁,h₂⟩ := hp
  rw [b.isClosed_body.closure_eq] at h₁
  rw [b.interior_body] at h₂
  by_contra! h
  apply h₂
  exact fun i => ⟨lt_of_le_of_ne (h₁ i).1 (h i).1.symm,
                  lt_of_le_of_ne (h₁ i).2 (h i).2⟩

/-- Each coordinate of a point in the interior of the closed cube lies strictly
between its corresponding bounds. -/
theorem interior_cube (s : ℝ) :
    interior (Set.Icc (fun _ : Fin 3 => (0 : ℝ)) (fun _ => s)) =
    {p | ∀ i, 0 < p i ∧ p i < s} := by
  have he : Set.Icc (fun _ : Fin 3 => (0 : ℝ)) (fun _ => s) =
      univ.pi (fun _ => Icc 0 s) := by
    ext p
    simp [Set.mem_Icc, Pi.le_def]
  rw [he, interior_pi_set finite_univ]
  ext p
  simp [interior_Icc]

theorem cube_face_of_frontier {s : ℝ} {p : Fin 3 → ℝ}
    (hp : p ∈ frontier (Set.Icc (fun _ : Fin 3 => (0 : ℝ)) (fun _ => s))) :
    ∃ i, p i = 0 ∨ p i = s := by
  obtain ⟨h₁,h₂⟩ := hp
  rw [isClosed_Icc.closure_eq] at h₁
  rw [interior_cube] at h₂
  by_contra! h
  apply h₂
  exact fun i => ⟨lt_of_le_of_ne (h₁.1 i) (h i).1.symm,
                  lt_of_le_of_ne (h₁.2 i) (h i).2⟩

open Set

/-- Set one chart coordinate to t and let the other coordinates vary freely. -/
private noncomputable def fixCoord (i : Fin 3) (t : ℝ) :
    (Fin 3 → ℝ) →ᵃ[ℝ] (Fin 3 → ℝ) :=
  AffineMap.pi (fun j => if j = i then AffineMap.const _ _ t else AffineMap.proj j)

@[simp] private theorem fixCoord_apply (i : Fin 3) (t : ℝ) (x : Fin 3 → ℝ) (j : Fin 3) :
    fixCoord i t x j = if j = i then t else x j := by
  by_cases h : j = i <;> simp [fixCoord, h, AffineMap.pi_apply]

theorem Cuboid.face_patch (b : Cuboid) (i : Fin 3) (t : ℝ)
    (ht : b.lo i ≤ t ∧ t ≤ b.lo i + b.length i) (hp : ∀ j, 0 < b.length j) :
    ∃ (param : (Fin 3 → ℝ) →ᵃ[ℝ] (Fin 3 → ℝ)) (U : Set (Fin 3 → ℝ)),
      Set.range param = {p | b.chart p i = t} ∧ IsOpen U ∧ U.Nonempty ∧
      ∀ x ∈ U, param x ∈ b.body := by
  let param := b.chart.symm.toLinearMap.toAffineMap.comp (fixCoord i t)
  let U : Set (Fin 3 → ℝ) := ⋂ j, {x | b.lo j < x j ∧ x j < b.lo j + b.length j}
  have ev (x : Fin 3 → ℝ) (j : Fin 3) :
      b.chart (param x) j = if j = i then t else x j := by simp [param]
  refine ⟨param, U, ?_, ?_, ?_, ?_⟩
  · ext p
    constructor
    · rintro ⟨x, rfl⟩
      simpa using ev x i
    · intro h
      change b.chart p i = t at h
      refine ⟨b.chart p, b.chart.injective ?_⟩
      funext j
      by_cases he : j = i <;> simp [ev, he, h]
  · apply isOpen_iInter_of_finite
    intro j
    exact (isOpen_lt continuous_const (continuous_apply j)).inter
      (isOpen_lt (continuous_apply j) continuous_const)
  · refine ⟨fun j => b.lo j + (b.length j : ℝ)/2, Set.mem_iInter.mpr ?_⟩
    intro j
    have hj : (0 : ℝ) < b.length j := by exact_mod_cast hp j
    change _ < _ ∧ _ < _
    constructor <;> linarith
  · intro x hx j
    have hj := Set.mem_iInter.mp hx j
    rw [ev]
    split
    · next e => simpa [e] using ht
    · exact ⟨hj.1.le,hj.2.le⟩

end SevenSlabs.FaceGeometry
