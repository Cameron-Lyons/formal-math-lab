module

public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Topology.Baire.CompleteMetrizable
public import SevenSlabs.Cuboid

/-! In a finite tiling by cuboids, every face direction occurs on the exterior. -/

@[expose] public section

open Set Filter Topology

namespace SevenSlabs.FaceGeometry

abbrev Space := Fin 3 → ℝ

/-- A point of a relatively open face patch may be chosen away from every affine
zero set that does not contain the whole patch. -/
theorem generic_face_point {J : Type*} [Finite J]
    (forms : J → (Space →ᵃ[ℝ] ℝ)) (U : Set Space) (hu : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, ∀ j, forms j x = 0 → forms j = 0 := by
  classical
  let active := {j : J // forms j ≠ 0}
  let good (j : active) := {x : Space | forms j.1 x ≠ 0}
  have ho (j : active) : IsOpen (good j) :=
    isOpen_ne_fun (forms j.1).continuous_of_finiteDimensional continuous_const
  have hd (j : active) : Dense (good j) := by
    apply dense_iff_inter_open.mpr
    intro V hv hvne
    by_contra hempty
    apply j.2 (AffineMap.ext_on (hv.affineSpan_eq_top hvne) ?_)
    intro x hx
    change forms j.val x = 0
    by_contra hn
    exact hempty ⟨x, hx, hn⟩
  obtain ⟨x, hx, hxU⟩ := (dense_iInter_of_isOpen ho hd).exists_mem_open hu hne
  refine ⟨x, hxU, ?_⟩
  intro j hj
  by_contra hnj
  exact (Set.mem_iInter.mp hx ⟨j,hnj⟩) hj

/-- Points on one side of `p` can only be covered by tiles meeting that side.
Since the cover is finite and closed, at least one such tile contains `p`. -/
theorem tile_reaching_side {X I : Type*} [TopologicalSpace X] [Finite I]
    (tiles : I → Set X) (closed_tiles : ∀ i, IsClosed (tiles i))
    {container side : Set X} (cover : container ⊆ ⋃ i, tiles i) {p : X}
    (hp : p ∈ interior container) (reach : p ∈ closure side) :
    ∃ j, p ∈ tiles j ∧ ∃ q ∈ tiles j, q ∈ side := by
  classical
  let J : Set I := {j | ∃ q ∈ tiles j, q ∈ side}
  let union : Set X := ⋃ j ∈ J, tiles j
  have closed_union : IsClosed union := J.toFinite.isClosed_biUnion fun i _ => closed_tiles i
  have covered : container ∩ side ⊆ union := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (cover hx.1)
    exact Set.mem_iUnion₂.mpr ⟨i, ⟨x, hi, hx.2⟩, hi⟩
  have hnear : p ∈ closure (container ∩ side) := by
    rw [mem_closure_iff_frequently] at reach ⊢
    exact (reach.and_eventually (mem_interior_iff_mem_nhds.mp hp)).mono
      (fun _ h => ⟨h.2, h.1⟩)
  obtain ⟨i, hi, hpi⟩ := Set.mem_iUnion₂.mp (closure_minimal covered closed_union hnear)
  exact ⟨i, hpi, hi⟩

/-- Across a supporting face in the interior of the container, some *other*
tile shares the boundary point and reaches strictly across the supporting plane.
For a face of a full-dimensional cuboid, `hp` is regularity at the face. -/
theorem face_contact {X I : Type*} [TopologicalSpace X] [Finite I]
    (tiles : I → Set X) (closed_tiles : ∀ i, IsClosed (tiles i))
    (separate : ∀ i j, i ≠ j → Disjoint (interior (tiles i)) (interior (tiles j)))
    {container side : Set X} (cover : container ⊆ ⋃ i, tiles i)
    {p : X} {i : I} (hin : p ∈ interior container) (hp : p ∈ closure (interior (tiles i)))
    (reach : p ∈ closure side) (disj : Disjoint (tiles i) side) :
    ∃ j, j ≠ i ∧ p ∈ frontier (tiles j) ∧ ∃ q ∈ tiles j, q ∈ side := by
  obtain ⟨j, hj, q, hq, hside⟩ := tile_reaching_side tiles closed_tiles cover hin reach
  have hji : j ≠ i := by
    rintro rfl
    exact Set.disjoint_left.mp disj hq hside
  have hn : p ∉ interior (tiles j) := by
    intro hjp
    obtain ⟨r, hrj, hri⟩ := mem_closure_iff.mp hp _ isOpen_interior hjp
    exact Set.disjoint_left.mp (separate j i hji) hrj hri
  exact ⟨j, hji, ⟨subset_closure hj, hn⟩, q, hq, hside⟩

/-- A supporting plane of a face is described as the zero locus of an affine form. -/
structure FacetedSolid (F : Type*) where
  carrier : Set Space
  closed : IsClosed carrier
  forms : F → (Space →ᵃ[ℝ] ℝ)
  boundary : ∀ x ∈ frontier carrier, ∃ f, forms f x = 0

/-- The linear parts have proportional normals. Real face forms have nonzero linear part. -/
def Parallel (h : Space →ₗ[ℝ] ℝ) (g : Space →ᵃ[ℝ] ℝ) : Prop :=
  ∃ c : ℝ, ∀ x, g.linear x = c * h x

def HasFace {F} (P : FacetedSolid F) (h : Space →ₗ[ℝ] ℝ) : Prop :=
  ∃ f, Parallel h (P.forms f)

/-- The body attains its minimum height at a genuine face. An open patch of its
supporting hyperplane lies in the closure of the interior. Parameters can have
a redundant coordinate, so the coordinate projection of a cube is a valid chart. -/
def LowerFace {F} (P : FacetedSolid F) (h : Space →ₗ[ℝ] ℝ) (t : ℝ) : Prop :=
  (∀ q ∈ P.carrier, t ≤ h q) ∧
    ∃ (param : Space →ᵃ[ℝ] Space) (U : Set Space),
      Set.range param = {x | h x = t} ∧ IsOpen U ∧ U.Nonempty ∧
      ∀ x ∈ U, param x ∈ closure (interior P.carrier)

private theorem parallel_of_vanishing {h : Space →ₗ[ℝ] ℝ} {w : Space} (hw : h w = 1)
    {g : Space →ᵃ[ℝ] ℝ} {t : ℝ} (hz : ∀ p, h p = t → g p = 0) : Parallel h g := by
  let p := t • w
  have hp : h p = t := by simp [p, hw]
  refine ⟨g.linear w, fun x => ?_⟩
  let v := x - (h x) • w
  have hv : h v = 0 := by simp [v, hw]
  have hgv : g (v + p) = 0 := hz _ (by simp [hv, hp])
  have e := g.map_vadd p v
  change g (v + p) = g.linear v + g p at e
  rw [hgv, hz p hp, add_zero] at e
  simp only [v, map_sub, map_smul, smul_eq_mul] at e
  linarith

private theorem reach_lower (h : Space →ₗ[ℝ] ℝ) {w : Space} (hw : h w = 1)
    (p : Space) : p ∈ closure {q | h q < h p} := by
  let f (u : ℝ) := p + u • w
  have hc : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
  have hmem : (0 : ℝ) ∈ closure (Iio (0:ℝ)) := by simp
  have him := mem_closure_image hc.continuousAt hmem
  have hsub : f '' Iio (0:ℝ) ⊆ {q | h q < h p} := by
    rintro _ ⟨u, hu, rfl⟩
    change h (p + u • w) < h p
    simpa [hw] using hu
  simpa [f] using (closure_mono hsub him)

/-- Finite-tiling alignment for solids with paired parallel facets. The only
shape-specific assumption `opposites` says that a tile with the given facet
normal also attains its minimum height on a full facet. -/
theorem alignment_of_lower_faces {I F G : Type*} [Finite I] [Finite F] [Finite G]
    (C : FacetedSolid G) (tiles : I → FacetedSolid F)
    (cover : C.carrier = ⋃ i, (tiles i).carrier)
    (separate : ∀ i j, i ≠ j → Disjoint (interior (tiles i).carrier) (interior (tiles j).carrier))
    (h : Space →ₗ[ℝ] ℝ) {w : Space} (hw : h w = 1)
    (opposites : ∀ i, HasFace (tiles i) h → ∃ t, LowerFace (tiles i) h t)
    (has : ∃ i, HasFace (tiles i) h) : HasFace C h := by
  classical
  let J := {i : I // HasFace (tiles i) h}
  have hj : Nonempty J := has.elim fun i hi => ⟨⟨i,hi⟩⟩
  choose ht hface using fun j : J => opposites j.1 j.2
  have exmin : ∃ j : J, ∀ k : J, ht j ≤ ht k := by
    let _ := Fintype.ofFinite J
    obtain ⟨j, _, hmin⟩ := Finset.exists_min_image Finset.univ ht Finset.univ_nonempty
    exact ⟨j, fun k => hmin k (Finset.mem_univ k)⟩
  obtain ⟨i, hmin⟩ := exmin
  obtain ⟨hbound, param, U, hrange, hu, hne, hpatch⟩ := hface i
  let forms : G ⊕ (I × F) → (Space →ᵃ[ℝ] ℝ)
    | .inl f => C.forms f
    | .inr (j,f) => (tiles j).forms f
  obtain ⟨u, hU, hgeneric⟩ := generic_face_point (fun j => (forms j).comp param) U hu hne
  let p := param u
  have hp : h p = ht i := by
    change p ∈ {x | h x = ht i}
    rw [← hrange]
    exact ⟨u,rfl⟩
  have same (f : G ⊕ (I × F)) (heq : forms f p = 0) : Parallel h (forms f) := by
    have e := hgeneric f heq
    apply parallel_of_vanishing hw (t := ht i)
    intro q hq
    have hm : q ∈ Set.range param := hrange.symm ▸ hq
    obtain ⟨x, rfl⟩ := hm
    exact congrArg (fun g : Space →ᵃ[ℝ] ℝ => g x) e
  by_contra hc
  have reg := hpatch u hU
  have pi : p ∈ (tiles i.val).carrier :=
    closure_minimal interior_subset (tiles i.val).closed reg
  have pc : p ∈ C.carrier := cover ▸ Set.mem_iUnion.mpr ⟨i.val,pi⟩
  have innerC : p ∈ interior C.carrier := by
    by_contra hinner
    have hfront : p ∈ frontier C.carrier := ⟨subset_closure pc, hinner⟩
    obtain ⟨f, heq⟩ := C.boundary _ hfront
    exact hc ⟨f, same (.inl f) heq⟩
  have disj : Disjoint (tiles i.val).carrier {q | h q < h p} := by
    refine Set.disjoint_left.mpr fun q hq hlt => ?_
    exact (not_lt_of_ge ((hbound q hq).trans' hp.le)) hlt
  obtain ⟨j, _, hj, q, hq, below⟩ := face_contact (fun k => (tiles k).carrier)
    (fun k => (tiles k).closed) separate cover.subset innerC reg (reach_lower h hw p) disj
  obtain ⟨f, hfj⟩ := (tiles j).boundary _ hj
  let next : J := ⟨j, f, same (.inr (j,f)) hfj⟩
  exact (not_lt_of_ge ((hmin next).trans ((hface next).1 q hq))) (hp ▸ below)

end SevenSlabs.FaceGeometry

open Set

namespace SevenSlabs.FaceGeometry

noncomputable def Cuboid.row (b : Cuboid) (i : Fin 3) : Space →ₗ[ℝ] ℝ :=
  (LinearMap.proj i).comp b.chart.toLinearMap

private noncomputable def offsetForm (f : Space →ₗ[ℝ] ℝ) (t : ℝ) : Space →ᵃ[ℝ] ℝ :=
  f.toAffineMap - AffineMap.const ℝ Space t

@[simp] private theorem offset_apply (f : Space →ₗ[ℝ] ℝ) (t : ℝ) (p : Space) :
    offsetForm f t p = f p - t := rfl

@[simp] private theorem offset_linear (f : Space →ₗ[ℝ] ℝ) (t : ℝ) :
    (offsetForm f t).linear = f := by simp [offsetForm, AffineMap.sub_linear]

private noncomputable def Cuboid.asSolid (b : Cuboid) : FacetedSolid (Fin 3 × Bool) where
  carrier := b.body
  closed := b.isClosed_body
  forms f := offsetForm (b.row f.1) (if f.2 then b.lo f.1 + b.length f.1 else b.lo f.1)
  boundary p hp := by
    obtain ⟨i, hlo | hhi⟩ := b.face_of_frontier hp
    · exact ⟨(i,false), sub_eq_zero.mpr hlo⟩
    · exact ⟨(i,true), sub_eq_zero.mpr hhi⟩

private noncomputable def cubeSolid (s : ℝ) : FacetedSolid (Fin 3 × Bool) where
  carrier := Set.Icc (fun _ => 0) (fun _ => s)
  closed := isClosed_Icc
  forms f := offsetForm (LinearMap.proj f.1) (if f.2 then s else 0)
  boundary p hp := by
    obtain ⟨i, hlo | hhi⟩ := cube_face_of_frontier hp
    · exact ⟨(i,false), sub_eq_zero.mpr hlo⟩
    · exact ⟨(i,true), sub_eq_zero.mpr hhi⟩

private theorem Cuboid.lower_of_parallel (b : Cuboid) (h : Space →ₗ[ℝ] ℝ)
    (pos : ∀ j, 0 < b.length j) (has : HasFace b.asSolid h) :
    ∃ t, LowerFace b.asSolid h t := by
  obtain ⟨⟨i, side⟩, c, heq⟩ := has
  have he (p : Space) : b.chart p i = c * h p := by
    simpa [Cuboid.asSolid, Cuboid.row] using heq p
  have hc : c ≠ 0 := by
    intro hzero
    simpa [hzero] using he (b.chart.symm (Pi.single i 1))
  let m := if 0 < c then b.lo i else b.lo i + b.length i
  have hm : b.lo i ≤ m ∧ m ≤ b.lo i + b.length i := by
    dsimp [m]
    split <;> simp
  obtain ⟨param,U,hr,ho,hne,hpatch⟩ := b.face_patch i m hm pos
  refine ⟨m / c, ?_, param, U, ?_, ho, hne, ?_⟩
  · intro p hbody
    obtain ⟨hlo,hhi⟩ := hbody i
    by_cases hs : 0 < c
    · apply (div_le_iff₀ hs).mpr
      simpa [m,hs,mul_comm,← he p] using hlo
    · have hn : c < 0 := lt_of_le_of_ne (le_of_not_gt hs) hc
      apply (div_le_iff_of_neg hn).mpr
      simpa [m,hs,mul_comm,← he p] using hhi
  · rw [hr]
    ext p
    change b.chart p i = m ↔ h p = m / c
    rw [eq_div_iff hc, mul_comm (h p), ← he p]
  · intro p hp
    change param p ∈ closure (interior b.body)
    rw [b.interior_body, b.closure_openBody pos]
    exact hpatch p hp

/-- Every face of every cuboid in a finite tiling of a real cube is parallel
to a cube face. Cuboid charts can have any orientation and any real origin. -/
theorem cuboid_alignment {I : Type*} [Finite I] (s : ℝ) (tiles : I → Cuboid)
    (pos : ∀ k j, 0 < (tiles k).length j)
    (cover : Set.Icc (fun _ : Fin 3 => (0 : ℝ)) (fun _ => s) = ⋃ i, (tiles i).body)
    (separate : ∀ k l, k ≠ l → Disjoint (interior (tiles k).body) (interior (tiles l).body)) :
    ∀ i, (tiles i).Aligned := by
  intro i k
  let b := tiles i
  let h := b.row k
  have hw : h (b.chart.symm (Pi.single k 1)) = 1 := by simp [h, Cuboid.row]
  have has : HasFace b.asSolid h := by
    refine ⟨(k,false),1,?_⟩
    intro p
    simp [Cuboid.asSolid, h]
  obtain ⟨⟨j,side⟩,c,heq⟩ := alignment_of_lower_faces (cubeSolid s)
    (fun i => (tiles i).asSolid) cover separate h hw
    (fun i => (tiles i).lower_of_parallel h (pos i)) ⟨i,has⟩
  have he (p : Space) : p j = c * b.chart p k := by
    simpa [cubeSolid,h,Cuboid.row] using heq p
  have hc : c ≠ 0 := by
    intro hzero
    simpa [hzero] using he (Pi.single j 1)
  refine ⟨j,c⁻¹,inv_ne_zero hc,?_⟩
  intro p
  change b.chart p k = c⁻¹ * p j
  rw [he p, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

end SevenSlabs.FaceGeometry
