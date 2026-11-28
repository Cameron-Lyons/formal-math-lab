module

public import Order17Reflection
public import Mathlib.Data.Finset.Preimage

@[expose] public section

namespace Erdos835.TwentyPoint

open Finset Equiv.Perm

private def includeVertex : Vertex ↪ Point := Fin.castLEEmb (by decide)

private def shiftGround (j : Fin 17) (x : Point) : Point :=
  if x.val < 17 then ⟨(x.val + j.val) % 17, by omega⟩ else x

private def rotateGround : Equiv.Perm Point where
  toFun := shiftGround 1
  invFun := shiftGround 16
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem rotateGround_order : orderOf rotateGround = 17 := by
  have hpow : rotateGround ^ 17 = 1 := Equiv.ext (by decide +kernel)
  apply ((by decide : Nat.Prime 17).eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hpow)).resolve_left
  intro h
  have hzero := congrArg (fun p : Equiv.Perm Point => p 0) (orderOf_eq_one_iff.mp h)
  exact (by decide : rotateGround 0 ≠ 0) hzero

/-- A solution to the order-17 case on 32 points yields a seed in exactly
the coordinates used by the solver: residues 0,...,16 and fixed points
17,18,19. No further symmetry or choice of a 19-point seed is assumed. -/
theorem order17_requires_concrete_seed {c g τ} (hc : Rainbow c) (he : Equivariant c g τ)
    (hg : orderOf g = 17) :
    ∃ D : Finset Vertex → Prop, QuadrupleSeed univ translate D := by
  have cyc (p : Equiv.Perm Point) (hp : orderOf p = 17) : p.IsCycle :=
    isCycle_of_prime_order' (by rw [hp]; decide) (by rw [hp]; decide)
  have conj := (cyc rotateGround rotateGround_order).isConj (cyc g hg)
    (by rw [← (cyc rotateGround rotateGround_order).orderOf, ← (cyc g hg).orderOf, hg, rotateGround_order])
  obtain ⟨π, hπ⟩ := isConj_iff.mp conj
  let e := includeVertex.trans π.toEmbedding
  let W := (univ : Finset Vertex).map e
  have incl0 : rotateGround.support ⊆ (univ : Finset Vertex).map includeVertex := by decide +kernel
  have hs : g.support ⊆ W := by
    rw [← hπ, support_conj]
    change _ ⊆ (univ : Finset Vertex).map (includeVertex.trans π.toEmbedding)
    rw [← map_map]
    exact map_subset_map.mpr incl0
  obtain ⟨D, hD⟩ := order17_forces_quadruple_seed hc he hg W (by simp [W]) hs
  have onLabels : ∀ (j : Fin 17) (x : Vertex),
      (rotateGround ^ j.val) (includeVertex x) = includeVertex (shift j x) := by decide +kernel
  have commute (j : Fin 17) (x : Vertex) : (g ^ j.val) (e x) = e (shift j x) := by
    rw [← hπ, conj_pow]
    simpa only [e, Function.Embedding.trans_apply, Equiv.coe_toEmbedding, mul_apply,
      Equiv.Perm.inv_def, Equiv.symm_apply_apply] using congrArg π (onLabels j x)
  refine ⟨fun Q => D (Q.map e), ⟨fun Q h => ⟨subset_univ _, by simpa using (hD.blocks _ h).2⟩, ?_, ?_⟩⟩
  · intro T _ ht
    have hTW : T.map e ⊆ W := map_subset_map.mpr (subset_univ _)
    obtain ⟨Q, ⟨hQ, hTQ⟩, hu⟩ := hD.triples _ hTW (by simpa using ht)
    obtain ⟨q, _, rfl⟩ := subset_map_iff.mp (hD.blocks _ hQ).1
    refine ⟨q, ⟨hQ, map_subset_map.mp hTQ⟩, ?_⟩
    intro q' h
    exact (map_injective e) (hu (q'.map e) ⟨h.1, map_subset_map.mpr h.2⟩)
  · intro Q _ h4
    have exchange (j : Fin 17) :
        (Q.map e).map (g ^ j.val).toEmbedding = (translate j Q).map e := by
      simp only [translate, map_eq_image, image_image]
      apply image_congr
      intro x _
      exact commute j x
    simpa only [exchange] using
      hD.orbits (Q.map e) (map_subset_map.mpr (subset_univ _)) (by simpa using h4)

end Erdos835.TwentyPoint
