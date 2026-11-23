import Coloring
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Dynamics.FixedPoints.Defs
import Mathlib.GroupTheory.OrderOfElement

namespace Erdos835

open Finset Equiv.Perm

/-- Deleting a fixed point from an invariant 17-set gives a fixed color,
and every fixed color is obtained exactly once this way. -/
theorem fixed_colors_on_invariant_set {c g τ} (hc : Rainbow c) (he : Equivariant c g τ)
    (A : Finset Point) (ha : A.card = 17) (hs : A.map g.toEmbedding = A) :
    (A.filter fun x => g x = x).card = Fintype.card (Function.fixedPoints τ) := by
  let color (x : A) := c (face A ha x)
  have bij : Function.Bijective color := face_bijective hc A ha
  let act (x : A) : A := ⟨g x, by
    simpa only [hs, Equiv.coe_toEmbedding] using mem_map_of_mem g.toEmbedding x.property⟩
  have equiv (x : A) : τ (color x) = color (act x) := by
    rw [← he (face A ha x)]
    exact congrArg c (Subtype.ext (by simp [face, act, hs]))
  have fixed (x : A) : g x = x ↔ τ (color x) = color x := by
    rw [equiv, bij.1.eq_iff]
    exact (Subtype.ext_iff (a1 := act x) (a2 := x)).symm
  have cards := Fintype.card_congr ((Equiv.ofBijective color bij).subtypeEquiv
    (p := fun x : A => g x = x) (q := fun i => τ i = i) fixed)
  simpa only [Fintype.card_subtype, Finset.univ_eq_attach,
    Finset.filter_attach (fun x : Point => g x = x) A, Finset.card_map, Finset.card_attach,
    Function.mem_fixedPoints_iff] using cards

/-- An invariant set containing a fixed point contains invariant subsets
of every odd size that fits. -/
private theorem invariant_odd_subset {g : Equiv.Perm Point} (inv : Function.Involutive g)
    {z : Point} (hz : g z = z) (n : ℕ) (S : Finset Point)
    (stable : S.map g.toEmbedding = S) (hzS : z ∈ S) (size : 2 * n + 1 ≤ S.card) :
    ∃ T ⊆ S, T.card = 2 * n + 1 ∧ T.map g.toEmbedding = T := by
  induction n generalizing S with
  | zero => exact ⟨{z}, by simpa, by simp, by simp [hz]⟩
  | succ n ih =>
    -- A moved pair can be removed and put back after the smaller choice.
    by_cases allFixed : ∀ x ∈ S, g x = x
    · obtain ⟨T, hT, hc⟩ := exists_subset_card_eq size
      refine ⟨T, hT, hc, map_eq_of_subset ?_⟩
      rw [map_eq_image, image_subset_iff]
      exact fun x hx => (allFixed x (hT hx)).symm ▸ hx
    push Not at allFixed
    obtain ⟨x, hx, moved⟩ := allFixed
    let P : Finset Point := {x, g x}
    have inside : P ⊆ S := by
      rw [insert_subset_iff, singleton_subset_iff]
      exact ⟨hx, stable ▸ mem_map_of_mem g.toEmbedding hx⟩
    have pair : P.card = 2 := card_pair moved.symm
    have stableP : P.map g.toEmbedding = P := by simp [P, inv x, pair_comm]
    obtain ⟨T, sub, card, stableT⟩ := ih (S \ P) (by simp [map_sdiff, stable, stableP])
      (by simpa [P, hzS] using (show z ≠ x ∧ z ≠ g x by grind [Function.Involutive]))
      (by rw [card_sdiff_of_subset inside, pair]; omega)
    refine ⟨T ∪ P, union_subset (sub.trans sdiff_subset) inside, ?_, by simp [map_union, stableT, stableP]⟩
    rw [card_union_of_disjoint (sdiff_disjoint.mono_left sub), card, pair]
    omega

/-- Every point involution of an equivariant rainbow coloring on 32 points
moves at least 30 points. Its palette action may be arbitrary. -/
theorem involution_moves_at_least_thirty {c g τ} (hc : Rainbow c) (he : Equivariant c g τ)
    (hg : orderOf g = 2) : 30 ≤ g.support.card := by
  by_contra! small
  have square : g ^ 2 = 1 := hg ▸ pow_orderOf_eq_one g
  have inv (x : Point) : g (g x) = x := by
    simpa [pow_two] using congrArg (fun p : Equiv.Perm Point => p x) square
  have many : 2 < g.supportᶜ.card := by rw [card_compl, Fintype.card_fin]; omega
  obtain ⟨a, b, z, ha, hb, hz, hab, haz, hbz⟩ := two_lt_card_iff.mp many
  simp only [mem_compl, notMem_support] at ha hb hz
  obtain ⟨x, moved⟩ : ∃ x, g x ≠ x := by
    by_contra! h
    simp [show g = 1 from Equiv.ext h] at hg

  -- Reserve two fixed points and a transposed pair, and choose the common 15 points.
  let F : Finset Point := {a, b}
  let P : Finset Point := {x, g x}
  let S : Finset Point := univ \ (F ∪ P)
  have stableF : F.map g.toEmbedding = F := by simp [F, ha, hb]
  have stableP : P.map g.toEmbedding = P := by simp [P, inv x, pair_comm]
  have fcard : F.card = 2 := card_pair hab
  have pcard : P.card = 2 := card_pair moved.symm
  obtain ⟨T, sub, size, stable⟩ := invariant_odd_subset inv hz 7 S
    (by simp [S, map_sdiff, map_union, stableF, stableP])
    (by simp [S, F, P]; grind)
    (by
      have bound := card_union_le F P
      rw [fcard, pcard] at bound
      simp [S, card_sdiff_of_subset]
      omega)
  have disjoint : Disjoint T (F ∪ P) := sdiff_disjoint.mono_left sub

  -- Either pair completes T to a 17-set, so each must contribute the same number of fixed points.
  let fixed := fun y : Point => g y = y
  have count (Q : Finset Point) (hQ : Q ⊆ F ∪ P) (hq : Q.card = 2)
      (sq : Q.map g.toEmbedding = Q) :
      (T.filter fixed).card + (Q.filter fixed).card = Fintype.card (Function.fixedPoints τ) := by
    have dj := disjoint.mono_right hQ
    rw [← card_union_of_disjoint (dj.mono (filter_subset _ _) (filter_subset _ _)), ← filter_union]
    exact fixed_colors_on_invariant_set hc he _ (by rw [card_union_of_disjoint dj, size, hq])
      (by simp [map_union, stable, sq])
  have eq := (count F subset_union_left fcard stableF).trans
    (count P subset_union_right pcard stableP).symm
  simp [fixed, F, P, filter_insert, filter_singleton, ha, hb, hab, inv x, moved, moved.symm] at eq

end Erdos835
