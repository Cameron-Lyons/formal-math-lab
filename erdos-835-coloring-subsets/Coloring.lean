module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.GroupTheory.Perm.Basic

@[expose] public section

namespace Erdos835

open Finset

abbrev Point := Fin 32
abbrev Block := {s : Finset Point // s.card = 16}

/-- The condition on an individual witness in the upstream definition of
`Erdos835.Property 16`. -/
def Rainbow (c : Block → Fin 17) : Prop :=
  ∀ A : Finset Point, A.card = 17 →
    image c {s : Block | s.val ⊂ A} = (univ : Finset (Fin 17))

/-- A symmetry may relabel the palette by an arbitrary permutation. -/
def Equivariant (c : Block → Fin 17) (g : Equiv.Perm Point) (τ : Equiv.Perm (Fin 17)) : Prop :=
  ∀ B : Block, c ⟨B.val.map g.toEmbedding, by simp [B.property]⟩ = τ (c B)

def face (A : Finset Point) (hA : A.card = 17) (x : A) : Block :=
  ⟨A.erase x.val, by simp [card_erase_of_mem x.property, hA]⟩

/-- Deleting each point of a 17-set lists each color exactly once. -/
theorem face_bijective {c : Block → Fin 17} (hc : Rainbow c)
    (A : Finset Point) (hA : A.card = 17) :
    Function.Bijective (fun x : A => c (face A hA x)) := by
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  refine ⟨?_, by simp [hA]⟩
  intro i
  have hi : i ∈ image c {s : Block | s.val ⊂ A} := (hc A hA) ▸ mem_univ i
  obtain ⟨s, hs, hsi⟩ := mem_image.mp hi
  have hsub : s.val ⊂ A := (mem_filter.mp hs).2
  obtain ⟨x, hx, hface⟩ := ssubset_iff_exists_subset_erase.mp hsub
  have heq := eq_of_subset_of_card_le hface (by simp [card_erase_of_mem hx, hA, s.property])
  exact ⟨⟨x, hx⟩, (congrArg c (Subtype.ext heq.symm)).trans hsi⟩

/-- On an 18-set W, give the edge xy the color of W with x and y deleted. -/
def EdgeHasColor (c : Block → Fin 17) (W : Finset Point) (i : Fin 17) (x y : Point) : Prop :=
  x ≠ y ∧ ∃ h : ((W.erase x).erase y).card = 16, c ⟨_, h⟩ = i

theorem edge_symm {c W i x y} (h : EdgeHasColor c W i x y) : EdgeHasColor c W i y x := by
  unfold EdgeHasColor at *
  rw [erase_right_comm]
  exact ⟨h.1.symm, h.2⟩

theorem edge_irrefl {c W i} (x : Point) : ¬ EdgeHasColor c W i x x := fun h => h.1 rfl

theorem edge_color_unique {c W i j x y}
    (hi : EdgeHasColor c W i x y) (hj : EdgeHasColor c W j x y) : i = j := by
  obtain ⟨_, _, h⟩ := hi
  obtain ⟨_, _, h'⟩ := hj
  exact h.symm.trans h'

theorem edge_unique {c} {W : Finset Point} (hc : Rainbow c) (hW : W.card = 18) (i : Fin 17) (x : Point)
    (hx : x ∈ W) : ∃! y : W, EdgeHasColor c W i x y.val := by
  let A := W.erase x
  have hA : A.card = 17 := by simp [A, card_erase_of_mem hx, hW]
  have hf := face_bijective hc A hA
  obtain ⟨y, hy⟩ := hf.2 i
  have hym := mem_erase.mp y.property
  refine ⟨⟨y.val, hym.2⟩, ⟨hym.1.symm, (face A hA y).property, hy⟩, ?_⟩
  rintro z ⟨hxz, hz, hzi⟩
  let z' : A := ⟨z.val, mem_erase.mpr ⟨hxz.symm, z.property⟩⟩
  have heq : z' = y := hf.1 ((show c (face A hA z') = i from hzi).trans hy.symm)
  exact Subtype.ext (congrArg (fun v : A => v.val) heq)

theorem edge_map {c g τ W i x y} (he : Equivariant c g τ) (hW : W.map g.toEmbedding = W)
    (h : EdgeHasColor c W i x y) : EdgeHasColor c W (τ i) (g x) (g y) := by
  obtain ⟨hxy, hc, hi⟩ := h
  let B : Block := ⟨_, hc⟩
  have hs : B.val.map g.toEmbedding = (W.erase (g x)).erase (g y) := by
    simp [B, hW]
  have hm : ((W.erase (g x)).erase (g y)).card = 16 := by
    rw [← hs, card_map, B.property]
  refine ⟨fun h => hxy (g.injective h), hm, ?_⟩
  calc
    c _ = c ⟨B.val.map g.toEmbedding, by simp [B.property]⟩ := congrArg c (Subtype.ext hs.symm)
    _ = τ (c B) := he B
    _ = τ i := congrArg τ hi

end Erdos835
