import Coloring

namespace Erdos835

open Finset

/-- A fixed-point-free involution on 32 points has at least eleven distinct
orbits of size two. Take the smaller endpoint of each chosen pair. -/
theorem eleven_pairs (g : Equiv.Perm Point) (hinv : ∀ x, g (g x) = x) (hf : ∀ x, g x ≠ x) :
    ∃ U : Finset Point, U.card = 11 ∧ ∀ a b : U, a.val ≠ g b.val := by
  let L : Finset Point := univ.filter fun x => x < g x
  have flip : L.map g.toEmbedding = Lᶜ := by
    ext x
    simp only [mem_map, Equiv.coe_toEmbedding, L, mem_filter, mem_univ, true_and, mem_compl]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [hinv, not_lt] using hy.le
    · intro hx
      have hlt : g x < x := lt_of_le_of_ne (le_of_not_gt hx) (hf x)
      exact ⟨g x, (hinv x).symm ▸ hlt, hinv x⟩
  have count := congrArg card flip
  simp only [card_map, card_compl, Fintype.card_fin] at count
  obtain ⟨U, hsub, hU⟩ := exists_subset_card_eq (show 11 ≤ L.card by omega)
  refine ⟨U, hU, ?_⟩
  intro a b heq
  have ha : a.val < g a.val := (mem_filter.mp (hsub a.property)).2
  have hb : b.val < g b.val := (mem_filter.mp (hsub b.property)).2
  rw [heq, hinv] at ha
  exact (not_lt_of_gt ha) hb

/-- Expand representatives into both endpoints of their orbits. -/
def pairUnion {U : Finset Point} (g : Equiv.Perm Point) (S : Finset U) : Finset Point :=
  let T := S.map (Function.Embedding.subtype _)
  T ∪ T.map g.toEmbedding

theorem mem_pairUnion {U : Finset Point} (g : Equiv.Perm Point) (S : Finset U) (x : Point) :
    x ∈ pairUnion g S ↔ ∃ a ∈ S, x = a.val ∨ x = g a.val := by
  simp [pairUnion, mem_map]
  grind

theorem pairUnion_card {U : Finset Point} (g : Equiv.Perm Point)
    (apart : ∀ a b : U, a.val ≠ g b.val) (S : Finset U) :
    (pairUnion g S).card = 2 * S.card := by
  unfold pairUnion
  rw [card_union_of_disjoint]
  · simp [Nat.two_mul]
  · apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, _, rfl⟩ := mem_map.mp hx
    obtain ⟨y, hy, e⟩ := mem_map.mp hy
    obtain ⟨b, _, rfl⟩ := mem_map.mp hy
    exact apart a b e.symm

theorem pairUnion_stable {U : Finset Point} (g : Equiv.Perm Point)
    (hinv : ∀ x, g (g x) = x) (S : Finset U) :
    (pairUnion g S).map g.toEmbedding = pairUnion g S := by
  apply map_eq_of_subset
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
  obtain ⟨a, ha, rfl | rfl⟩ := (mem_pairUnion g S x).mp hx
  · exact (mem_pairUnion g S _).mpr ⟨a, ha, Or.inr rfl⟩
  · exact (mem_pairUnion g S _).mpr ⟨a, ha, Or.inl (hinv _)⟩

theorem pairUnion_erase {U : Finset Point} (g : Equiv.Perm Point)
    (apart : ∀ a b : U, a.val ≠ g b.val) (S : Finset U) (a : U) :
    pairUnion g (S.erase a) = ((pairUnion g S).erase a.val).erase (g a.val) := by
  ext x
  simp only [mem_pairUnion, mem_erase]
  constructor
  · rintro ⟨b, ⟨hne, hb⟩, rfl | rfl⟩
    · exact ⟨apart b a, fun e => hne (Subtype.ext e), b, hb, Or.inl rfl⟩
    · exact ⟨fun e => hne (Subtype.ext (g.injective e)), (apart a b).symm, b, hb, Or.inr rfl⟩
  · rintro ⟨h1, h2, b, hb, rfl | rfl⟩
    · exact ⟨b, ⟨fun e => h2 (congrArg Subtype.val e), hb⟩, Or.inl rfl⟩
    · exact ⟨b, ⟨fun e => h1 (congrArg (fun z : U => g z.val) e), hb⟩, Or.inr rfl⟩

end Erdos835
