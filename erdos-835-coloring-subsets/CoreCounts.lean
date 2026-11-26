module

public import Order17Reflection
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace Erdos835.TwentyPoint

open Finset

noncomputable def blocksThrough (D : Finset Vertex → Prop) (S : Finset Vertex) :
    Finset (Finset Vertex) := by
  classical exact univ.filter fun Q => D Q ∧ S ⊆ Q

@[simp] theorem mem_blocksThrough {D S Q} : Q ∈ blocksThrough D S ↔ D Q ∧ S ⊆ Q := by
  classical simp [blocksThrough]

/-- All selected mobile-only blocks through the given face. -/
noncomputable def coreBlocks (D : Finset Vertex → Prop) (S : Finset Vertex) :
    Finset (Finset Vertex) := by
  classical exact (blocksThrough D S).filter fun Q => ∀ x ∈ Q, x.val < 17

@[simp] theorem mem_coreBlocks {D S Q} :
    Q ∈ coreBlocks D S ↔ (D Q ∧ S ⊆ Q) ∧ ∀ x ∈ Q, x.val < 17 := by
  classical simp [coreBlocks]

/-- Count the triples through S first by choosing the other points, then
by their unique covering block. -/
private theorem replication {D : Finset Vertex → Prop} (h : QuadrupleSeed univ translate D)
    (S : Finset Vertex) (hs : S.card ≤ 3) :
    (blocksThrough D S).card * (4 - S.card).choose (3 - S.card) =
      (20 - S.card).choose (3 - S.card) := by
  classical
  let F (Q : Finset Vertex) := (Q.powersetCard 3).filter (S ⊆ ·)
  have hei : (blocksThrough D S).biUnion F = F univ := by
    ext T
    simp only [F, mem_biUnion, mem_filter, mem_powersetCard, mem_blocksThrough,
      subset_univ, true_and]
    constructor
    · rintro ⟨Q, _, ⟨_, ht⟩, hS⟩
      exact ⟨ht, hS⟩
    · rintro ⟨ht, hS⟩
      obtain ⟨Q, ⟨hQ, hTQ⟩, _⟩ := h.triples T (subset_univ _) ht
      exact ⟨Q, ⟨hQ, hS.trans hTQ⟩, ⟨hTQ, ht⟩, hS⟩
  have dis : (blocksThrough D S : Set (Finset Vertex)).PairwiseDisjoint F := by
    intro A hA B hB hne
    apply disjoint_left.mpr
    intro T ha hb
    have ta := mem_powersetCard.mp (mem_filter.mp ha).1
    have tb := mem_powersetCard.mp (mem_filter.mp hb).1
    exact hne ((h.triples T (subset_univ _) ta.2).unique
      ⟨(mem_blocksThrough.mp hA).1, ta.1⟩ ⟨(mem_blocksThrough.mp hB).1, tb.1⟩)
  have count := card_biUnion dis
  rw [hei, show (F univ).card = (20-S.card).choose (3-S.card) by
    simpa [F] using card_filter_powersetCard_subset S (univ : Finset Vertex) 3 (subset_univ _) hs] at count
  have each (Q) (hQ : Q ∈ blocksThrough D S) :
      (F Q).card = (4 - S.card).choose (3 - S.card) := by
    dsimp only [F]
    rw [card_filter_powersetCard_subset _ _ _ (mem_blocksThrough.mp hQ).2 hs,
      (h.blocks _ (mem_blocksThrough.mp hQ).1).2]
  rw [sum_congr rfl each, sum_const, Nat.nsmul_eq_mul] at count
  exact count.symm

private theorem through_two {D} (h : QuadrupleSeed univ translate D) {S : Finset Vertex}
    (hs : S.card = 2) : (blocksThrough D S).card = 9 := by
  have eq := replication h S (by omega)
  rw [hs] at eq
  change (blocksThrough D S).card * 2 = 18 at eq
  omega

private theorem through_three {D} (h : QuadrupleSeed univ translate D) {S : Finset Vertex}
    (hs : S.card = 3) : (blocksThrough D S).card = 1 := by
  have eq := replication h S (by omega)
  rw [hs] at eq
  simpa using eq

private theorem outside {x : Vertex} (hx : ¬ x.val < 17) : x = 17 ∨ x = 18 ∨ x = 19 := by
  have hv := x.isLt
  rcases (show x.val = 17 ∨ x.val = 18 ∨ x.val = 19 by omega) with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

private theorem core_union_extras (D : Finset Vertex → Prop) (S : Finset Vertex) :
    blocksThrough D S = coreBlocks D S ∪ (blocksThrough D (insert 17 S) ∪
      blocksThrough D (insert 18 S) ∪ blocksThrough D (insert 19 S)) := by
  classical
  ext Q
  simp only [mem_blocksThrough, mem_union, mem_coreBlocks, insert_subset_iff]
  constructor
  · rintro ⟨hd, hs⟩
    by_cases hf : ∀ x ∈ Q, x.val < 17
    · exact Or.inl ⟨⟨hd, hs⟩, hf⟩
    · push Not at hf
      obtain ⟨x, hx, hv⟩ := hf
      rcases outside (by omega : ¬x.val < 17) with rfl | rfl | rfl <;> tauto
  · tauto

theorem core_pair_degree_lower {D} (h : QuadrupleSeed univ translate D)
    {x y : Vertex} (hx : x.val < 17) (hy : y.val < 17) (hxy : x ≠ y) :
    6 ≤ (coreBlocks D {x,y}).card := by
  let S : Finset Vertex := {x,y}
  have hS : S.card = 2 := by simp [S, hxy]
  have hfar (z : Vertex) (hz : 17 ≤ z.val) : z ∉ S := by
    intro hm
    rcases (by simpa [S] using hm : z = x ∨ z = y) with rfl | rfl <;> omega
  have c (z : Vertex) (hz : 17 ≤ z.val) : (blocksThrough D (insert z S)).card = 1 :=
    through_three h (by rw [card_insert_of_notMem (hfar z hz), hS])
  have eq := through_two h hS
  rw [core_union_extras D S] at eq
  have u := card_union_le (coreBlocks D S) (blocksThrough D (insert 17 S) ∪
      blocksThrough D (insert 18 S) ∪ blocksThrough D (insert 19 S))
  have v := card_union_le (blocksThrough D (insert 17 S) ∪ blocksThrough D (insert 18 S))
      (blocksThrough D (insert 19 S))
  have w := card_union_le (blocksThrough D (insert 17 S)) (blocksThrough D (insert 18 S))
  have c₁ := c 17 (by decide)
  have c₂ := c 18 (by decide)
  have c₃ := c 19 (by decide)
  change 6 ≤ (coreBlocks D S).card
  omega

private noncomputable def extraBlocks (D : Finset Vertex → Prop) (S : Finset Vertex) :=
  blocksThrough D (insert 17 S) ∪ blocksThrough D (insert 18 S) ∪ blocksThrough D (insert 19 S)

private theorem card_partition (D : Finset Vertex → Prop) (S : Finset Vertex) :
    (coreBlocks D S).card + (extraBlocks D S).card = (blocksThrough D S).card := by
  apply (card_union_of_disjoint _).symm.trans
    (congrArg card (core_union_extras D S).symm)
  apply disjoint_left.mpr
  intro Q hm he
  have hf := (mem_coreBlocks.mp hm).2
  simp only [mem_union, mem_blocksThrough, insert_subset_iff] at he
  have h₁ : (17 : Vertex) ∉ Q := fun h => (by decide : ¬(17 : Vertex).val < 17) (hf _ h)
  have h₂ : (18 : Vertex) ∉ Q := fun h => (by decide : ¬(18 : Vertex).val < 17) (hf _ h)
  have h₃ : (19 : Vertex) ∉ Q := fun h => (by decide : ¬(19 : Vertex).val < 17) (hf _ h)
  tauto

private theorem core_inclusion_exclusion (D : Finset Vertex → Prop) (S : Finset Vertex) :
    let A := blocksThrough D (insert 17 S)
    let B := blocksThrough D (insert 18 S)
    let C := blocksThrough D (insert 19 S)
    (coreBlocks D S).card + A.card + B.card + C.card + ((A ∩ C) ∩ (B ∩ C)).card =
      (blocksThrough D S).card + (A ∩ B).card + (A ∩ C).card + (B ∩ C).card := by
  intro A B C
  have h₁ := card_union_add_card_inter A B
  have h₂ := card_union_add_card_inter (A ∪ B) C
  have h₃ := card_union_add_card_inter (A ∩ C) (B ∩ C)
  rw [union_inter_distrib_right] at h₂
  have eq := card_partition D S
  change (coreBlocks D S).card + (A ∪ B ∪ C).card = _ at eq
  omega

/-- Of the nine blocks through a mobile pair, two or three contain an
extra point. One block cannot contain both mobile points and all three extras. -/
theorem core_pair_degree {D} (h : QuadrupleSeed univ translate D)
    {x y : Vertex} (hx : x.val < 17) (hy : y.val < 17) (hxy : x ≠ y) :
    (coreBlocks D {x,y}).card = 6 ∨ (coreBlocks D {x,y}).card = 7 := by
  let S : Finset Vertex := {x,y}
  have hS : S.card = 2 := by simp [S, hxy]
  have hm (z : Vertex) (hz : 17 ≤ z.val) : z ∉ S := by
    intro hm
    rcases (by simpa [S] using hm : z = x ∨ z = y) with rfl | rfl <;> omega
  have extend (z : Vertex) (hz : 17 ≤ z.val) :
      ∃ Q ∈ blocksThrough D (insert z S), True := by
    obtain ⟨Q, hQ, _⟩ := h.triples (insert z S) (subset_univ _)
      (by rw [card_insert_of_notMem (hm z hz), hS])
    exact ⟨Q, mem_blocksThrough.mpr hQ, trivial⟩
  obtain ⟨A, ha, _⟩ := extend 17 (by decide)
  obtain ⟨B, hb, _⟩ := extend 18 (by decide)
  obtain ⟨C, hc, _⟩ := extend 19 (by decide)
  have cextra : 2 ≤ (extraBlocks D S).card := by
    by_contra! few
    have one := card_le_one.mp (show (extraBlocks D S).card ≤ 1 by omega)
    have aE : A ∈ extraBlocks D S := mem_union_left _ (mem_union_left _ ha)
    have bE : B ∈ extraBlocks D S := mem_union_left _ (mem_union_right _ hb)
    have cE : C ∈ extraBlocks D S := mem_union_right _ hc
    have eqB : B = A := one _ bE _ aE
    have eqC : C = A := one _ cE _ aE
    subst B
    subst C
    have hsup : insert 17 (insert 18 (insert 19 S)) ⊆ A := by
      have aa := insert_subset_iff.mp (mem_blocksThrough.mp ha).2
      have bb := insert_subset_iff.mp (mem_blocksThrough.mp hb).2
      have cc := insert_subset_iff.mp (mem_blocksThrough.mp hc).2
      exact insert_subset aa.1 (insert_subset bb.1 (insert_subset cc.1 aa.2))
    have sz : (insert 17 (insert 18 (insert 19 S))).card = 5 := by
      simp [hm 17 (by decide), hm 18 (by decide), hm 19 (by decide), hS]
    have small := card_le_card hsup
    rw [sz, (h.blocks A (mem_blocksThrough.mp ha).1).2] at small
    contradiction
  have eq := card_partition D S
  rw [through_two h hS] at eq
  have lo : 6 ≤ (coreBlocks D S).card := core_pair_degree_lower h hx hy hxy
  change (coreBlocks D S).card = 6 ∨ (coreBlocks D S).card = 7
  omega

/-- A mobile vertex occurs in 57 blocks. Removing the blocks incident with
at least one of the three extras leaves 32 or 33 mobile-only blocks. -/
theorem core_point_degree {D} (h : QuadrupleSeed univ translate D)
    {x : Vertex} (hx : x.val < 17) :
    (coreBlocks D {x}).card = 32 ∨ (coreBlocks D {x}).card = 33 := by
  classical
  let S : Finset Vertex := {x}
  let F (z : Vertex) := blocksThrough D (insert z S)
  have h1 : S.card = 1 := card_singleton _
  have through := replication h S (by omega)
  rw [h1] at through
  change (blocksThrough D S).card * 3 = 171 at through
  have hm (z : Vertex) (hz : 17 ≤ z.val) : z ∉ S := by
    intro hm
    have e : z = x := mem_singleton.mp hm
    subst z
    omega
  have count (z : Vertex) (hz : 17 ≤ z.val) : (F z).card = 9 :=
    through_two h (by rw [card_insert_of_notMem (hm z hz), h1])
  have c₁ := count 17 (by decide)
  have c₂ := count 18 (by decide)
  have c₃ := count 19 (by decide)
  have inter (a b : Vertex) : F a ∩ F b = blocksThrough D (insert a (insert b S)) := by
    ext Q
    simp only [F, mem_inter, mem_blocksThrough, insert_subset_iff]
    tauto
  have pair (a b : Vertex) (ha : 17 ≤ a.val) (hb : 17 ≤ b.val) (hne : a ≠ b) :
      (F a ∩ F b).card = 1 := by
    rw [inter]
    apply through_three h
    simp [hne, hm a ha, hm b hb, h1]
  have p₁ := pair 17 18 (by decide) (by decide) (by decide)
  have p₂ := pair 17 19 (by decide) (by decide) (by decide)
  have p₃ := pair 18 19 (by decide) (by decide) (by decide)
  have last : ((F 17 ∩ F 19) ∩ (F 18 ∩ F 19)).card ≤ 1 :=
    (card_le_card inter_subset_left).trans p₂.le
  have total := core_inclusion_exclusion D S
  change (coreBlocks D S).card + (F 17).card + (F 18).card + (F 19).card +
    ((F 17 ∩ F 19) ∩ (F 18 ∩ F 19)).card = _ at total
  change _ = (blocksThrough D S).card + (F 17 ∩ F 18).card + (F 17 ∩ F 19).card +
    (F 18 ∩ F 19).card at total
  change (coreBlocks D S).card = 32 ∨ (coreBlocks D S).card = 33
  omega

/-- Every Steiner quadruple system on 20 points contains 140 blocks avoiding
any specified three points. Here the three extras are 17, 18 and 19. -/
theorem core_card {D} (h : QuadrupleSeed univ translate D) : (coreBlocks D ∅).card = 140 := by
  let F (z : Vertex) := blocksThrough D {z}
  have through := replication h ∅ (by simp)
  change (blocksThrough D ∅).card * 4 = 1140 at through
  have count (z : Vertex) : (F z).card = 57 := by
    have eq := replication h {z} (by simp)
    rw [card_singleton] at eq
    change (F z).card * 3 = 171 at eq
    omega
  have c₁ := count 17
  have c₂ := count 18
  have c₃ := count 19
  have inter (a b : Vertex) : F a ∩ F b = blocksThrough D {a,b} := by
    ext Q
    simp only [F, mem_inter, mem_blocksThrough, insert_subset_iff, singleton_subset_iff]
    tauto
  have pair (a b : Vertex) (hne : a ≠ b) : (F a ∩ F b).card = 9 := by
    rw [inter]
    exact through_two h (by simp [hne])
  have p₁ := pair 17 18 (by decide)
  have p₂ := pair 17 19 (by decide)
  have p₃ := pair 18 19 (by decide)
  have triple : (F 17 ∩ F 19) ∩ (F 18 ∩ F 19) = blocksThrough D {17,18,19} := by
    ext Q
    simp only [F, mem_inter, mem_blocksThrough, singleton_subset_iff, insert_subset_iff]
    tauto
  have tr := through_three h (S := {17,18,19}) (by decide)
  rw [← triple] at tr
  have total := core_inclusion_exclusion D ∅
  change (coreBlocks D ∅).card + (F 17).card + (F 18).card + (F 19).card +
    ((F 17 ∩ F 19) ∩ (F 18 ∩ F 19)).card = (blocksThrough D ∅).card +
    (F 17 ∩ F 18).card + (F 17 ∩ F 19).card + (F 18 ∩ F 19).card at total
  omega

end Erdos835.TwentyPoint
