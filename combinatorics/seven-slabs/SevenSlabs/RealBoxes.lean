module

public import SevenSlabs.Grid
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! Closed, axis-aligned real boxes reduce to unit-cell tilings with unchanged dimensions. -/

@[expose] public section

namespace SevenSlabs

structure RealBox where
  lo : Axis → ℝ
  size : Triple

noncomputable def RealBox.weight (b : RealBox) (a : Axis) (t : ℝ) : Nat :=
  if b.lo a ≤ t ∧ t < b.lo a + b.size.along a then 1 else 0

/-- Boxes of positive lengths lie in [0,s)³, and exactly one box contains
each point in that half-open cube. Both s and all lower corners are real. -/
structure RealTiling (s : ℝ) (bs : List RealBox) : Prop where
  pos : ∀ b ∈ bs, ∀ a, 0 < b.size.along a
  lower : ∀ b ∈ bs, ∀ a, 0 ≤ b.lo a
  upper : ∀ b ∈ bs, ∀ a, b.lo a + b.size.along a ≤ s
  cover : ∀ x : ℝ, 0 ≤ x → x < s → ∀ y : ℝ, 0 ≤ y → y < s →
          ∀ z : ℝ, 0 ≤ z → z < s →
    (bs.map (fun b => b.weight .x x * b.weight .y y * b.weight .z z)).sum = 1

noncomputable def RealBox.grid (b : RealBox) : Box :=
  ⟨⟨⌈b.lo .x⌉₊, ⌈b.lo .y⌉₊, ⌈b.lo .z⌉₊⟩, b.size⟩

theorem RealBox.grid_lo (b : RealBox) (a : Axis) :
    b.grid.lo.along a = ⌈b.lo a⌉₊ := by cases a <;> rfl

theorem RealBox.grid_weight (b : RealBox) (a : Axis) (i : Nat) (h : 0 ≤ b.lo a) :
    b.grid.weight a i = b.weight a (i : ℝ) := by
  simp only [Box.weight, hit, RealBox.weight, grid_lo]
  change (if ⌈b.lo a⌉₊ ≤ i ∧ i < ⌈b.lo a⌉₊ + b.size.along a then 1 else 0) = _
  simp only [← Nat.ceil_add_natCast h, Nat.ceil_le, Nat.lt_ceil]

theorem RealTiling.toGrid {s : ℝ} {bs : List RealBox} (H : RealTiling s bs) :
    Tiling ⌈s⌉₊ (bs.map RealBox.grid) := by
  constructor
  · intro b hb a
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
    exact H.pos r hr a
  · intro b hb a
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
    rw [RealBox.grid_lo]
    change ⌈r.lo a⌉₊ + r.size.along a ≤ ⌈s⌉₊
    rw [← Nat.ceil_add_natCast (H.lower r hr a)]
    exact Nat.ceil_mono (H.upper r hr a)
  · intro x hx y hy z hz
    rw [List.map_map]
    refine Eq.trans (congrArg List.sum (List.map_congr_left ?_))
      (H.cover x (Nat.cast_nonneg x) (Nat.lt_ceil.mp hx)
               y (Nat.cast_nonneg y) (Nat.lt_ceil.mp hy)
               z (Nat.cast_nonneg z) (Nat.lt_ceil.mp hz))
    intro b hb
    simp only [Function.comp_apply, b.grid_weight _ _ (H.lower b hb _)]

/-- There is another point to the right before any of a finite set of endpoints. -/
private theorem finite_gap {p s : ℝ} (hp : p < s) (ends : List ℝ) :
    ∃ q, p < q ∧ q < s ∧ ∀ e ∈ ends, p < e → q < e := by
  induction ends generalizing s with
  | nil => obtain ⟨q,h₁,h₂⟩ := exists_between hp; exact ⟨q,h₁,h₂,by simp⟩
  | cons e es ih =>
    by_cases h : p < e
    · obtain ⟨q,hq,hu,he⟩ := ih (s := min s e) (lt_min hp h)
      exact ⟨q,hq,lt_of_lt_of_le hu (min_le_left _ _),fun v hv hvp => by
        rcases List.mem_cons.mp hv with rfl | hv
        · exact lt_of_lt_of_le hu (min_le_right _ _)
        · exact he v hv hvp⟩
    · obtain ⟨q,hq,hu,he⟩ := ih hp
      exact ⟨q,hq,hu,fun v hv hvp => by
        rcases List.mem_cons.mp hv with rfl | hv
        · exact (h hvp).elim
        · exact he v hv hvp⟩

private theorem indicator_sum {α : Type*} (P : α → Prop) [DecidablePred P] (xs : List α)
    (someP : ∃ b ∈ xs, P b) (unique : xs.Pairwise (fun b c => P b → ¬ P c)) :
    (xs.map (fun b => if P b then 1 else 0)).sum = (1 : Nat) := by
  induction xs with
  | nil => simp at someP
  | cons b bs ih =>
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp unique
    by_cases hb : P b
    · have hz : bs.map (fun c => if P c then 1 else 0) = bs.map (fun _ => (0 : Nat)) :=
        List.map_congr_left (fun c hc => ite_eq_right (head c hc hb))
      simp [hb, hz]
    · simp only [List.map_cons, List.sum_cons, ite_eq_right hb, Nat.zero_add]
      apply ih _ tail
      simpa [hb] using someP

/-- The usual closed-box convention: containment, complete coverage, and
pairwise disjoint open interiors. -/
structure ClosedTiling (s : ℝ) (bs : List RealBox) : Prop where
  pos : ∀ b ∈ bs, ∀ a, 0 < b.size.along a
  lower : ∀ b ∈ bs, ∀ a, 0 ≤ b.lo a
  upper : ∀ b ∈ bs, ∀ a, b.lo a + b.size.along a ≤ s
  cover : ∀ p : Axis → ℝ, (∀ a, 0 ≤ p a ∧ p a ≤ s) →
    ∃ b ∈ bs, ∀ a, b.lo a ≤ p a ∧ p a ≤ b.lo a + b.size.along a
  disjoint : bs.Pairwise (fun b c => ∀ p : Axis → ℝ,
    (∀ a, b.lo a < p a ∧ p a < b.lo a + b.size.along a) →
    ¬ (∀ a, c.lo a < p a ∧ p a < c.lo a + c.size.along a))

/-- A small positive displacement resolves all shared boundaries consistently. -/
theorem ClosedTiling.toHalfOpen {s : ℝ} {bs : List RealBox} (h : ClosedTiling s bs) :
    RealTiling s bs := by
  obtain ⟨pos, lower, upper, cover, disjoint⟩ := h
  classical
  refine ⟨pos,lower,upper,?_⟩
  intro x hx hx' y hy hy' z hz hz'
  let p : Axis → ℝ := fun | .x => x | .y => y | .z => z
  have hp (a : Axis) : 0 ≤ p a ∧ p a < s := by cases a <;> simp_all [p]
  let ends (a : Axis) := bs.flatMap (fun b => [b.lo a, b.lo a + (b.size.along a : ℝ)])
  choose q hpq hqs gap using (fun a => finite_gap (hp a).2 (ends a))
  have qcube a : 0 ≤ q a ∧ q a ≤ s :=
    ⟨le_trans (hp a).1 (hpq a).le, (hqs a).le⟩
  let P (b : RealBox) := ∀ a, b.lo a ≤ p a ∧ p a < b.lo a + b.size.along a
  have enters {b : RealBox} (hb : b ∈ bs) (h : P b) (a : Axis) :
      b.lo a < q a ∧ q a < b.lo a + b.size.along a :=
    ⟨lt_of_le_of_lt (h a).1 (hpq a), gap a _ (List.mem_flatMap.mpr ⟨b,hb, by simp⟩) (h a).2⟩
  obtain ⟨b,hb,hclosed⟩ := cover q qcube
  have hP : P b := by
    intro a
    refine ⟨le_of_not_gt (fun hg => ?_), lt_of_lt_of_le (hpq a) (hclosed a).2⟩
    exact (not_lt_of_ge (hclosed a).1) (gap a _ (List.mem_flatMap.mpr ⟨b,hb,by simp⟩) hg)
  have only : bs.Pairwise (fun b c => P b → ¬ P c) := by
    apply List.Pairwise.imp_of_mem _ disjoint
    intro u v hu hv h tuv tv
    exact h q (enters hu tuv) (enters hv tv)
  have sum := indicator_sum P bs ⟨b,hb,hP⟩ only
  refine Eq.trans (congrArg List.sum (List.map_congr_left ?_)) sum
  intro c _
  have char : P c ↔
      (c.lo .x ≤ x ∧ x < c.lo .x + c.size.along .x) ∧
      (c.lo .y ≤ y ∧ y < c.lo .y + c.size.along .y) ∧
      (c.lo .z ≤ z ∧ z < c.lo .z + c.size.along .z) := by
    constructor
    · exact fun h => ⟨h .x,h .y,h .z⟩
    · intro h a
      cases a with
      | x => exact h.1
      | y => exact h.2.1
      | z => exact h.2.2
  simp only [RealBox.weight, char]
  split_ifs <;> simp_all
end SevenSlabs
