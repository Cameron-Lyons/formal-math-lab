import Matchsticks.Basic

namespace Matchsticks

/-- The vertical edges at lattice column `x`, indexed by their lower row. -/
def Board.verticalAt : Board → Nat → Nat
  | .left v, x => if x = 0 then v.val else 0
  | .snoc b _ v, x => if x = b.width + 1 then v.val else b.verticalAt x

/-- The horizontal edges from lattice column `x` to `x+1`, indexed by row. -/
def Board.horizontalAt : Board → Nat → Nat
  | .left _, _ => 0
  | .snoc b h _, x => if x = b.width then h.val else b.horizontalAt x

/-- Every unit edge from row `a` to row `d` survives at column `x`. -/
def Board.verticalSide (b : Board) (x a d : Nat) : Prop :=
  ∀ i, a ≤ i → i < d → (b.verticalAt x).testBit i = true

/-- Both horizontal sides from column `x` to column `y` survive. -/
def Board.horizontalSides (b : Board) (x y a d : Nat) : Prop :=
  ∀ k, x ≤ k → k < y →
    (b.horizontalAt k).testBit a = true ∧ (b.horizontalAt k).testBit d = true

/-- A positive-area axis-aligned rectangle on the actual lattice with four complete sides. -/
def Board.HasRectangle (b : Board) : Prop :=
  ∃ x y a d : Nat, x < y ∧ y ≤ b.width ∧ a < d ∧ d < 6 ∧
    b.verticalSide x a d ∧ b.verticalSide y a d ∧ b.horizontalSides x y a d

private def OpenPair (b : Board) (p : RowPair) : Prop :=
  ∃ x, x ≤ b.width ∧ b.verticalSide x (top p) (bottom p) ∧
    b.horizontalSides x b.width (top p) (bottom p)

private theorem vertical_old {b : Board} {h : HMask} {v : VMask} {x a d : Nat}
    (hx : x ≤ b.width) :
    (b.snoc h v).verticalSide x a d ↔ b.verticalSide x a d := by
  have hx' : x ≠ b.width + 1 := by omega
  simp only [Board.verticalSide, Board.verticalAt, ite_eq_right hx']

private theorem vertical_last (b : Board) (h : HMask) (v : VMask) (p : RowPair) :
    (b.snoc h v).verticalSide (b.width + 1) (top p) (bottom p) ↔
      (vPairs v).testBit p.val = true := by
  simp [Board.verticalSide, Board.verticalAt, vPairs_bit]

private theorem horizontal_old {b : Board} {h : HMask} {v : VMask} {x y a d : Nat}
    (hy : y ≤ b.width) :
    (b.snoc h v).horizontalSides x y a d ↔ b.horizontalSides x y a d := by
  constructor <;> intro sides k hx hk
  all_goals
    have hk' : k ≠ b.width := by omega
    simpa only [Board.horizontalAt, ite_eq_right hk'] using sides k hx hk

private theorem horizontal_extend {b : Board} {h : HMask} {v : VMask} {x : Nat}
    (hx : x ≤ b.width) (p : RowPair) :
    (b.snoc h v).horizontalSides x (b.width + 1) (top p) (bottom p) ↔
      b.horizontalSides x b.width (top p) (bottom p) ∧
        (hPairs h).testBit p.val = true := by
  rw [hPairs_bit, Bool.and_eq_true]
  constructor
  · intro sides
    refine ⟨(horizontal_old (h := h) (v := v) (Nat.le_refl _)).mp ?_, ?_⟩
    · exact fun k h₁ h₂ => sides k h₁ (by omega)
    · simpa [Board.horizontalAt] using sides b.width hx (by omega)
  · rintro ⟨old, last⟩ k hk₁ hk₂
    by_cases hk : k = b.width
    · subst k
      simpa [Board.horizontalAt] using last
    · simpa only [Board.horizontalAt, ite_eq_right hk] using old k hk₁ (by omega)

private theorem open_snoc (b : Board) (h : HMask) (v : VMask) (p : RowPair) :
    OpenPair (b.snoc h v) p ↔
      (OpenPair b p ∧ (hPairs h).testBit p.val = true) ∨ (vPairs v).testBit p.val = true := by
  constructor
  · rintro ⟨x, hx, side, rails⟩
    change x ≤ b.width + 1 at hx
    by_cases last : x = b.width + 1
    · subst x
      exact Or.inr ((vertical_last b h v p).mp side)
    · have hx' : x ≤ b.width := by omega
      obtain ⟨rails', bit⟩ := (horizontal_extend hx' p).mp rails
      exact Or.inl ⟨⟨x, hx', (vertical_old hx').mp side, rails'⟩, bit⟩
  · rintro (⟨⟨x, hx, side, rails⟩, bit⟩ | bit)
    · exact ⟨x, Nat.le_succ_of_le hx, (vertical_old hx).mpr side,
        (horizontal_extend hx p).mpr ⟨rails, bit⟩⟩
    · exact ⟨b.width + 1, Nat.le_refl _, (vertical_last b h v p).mpr bit,
        fun _ h₁ h₂ => by change _ < b.width + 1 at h₂; omega⟩

private theorem state_geometry (b : Board) (p : RowPair) :
    b.state.testBit p.val = true ↔ OpenPair b p := by
  induction b with
  | left v =>
    change (vPairs v).testBit p.val = true ↔ _
    rw [vPairs_bit]
    constructor
    · intro edges
      exact ⟨0, Nat.le_refl _, by simpa [Board.verticalSide, Board.verticalAt] using edges,
        fun _ _ h => by change _ < 0 at h; omega⟩
    · rintro ⟨x, hx, edges, _⟩
      change x ≤ 0 at hx
      have heq : x = 0 := by omega
      subst x
      simpa [Board.verticalSide, Board.verticalAt] using edges
  | snoc b h v ih =>
    rw [open_snoc]
    simp only [Board.state, advance, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_true,
      Bool.and_eq_true, ih]

private theorem rectangle_snoc (b : Board) (h : HMask) (v : VMask) :
    (b.snoc h v).HasRectangle ↔ b.HasRectangle ∨
      ∃ p : RowPair, OpenPair b p ∧ (hPairs h).testBit p.val = true ∧
        (vPairs v).testBit p.val = true := by
  constructor
  · rintro ⟨x, y, a, d, hxy, hy, had, hd, left, right, rails⟩
    change y ≤ b.width + 1 at hy
    by_cases hlast : y = b.width + 1
    · subst y
      obtain ⟨p, rfl, rfl⟩ := all_pairs a d had hd
      have hx : x ≤ b.width := by omega
      obtain ⟨old, bit⟩ := (horizontal_extend hx p).mp rails
      exact Or.inr ⟨p, ⟨x, hx, (vertical_old hx).mp left, old⟩, bit, (vertical_last b h v p).mp right⟩
    · have hy' : y ≤ b.width := by omega
      have hx : x ≤ b.width := by omega
      exact Or.inl ⟨x, y, a, d, hxy, hy', had, hd, (vertical_old hx).mp left,
        (vertical_old hy').mp right, (horizontal_old hy').mp rails⟩
  · rintro (⟨x, y, a, d, hxy, hy, had, hd, left, right, rails⟩ |
      ⟨p, ⟨x, hx, left, rails⟩, bit, side⟩)
    · exact ⟨x, y, a, d, hxy, Nat.le_succ_of_le hy, had, hd,
        (vertical_old (Nat.le_trans (Nat.le_of_lt hxy) hy)).mpr left, (vertical_old hy).mpr right,
        (horizontal_old hy).mpr rails⟩
    · obtain ⟨had, hd⟩ := pair_bounds p
      exact ⟨x, b.width + 1, top p, bottom p, by omega, Nat.le_refl _, had, hd,
        (vertical_old hx).mpr left, (vertical_last b h v p).mpr side,
        (horizontal_extend hx p).mpr ⟨rails, bit⟩⟩

/-- The scan accepts exactly those boards with no intact positive-area rectangle. -/
theorem safe_iff_no_rectangle (b : Board) : b.safe ↔ ¬ b.HasRectangle := by
  induction b with
  | left v =>
    constructor
    · intro _ ⟨x, y, _, _, hxy, hy, _⟩
      change y ≤ 0 at hy
      omega
    · intro _
      trivial
  | snoc b h v ih =>
    change b.safe ∧ legal b.state h v ↔ _
    rw [ih, legal_iff, rectangle_snoc]
    simp only [state_geometry, not_or, not_exists]

end Matchsticks
