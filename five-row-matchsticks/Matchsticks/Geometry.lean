import Matchsticks.Basic

/-! Lattice coordinates for a board, definition of an intact axis-aligned
rectangle, and soundness of the column-scan state used for the upper bound. -/
namespace Matchsticks

/-- The vertical sticks at lattice column `x`, indexed by their top row `0..4`. -/
def Board.verticalAt : Board → Nat → Nat
  | .left v, x => if x = 0 then v.val else 0
  | .snoc b _ v, x => if x = b.width + 1 then v.val else b.verticalAt x

/-- The horizontal sticks from column `x` to `x+1`, indexed by grid line `0..5`. -/
def Board.horizontalAt : Board → Nat → Nat
  | .left _, _ => 0
  | .snoc b h _, x => if x = b.width then h.val else b.horizontalAt x

/-- Every unit vertical stick from row `a` to row `d` survives at column `x`. -/
def Board.verticalSide (b : Board) (x a d : Nat) : Prop :=
  ∀ i, a ≤ i → i < d → (b.verticalAt x).testBit i = true

/-- Both horizontal sides from column `x` to column `y` survive at lines `a` and `d`. -/
def Board.horizontalSides (b : Board) (x y a d : Nat) : Prop :=
  ∀ k, x ≤ k → k < y →
    (b.horizontalAt k).testBit a = true ∧ (b.horizontalAt k).testBit d = true

/-- A positive-area axis-aligned rectangle on the lattice with all four sides intact. -/
def Board.HasRectangle (b : Board) : Prop :=
  ∃ x y a d : Nat, x < y ∧ y ≤ b.width ∧ a < d ∧ d < 6 ∧
    b.verticalSide x a d ∧ b.verticalSide y a d ∧ b.horizontalSides x y a d

private def OpenPair (b : Board) (p : RowPair) : Prop :=
  ∃ x, x ≤ b.width ∧ b.verticalSide x (top p) (bottom p) ∧
    b.horizontalSides x b.width (top p) (bottom p)

private theorem vertical_old {b : Board} {h : HMask} {v : VMask} {x a d : Nat}
    (hx : x ≤ b.width) (hs : (b.snoc h v).verticalSide x a d) : b.verticalSide x a d := by
  intro i hlo hhi
  have hx' : x ≠ b.width + 1 := by omega
  simpa only [Board.verticalAt, ite_eq_right hx'] using hs i hlo hhi

private theorem horizontal_old {b : Board} {h : HMask} {v : VMask} {x y a d : Nat}
    (hy : y ≤ b.width) (hs : (b.snoc h v).horizontalSides x y a d) : b.horizontalSides x y a d := by
  intro k hlo hhi
  have hk' : k ≠ b.width := by omega
  simpa only [Board.horizontalAt, ite_eq_right hk'] using hs k hlo hhi

private theorem open_implies_state (b : Board) (p : RowPair) :
    OpenPair b p → b.state.testBit p.val = true := by
  induction b with
  | left v =>
    rintro ⟨x, hx, side, _⟩
    have hx0 : x = 0 := by change x ≤ 0 at hx; omega
    subst hx0
    exact (vPairs_bit v p).mpr fun i hlo hhi => by
      simpa [Board.verticalAt] using side i hlo hhi
  | snoc b h v ih =>
    rintro ⟨x, hx, side, rails⟩
    change x ≤ b.width + 1 at hx
    simp only [Board.state, advance, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_true,
      Bool.and_eq_true]
    by_cases hlast : x = b.width + 1
    · subst hlast
      exact Or.inr ((vPairs_bit v p).mpr fun i hlo hhi => by
        simpa [Board.verticalAt] using side i hlo hhi)
    · have hx' : x ≤ b.width := by omega
      have hprev : OpenPair b p :=
        ⟨x, hx', vertical_old hx' side,
          horizontal_old (Nat.le_refl _) (fun k h₁ h₂ => rails k h₁ (by simp only [Board.width]; omega))⟩
      have hstep : (hPairs h).testBit p.val = true := by
        rw [hPairs_bit, Bool.and_eq_true]
        simpa [Board.horizontalAt] using rails b.width hx' (by simp only [Board.width]; omega)
      exact Or.inl ⟨ih hprev, hstep⟩

/-- A board accepted by the column scan contains no intact positive-area rectangle. -/
theorem no_rectangle_of_safe (b : Board) : b.safe → ¬ b.HasRectangle := by
  induction b with
  | left v =>
    intro _ ⟨x, y, _, _, hxy, hy, _⟩
    change y ≤ 0 at hy
    omega
  | snoc b h v ih =>
    rintro ⟨hsafe, hleg⟩ ⟨x, y, a, d, hxy, hy, had, hd, left, right, rails⟩
    change y ≤ b.width + 1 at hy
    by_cases hlast : y = b.width + 1
    · subst hlast
      obtain ⟨p, rfl, rfl⟩ := all_pairs a d had hd
      have hx' : x ≤ b.width := by omega
      have hopen : OpenPair b p :=
        ⟨x, hx', vertical_old hx' left,
          horizontal_old (Nat.le_refl _) (fun k h₁ h₂ => rails k h₁ (by omega))⟩
      have hstep : (hPairs h).testBit p.val = true := by
        rw [hPairs_bit, Bool.and_eq_true]
        simpa [Board.horizontalAt] using rails b.width hx' (by omega)
      have hright : (vPairs v).testBit p.val = true :=
        (vPairs_bit v p).mpr fun i hlo hhi => by
          simpa [Board.verticalAt] using right i hlo hhi
      exact legal_elim hleg p ⟨open_implies_state b p hopen, hstep, hright⟩
    · have hy' : y ≤ b.width := by omega
      exact ih hsafe ⟨x, y, a, d, hxy, hy', had, hd,
        vertical_old (by omega) left, vertical_old hy' right, horizontal_old hy' rails⟩

end Matchsticks
