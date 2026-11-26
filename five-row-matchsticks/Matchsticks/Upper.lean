import Matchsticks.Basic

namespace Matchsticks

private def first : Board := .snoc (.left 31) 37 26
private def second : Board := .snoc first 47 13
private def third : Board := .snoc second 59 22

/-- Starting at width three, the next six columns repeat. Each entry gives
the state before the column and its two masks of surviving sticks. -/
private structure Column where
  before : Nat
  horizontal : HMask
  vertical : VMask

private def pattern (i : Fin 6) : Column :=
  match i.val with
  | 0 => ⟨29297, 53, 15⟩
  | 1 => ⟨22271, 45, 26⟩
  | 2 => ⟨29238, 55, 13⟩
  | 3 => ⟨22067, 43, 30⟩
  | 4 => ⟨32753, 45, 11⟩
  | _ => ⟨14899, 59, 22⟩

private def phase (k : Nat) : Fin 6 := ⟨k % 6, Nat.mod_lt _ (by decide)⟩

private theorem phase_succ (k : Nat) :
    phase (k+1) = phase ((phase k).val + 1) := by
  apply Fin.ext
  simp only [phase]
  omega

private theorem checkCycle : ∀ i : Fin 6,
    let p := pattern i
    legal p.before p.horizontal p.vertical ∧
    advance p.before p.horizontal p.vertical = (pattern (phase (i.val+1))).before ∧
    hCost p.horizontal + vCost p.vertical = (if i.val % 3 = 1 then 4 else 3) := by
  decide

private theorem prefixOne : first.width = 1 ∧ first.safe ∧ first.cost = target 1 := by
  simp only [first, Board.safe]
  decide

private theorem prefixTwo : second.width = 2 ∧ second.safe ∧ second.cost = target 2 := by
  simp only [second, first, Board.safe]
  decide

private theorem prefixThree : third.width = 3 ∧ third.state = (pattern (phase 0)).before ∧
    third.safe ∧ third.cost = target 3 := by
  simp only [third, second, first, Board.safe]
  decide

private theorem extendPattern (k : Nat) :
    ∃ b : Board, b.width = k+3 ∧ b.state = (pattern (phase k)).before ∧
      b.safe ∧ b.cost = target (k+3) := by
  induction k with
  | zero => exact ⟨third, prefixThree⟩
  | succ k ih =>
    obtain ⟨b, bw, bs, safe, cost⟩ := ih
    let p := pattern (phase k)
    obtain ⟨stepSafe, stepState, stepCost⟩ := checkCycle (phase k)
    refine ⟨.snoc b p.horizontal p.vertical, ?_, ?_, ?_, ?_⟩
    · simp only [Board.width, bw]
    · simp only [Board.state, bs, p, stepState]
      rw [phase_succ k]
    · exact ⟨safe, bs ▸ stepSafe⟩
    · simp only [Board.cost, cost, p, stepCost]
      have h₃ : k + 3 ≠ 1 := by omega
      have h₄ : k + 1 + 3 ≠ 1 := by omega
      simp only [phase, target, ite_eq_right h₃, ite_eq_right h₄]
      by_cases hk : k % 3 = 1 <;> simp [hk] <;> omega

/-- At each positive width the indicated number of erased sticks is attained. -/
theorem attainable (n : Nat) (hn : 0 < n) :
    ∃ b : Board, b.width = n ∧ b.safe ∧ b.cost = target n := by
  match n with
  | 0 => omega
  | 1 => exact ⟨first, prefixOne⟩
  | 2 => exact ⟨second, prefixTwo⟩
  | k+3 =>
    obtain ⟨b, hw, _, hs, hc⟩ := extendPattern k
    exact ⟨b, hw, hs, hc⟩

end Matchsticks
