import Matchsticks.Basic

/-! Explicit construction attaining 5 erasures at width 1 and ⌊(10n + 4)/3⌋
erasures at every width n ≥ 2.

After two starting columns, the construction alternates a three-column block
(A, B, C) with its top-to-bottom reflection. From width three onward, the
frontier state repeats with period six. -/
namespace Matchsticks

/-- Surviving horizontal-stick mask after erasing the listed grid lines `0..5`. -/
private def hErase (es : List Nat) : HMask :=
  ⟨es.foldl (fun m i => m &&& (63 - (1 <<< i))) 63,
    by have : ∀ acc, acc < 64 → ∀ xs : List Nat,
        xs.foldl (fun m i => m &&& (63 - (1 <<< i))) acc < 64 := by
        intro acc hacc xs
        induction xs generalizing acc with
        | nil => exact hacc
        | cons x xs ih => exact ih _ (Nat.lt_of_le_of_lt Nat.and_le_left hacc)
       exact this 63 (by decide) es⟩

/-- Surviving vertical-stick mask after erasing the listed edges `0..4`. -/
private def vErase (es : List Nat) : VMask :=
  ⟨es.foldl (fun m i => m &&& (31 - (1 <<< i))) 31,
    by have : ∀ acc, acc < 32 → ∀ xs : List Nat,
        xs.foldl (fun m i => m &&& (31 - (1 <<< i))) acc < 32 := by
        intro acc hacc xs
        induction xs generalizing acc with
        | nil => exact hacc
        | cons x xs ih => exact ih _ (Nat.lt_of_le_of_lt Nat.and_le_left hacc)
       exact this 31 (by decide) es⟩

/-- One column's erased horizontal lines and erased right-boundary vertical edges. -/
private def colSpec (hs vs : List Nat) : HMask × VMask := (hErase hs, vErase vs)

/-- Top-to-bottom reflection of a column specification: `h ↦ 5 - h`, `v ↦ 4 - v`. -/
private def reflectSpec (hs vs : List Nat) : HMask × VMask :=
  colSpec (hs.map (5 - ·)) (vs.map (4 - ·))

private def start1 : HMask × VMask := colSpec [1, 3, 4] [0, 2]
private def start2 : HMask × VMask := colSpec [4] [1, 4]
private def colA   : HMask × VMask := colSpec [2] [0, 3]
private def colB   : HMask × VMask := colSpec [1, 3] [4]
private def colC   : HMask × VMask := colSpec [1, 4] [0, 2]
private def colA'  : HMask × VMask := reflectSpec [2] [0, 3]
private def colB'  : HMask × VMask := reflectSpec [1, 3] [4]
private def colC'  : HMask × VMask := reflectSpec [1, 4] [0, 2]

private def first  : Board := .snoc (.left ⟨31, by decide⟩) start1.1 start1.2
private def second : Board := .snoc first start2.1 start2.2
private def third  : Board := .snoc second colA.1 colA.2

/-- The six repeating columns starting after `third`: B, C, A', B', C', A. -/
private def cycleCol (i : Fin 6) : HMask × VMask :=
  match i.val with
  | 0 => colB
  | 1 => colC
  | 2 => colA'
  | 3 => colB'
  | 4 => colC'
  | _ => colA

private def phase (k : Nat) : Fin 6 := ⟨k % 6, Nat.mod_lt _ (by decide)⟩

/-- Frontier state after `i` steps of the repeating cycle starting from `third.state`. -/
private def cycleState : Nat → Nat
  | 0 => third.state
  | i + 1 =>
      let c := cycleCol (phase i)
      advance (cycleState i) c.1 c.2

private theorem cycleState_period : cycleState 6 = cycleState 0 := by decide

private theorem cycleCheck : ∀ i : Fin 6,
    let c := cycleCol i
    legal (cycleState i.val) c.1 c.2 ∧
    hCost c.1 + vCost c.2 = (if i.val % 3 = 1 then 4 else 3) := by decide

private theorem cycleState_step (i : Fin 6) :
    advance (cycleState i.val) (cycleCol i).1 (cycleCol i).2 = cycleState ((i.val + 1) % 6) := by
  have h : ∀ j : Fin 6,
      advance (cycleState j.val) (cycleCol j).1 (cycleCol j).2 =
        cycleState ((j.val + 1) % 6) := by decide
  exact h i

private theorem prefixOne : first.width = 1 ∧ first.safe ∧ first.cost = target 1 := by
  simp only [first, Board.safe]
  decide

private theorem prefixTwo : second.width = 2 ∧ second.safe ∧ second.cost = target 2 := by
  simp only [second, first, Board.safe]
  decide

private theorem prefixThree : third.width = 3 ∧ third.state = cycleState 0 ∧
    third.safe ∧ third.cost = target 3 := by
  simp only [third, second, first, Board.safe, cycleState]
  decide

private theorem extendPattern (k : Nat) :
    ∃ b : Board, b.width = k + 3 ∧ b.state = cycleState (phase k).val ∧
      b.safe ∧ b.cost = target (k + 3) := by
  induction k with
  | zero => exact ⟨third, prefixThree⟩
  | succ k ih =>
    obtain ⟨b, bw, bs, hsafe, hcost⟩ := ih
    let i := phase k
    let c := cycleCol i
    obtain ⟨stepSafe, stepCost⟩ := cycleCheck i
    refine ⟨.snoc b c.1 c.2, ?_, ?_, ?_, ?_⟩
    · simp only [Board.width, bw]
    · simp only [Board.state, bs, c]
      rw [cycleState_step i]
      congr 1
      simp only [i, phase]
      omega
    · exact ⟨hsafe, bs ▸ stepSafe⟩
    · simp only [Board.cost, hcost, c, stepCost]
      have h₃ : k + 3 ≠ 1 := by omega
      have h₄ : k + 1 + 3 ≠ 1 := by omega
      simp only [i, phase, target, ite_eq_right h₃, ite_eq_right h₄]
      by_cases hk : k % 3 = 1 <;> simp [hk] <;> omega

/-- Every positive width attains the target number of erased sticks with no rectangle. -/
theorem attainable (n : Nat) (hn : 0 < n) :
    ∃ b : Board, b.width = n ∧ b.safe ∧ b.cost = target n := by
  match n with
  | 0 => omega
  | 1 => exact ⟨first, prefixOne⟩
  | 2 => exact ⟨second, prefixTwo⟩
  | k + 3 =>
    obtain ⟨b, hw, _, hs, hc⟩ := extendPattern k
    exact ⟨b, hw, hs, hc⟩

end Matchsticks
