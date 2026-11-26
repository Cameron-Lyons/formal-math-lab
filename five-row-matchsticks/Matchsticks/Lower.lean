import Matchsticks.StateSets

/-! # A certificate for the lower bound

For a safe board of positive width, the invariant supplies a budget `k ≥ 2`
with `10 * width + k ≤ 3 * cost`. The initial and single-column checks are
closed finite propositions proved by ordinary `decide`. Induction then
applies the bound at every width. -/
namespace Matchsticks.BitSets

/-- Bitwise inclusion checks all active states at once. -/
def included (a b : Nat) : Prop := a &&& b = a
instance (a b : Nat) : Decidable (included a b) := inferInstanceAs (Decidable (_ = a))

theorem included_mem {a b x : Nat} (ok : included a b) (hit : a.testBit x = true) :
    b.testBit x = true := by
  have t := congrArg (fun z : Nat => z.testBit x) ok
  simpa [Nat.testBit_and, hit] using t

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem horizontalCheck : ∀ (k : Fin 31) (h : HMask),
    included (horizSource k.val h) (middleSet (min 30 (k.val + 3*hCost h))) := by
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem verticalCheck : ∀ (k : Fin 31) (v : VMask),
    let budget := k.val+3*vCost v
    let a := vertSource k.val v
    if budget < 12 then a = 0
    else included a (potentialSet (min 30 (budget-10)) >>> vPairs v) := by
  decide

/-- Group the first two edge choices by their total cost. The next lemma checks
that these 203 entries cover every possible pair of masks. -/
private def opening : Array (List Nat) := #[
  [32767],
  [5871, 11127, 16999, 19899, 28707, 29149, 32257, 32286, 32736],
  [615, 1195, 2355, 4131, 4301, 5633, 5646, 5856, 5871, 8227, 8533, 10753, 10774, 11104, 16419, 16453, 16793, 16897, 16902, 16992, 19457, 19482, 19872, 28673, 28674, 28700, 28704, 29120, 32256, 32736],
  [35, 69, 137, 273, 513, 518, 608, 615, 1025, 1034, 1184, 1195, 2049, 2066, 2336, 4097, 4098, 4108, 4128, 4131, 4288, 4301, 5632, 5633, 5646, 5856, 8193, 8194, 8212, 8224, 8512, 10752, 11104, 16385, 16386, 16388, 16408, 16416, 16419, 16448, 16768, 16896, 16992, 19456, 19872, 28672, 28673, 28704, 29120, 32256],
  [1, 2, 4, 8, 16, 32, 35, 64, 69, 128, 137, 256, 512, 513, 518, 608, 615, 1024, 1025, 1034, 1184, 2048, 2336, 4096, 4097, 4098, 4108, 4128, 4288, 5632, 5856, 8192, 8193, 8224, 8512, 10752, 16384, 16385, 16386, 16416, 16448, 16768, 16896, 19456, 28672, 32256],
  [0, 1, 2, 4, 8, 32, 35, 64, 69, 128, 256, 512, 513, 518, 608, 1024, 1184, 2048, 4096, 4097, 4128, 4288, 5632, 8192, 10752, 16384, 16385, 16416, 16896, 19456, 28672],
  [0, 1, 2, 4, 32, 35, 64, 128, 512, 608, 1024, 2048, 4096, 5632, 8192, 16384, 28672],
  [0, 1, 2, 32, 64, 512, 1024, 4096, 8192, 16384],
  [0, 1, 32, 512, 4096, 16384],
  [0],
  [0],
  [0]]

private def openingCost (l : VMask) (h : HMask) : Nat := vCost l + hCost h
private def openingState (l : VMask) (h : HMask) : Nat := vPairs l &&& hPairs h

set_option maxRecDepth 10000
set_option maxHeartbeats 0

private theorem openingCovered : ∀ (l : VMask) (h : HMask),
    let d := openingCost l h
    d < 12 ∧ openingState l h ∈ opening[d]! := by decide

private def finalOK (d t : Nat) (v : VMask) : Prop :=
  t &&& vPairs v = 0 →
    let s := t ||| vPairs v
    let c := d + vCost v
    5 ≤ c ∧ s < 32768 ∧ (potentialSet (min 30 (3*c-10))).testBit s = true

private instance (d t : Nat) (v : VMask) : Decidable (finalOK d t v) := by
  unfold finalOK
  infer_instance

private theorem openingChecked : ∀ d : Fin 12,
    (opening[d.val]!).all (fun t => decide (∀ v : VMask, finalOK d.val t v)) = true := by
  decide

/-- Every valid first column meets the initial potential bound. -/
theorem firstColumn (l : VMask) (h : HMask) (v : VMask) (ok : legal (vPairs l) h v) :
    let s := advance (vPairs l) h v
    let c := vCost l + (hCost h + vCost v)
    5 ≤ c ∧ s < 32768 ∧ (potentialSet (min 30 (3*c - 10))).testBit s = true := by
  obtain ⟨bound, mem⟩ := openingCovered l h
  let d : Fin 12 := ⟨openingCost l h, bound⟩
  have check := List.all_eq_true.mp (openingChecked d) (openingState l h) mem
  have result := of_decide_eq_true check v ok
  simpa only [d, openingState, openingCost, advance, Nat.add_assoc] using result

/-- Width and cost are related by a budget in the finite potential table. -/
private def Invariant (b : Board) : Prop :=
  b.state < 32768 ∧ ∃ k : Fin 31, 2 ≤ k.val ∧
    (potentialSet k.val).testBit b.state = true ∧ 10*b.width + k.val ≤ 3*b.cost

private theorem startInvariant (l : VMask) (h : HMask) (v : VMask)
    (ok : legal (vPairs l) h v) : Invariant (.snoc (.left l) h v) := by
  let c := vCost l + (hCost h + vCost v)
  obtain ⟨cost, bound, hit⟩ := firstColumn l h v ok
  change 5 ≤ c at cost
  let budget : Fin 31 := ⟨min 30 (3*c-10), by omega⟩
  refine ⟨bound, budget, ?_, hit, ?_⟩
  · change 2 ≤ min 30 (3*c-10)
    omega
  · change 10*1 + min 30 (3*c-10) ≤ 3*c
    omega

private theorem nextInvariant (b : Board) (h : HMask) (v : VMask)
    (ih : Invariant b) (ok : legal b.state h v) : Invariant (.snoc b h v) := by
  obtain ⟨bound, k, _, hit, credit⟩ := ih
  let t := b.state &&& hPairs h
  have ht : t < 32768 := Nat.lt_of_le_of_lt Nat.and_le_left bound
  let r : Fin 31 := ⟨min 30 (k.val+3*hCost h), by omega⟩
  have mid : (middleSet r.val).testBit t = true :=
    included_mem (horizontalCheck k h) (horiz_mem _ _ _ bound hit)
  obtain ⟨atMiddle, sum, finalBound⟩ := vert_mem t r.val v ht ok mid
  let funds := r.val+3*vCost v
  have check := verticalCheck r v
  have enough : 12 ≤ funds := by
    by_cases small : r.val + 3*vCost v < 12
    · simp only [small, ↓reduceIte] at check
      rw [check] at atMiddle
      simp at atMiddle
    · exact Nat.le_of_not_gt small
  have pos : ¬ r.val + 3*vCost v < 12 := by omega
  simp only [pos, ↓reduceIte] at check
  let k' : Fin 31 := ⟨min 30 (funds-10), by omega⟩
  have atEnd := included_mem check atMiddle
  rw [Nat.testBit_shiftRight, Nat.add_comm (vPairs v) t, ← sum] at atEnd
  refine ⟨finalBound, k', ?_, atEnd, ?_⟩
  · change 2 ≤ min 30 (funds-10)
    omega
  · change 10*(b.width + 1) + min 30 (funds-10) ≤ 3*(b.cost + (hCost h + vCost v))
    have hr : r.val ≤ k.val + 3*hCost h := Nat.min_le_right ..
    have hf : funds ≤ k.val + 3*hCost h + 3*vCost v := Nat.add_le_add_right hr _
    omega

private theorem invariantOfPositive (b : Board)
    (hn : 0 < b.width) (hs : b.safe) : Invariant b := by
  induction b with
  | left v => simp [Board.width] at hn
  | snoc prev h v ih =>
    obtain ⟨prevSafe, ok⟩ := hs
    cases prev with
    | left left => exact startInvariant left h v ok
    | snoc p h' v' =>
      exact nextInvariant _ h v (ih (Nat.zero_lt_succ _) prevSafe) ok

end Matchsticks.BitSets

namespace Matchsticks
open BitSets

/-- Every rectangle-free board of positive width meets the lower bound. -/
theorem lower (b : Board)
    (hn : 0 < b.width) (hs : b.safe) : target b.width ≤ b.cost := by
  by_cases hone : b.width = 1
  · cases b with
    | left v => simp [Board.width] at hn
    | snoc prev h v =>
      cases prev with
      | left left => exact (firstColumn left h v hs.2).1
      | snoc p h' v' => simp [Board.width] at hone
  · obtain ⟨_, k, lb, _, credit⟩ := invariantOfPositive b hn hs
    simp only [target, ite_eq_right hone]
    omega

end Matchsticks
