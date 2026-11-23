module

public import ArctanBridge
meta import Lean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! A fixed-point enclosure for the Gaussian product. Divide both coordinates by
`n!` before scaling. The rounded coordinates then fit into a small fixed number
of digits over the certified range. At each index the interval for `|B n / A n|`
fits strictly between two consecutive integers. -/

public section

namespace Arxiv.«2607.05739»

private def scale : ℤ := 12 * 10 ^ 36

private def Close (n : ℕ) (a b : ℤ) : Prop :=
    |scale * (coords n).1 - a * (n.factorial : ℤ)| ≤ (n : ℤ) ^ 2 * n.factorial ∧
    |scale * (coords n).2 - b * (n.factorial : ℤ)| ≤ (n : ℤ) ^ 2 * n.factorial

set_option maxHeartbeats 800000 in
private theorem round_step {x y u v e d k : ℤ} (hk : 0 < k) (hd : 0 ≤ d)
    (he : e + k * e + k ≤ k ^ 3)
    (hx : |x - u * d| ≤ e * d) (hy : |y - v * d| ≤ e * d) :
    |(x + k * y) - (u / k + v) * (k * d)| ≤ k ^ 2 * (k * d) := by
  have h1 := Int.emod_nonneg u hk.ne'
  have h2 := (Int.emod_lt_of_pos u hk).le
  have hid : (x + k * y) - (u / k + v) * (k * d) =
      (x - u * d) + k * (y - v * d) + (u % k) * d := by
    have h := Int.emod_add_ediv_mul u k
    linear_combination -d * h
  rw [hid]
  calc
    _ ≤ (|x - u * d| + |k * (y - v * d)|) + |u % k * d| :=
      (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ ≤ e * d + k * (e * d) + k * d := by
      rw [abs_mul, abs_of_nonneg hk.le, abs_mul, abs_of_nonneg hd, abs_of_nonneg h1]
      exact add_le_add (add_le_add hx (mul_le_mul_of_nonneg_left hy hk.le))
        (mul_le_mul_of_nonneg_right h2 hd)
    _ = (e + k * e + k) * d := by ring
    _ ≤ k ^ 3 * d := mul_le_mul_of_nonneg_right he hd
    _ = _ := by ring

private theorem Close.step {n : ℕ} {a b : ℤ} (h : Close n a b) :
    Close (n + 1) (a / (n + 1 : ℤ) - b) (a + b / (n + 1 : ℤ)) := by
  obtain ⟨ha, hb⟩ := h
  let k : ℤ := n + 1
  have hk : 0 < k := by dsimp [k]; omega
  have hd : 0 ≤ (n.factorial : ℤ) := by positivity
  have he : (n : ℤ) ^ 2 + k * (n : ℤ) ^ 2 + k ≤ k ^ 3 := by dsimp [k]; nlinarith
  have hbneg : |- (scale * (coords n).2) - (-b) * (n.factorial : ℤ)| ≤
      (n : ℤ) ^ 2 * n.factorial := by
    have hneg : - (scale * (coords n).2) - -b * (n.factorial : ℤ) =
        -(scale * (coords n).2 - b * (n.factorial : ℤ)) := by ring
    rwa [hneg, abs_neg]
  have hA := round_step hk hd he ha hbneg
  have hB := round_step hk hd he hb ha
  simp only [Close, coords, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  constructor
  · convert hA using 1
    dsimp only [k]
    ring_nf
  · convert hB using 1
    dsimp only [k]
    ring_nf

private def separated (e a b : ℤ) : Bool :=
  let u := (a.natAbs : ℤ)
  let v := (b.natAbs : ℤ)
  let q : ℤ := ((v - e) / (u + e)).toNat
  decide (q * (u + e) < v - e ∧ v + e < (q + 1) * (u - e))

private theorem abs_bounds {w c e d : ℤ} (hd : 0 ≤ d) (h : |w - c * d| ≤ e * d) :
    (|c| - e) * d ≤ |w| ∧ |w| ≤ (|c| + e) * d := by
  have hc := abs_sub_abs_le_abs_sub (c * d) w
  have hw := abs_sub_abs_le_abs_sub w (c * d)
  rw [abs_sub_comm (c * d) w] at hc
  rw [abs_mul c d, abs_of_nonneg hd] at hc hw
  constructor <;> linarith

private theorem separated_sound {n : ℕ} {a b : ℤ} (h : Close n a b)
    (hs : separated ((n : ℤ) ^ 2) a b = true) : ¬ IsIntegerValue n := by
  rw [isIntegerValue_iff_coords]
  rintro ⟨m, hm⟩
  let e := (n : ℤ) ^ 2
  let q : ℤ := ((|b| - e) / (|a| + e)).toNat
  have hq : 0 ≤ q := by dsimp [q]; positivity
  change decide _ = true at hs
  obtain ⟨hlo, hhi⟩ := of_decide_eq_true hs
  simp only [Int.natCast_natAbs] at hlo hhi
  change q * (|a| + e) < |b| - e at hlo
  change |b| + e < (q + 1) * (|a| - e) at hhi
  have hd : (0 : ℤ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have ⟨ha1, ha2⟩ := abs_bounds hd.le h.1
  have ⟨hb1, hb2⟩ := abs_bounds hd.le h.2
  have hm' : |scale * (coords n).2| = |scale * (coords n).1| * |m| := by
    rw [hm, ← mul_assoc, abs_mul (scale * (coords n).1)]
  rw [hm'] at hb1 hb2
  by_cases hmq : |m| ≤ q
  · have hup : |scale * (coords n).1| * |m| ≤ q * (|a| + e) * (n.factorial : ℤ) := by
      rw [mul_assoc, mul_comm q]
      exact mul_le_mul ha2 hmq (abs_nonneg _) (by positivity)
    linarith [mul_lt_mul_of_pos_right hlo hd]
  · have hlo' : (q + 1) * (|a| - e) * (n.factorial : ℤ) ≤ |scale * (coords n).1| * |m| := by
      rw [mul_assoc, mul_comm (q + 1)]
      exact mul_le_mul ha1 (by omega) (by omega) (abs_nonneg _)
    linarith [mul_lt_mul_of_pos_right hhi hd]

private abbrev Sample := ℕ × ℤ × ℤ

private def advance (s : Sample) : Sample :=
  let k := s.1 + 1
  (k, s.2.1 / (k : ℤ) - s.2.2, s.2.1 + s.2.2 / (k : ℤ))

private def closeAt (s : Sample) := Close s.1 s.2.1 s.2.2

private def Covers (u v : Sample) : Prop :=
  u.1 ≤ v.1 ∧ (closeAt u → closeAt v ∧ ∀ j, u.1 ≤ j → j < v.1 → ¬ IsIntegerValue j)

private theorem cover_refl (u : Sample) : Covers u u :=
  ⟨le_rfl, fun hu => ⟨hu, by omega⟩⟩

private theorem cover_trans (u v w : Sample) (huv : Covers u v) (hvw : Covers v w) : Covers u w := by
  refine ⟨huv.1.trans hvw.1, ?_⟩
  intro hu
  obtain ⟨hv, h₁⟩ := huv.2 hu
  obtain ⟨hw, h₂⟩ := hvw.2 hv
  refine ⟨hw, fun j hju hjw => ?_⟩
  by_cases hjv : j < v.1
  · exact h₁ j hju hjv
  · exact h₂ j (by omega) hjw

private def checkRounded : ℕ → Sample → Sample → Bool
  | 0, s, t => s == t
  | count + 1, s, t =>
    separated ((s.1 : ℤ) ^ 2) s.2.1 s.2.2 && checkRounded count (advance s) t

private theorem checkRounded_sound (count : ℕ) (u v : Sample)
    (h : checkRounded count u v = true) : Covers u v := by
  induction count generalizing u with
  | zero =>
    obtain rfl : u = v := by simpa [checkRounded] using h
    exact cover_refl _
  | succ count ih =>
    simp only [checkRounded, Bool.and_eq_true] at h
    obtain ⟨hs, hrest⟩ := h
    apply cover_trans _ (advance u) _ _ (ih _ hrest)
    refine ⟨Nat.le_succ _, fun hu => ⟨?_, ?_⟩⟩
    · simpa only [closeAt, advance, Nat.cast_add, Nat.cast_one] using Close.step hu
    · intro j hlo hhi
      have hji : j = u.1 := by change j < u.1 + 1 at hhi; omega
      exact hji ▸ separated_sound hu hs

private def seed : Sample := (5, 19 * 10 ^ 36, -9 * 10 ^ 36)

private theorem seed_close : closeAt seed := by
  unfold closeAt Close seed
  decide +kernel

open Lean Meta Elab Term in
/-- Generate rounded endpoints as hints. The kernel checks every transition and
every separation inequality independently in bounded-size blocks. -/
local elab "roundedPrefix%" number:num : term => do
  let total := number.getNat
  let blockSize := 200
  let mut atIndex : Nat := 5
  let mut a : Int := 19 * 10 ^ 36
  let mut b : Int := -9 * 10 ^ 36
  let seedExpr := toExpr (atIndex, a, b)
  let mut startExpr := seedExpr
  let mut proof := mkApp (mkConst ``cover_refl) seedExpr
  while atIndex < total + 1 do
    let count := min blockSize (total + 1 - atIndex)
    for _ in [:count] do
      atIndex := atIndex + 1
      let nextA := a / (atIndex : Int) - b
      b := a + b / (atIndex : Int)
      a := nextA
    let endExpr := toExpr (atIndex, a, b)
    let check := mkApp3 (mkConst ``checkRounded) (toExpr count) startExpr endExpr
    let property ← mkEq check (mkConst ``Bool.true)
    let certName ← withOptions (Elab.async.set · false) do
      mkAuxLemma [] property (← mkDecideProof property)
    let part := mkApp4 (mkConst ``checkRounded_sound) (toExpr count) startExpr endExpr (mkConst certName)
    let joined := mkApp5 (mkConst ``cover_trans) seedExpr startExpr endExpr proof part
    -- Keep the proof term at each checkpoint small.
    let joinedName ← mkAuxLemma [] (mkApp2 (mkConst ``Covers) seedExpr endExpr) joined
    proof := mkConst joinedName
    startExpr := endExpr
  return proof

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
/-- The arctangent sum has no integer value at the first 999,996 conjectured indices. -/
theorem not_isIntegerValue_five_to_one_million {n : ℕ} (hlo : 5 ≤ n) (hhi : n ≤ 1000000) :
    ¬ IsIntegerValue n := by
  have h := roundedPrefix% 1000000
  exact (h.2 seed_close).2 n hlo (by omega)

end Arxiv.«2607.05739»
