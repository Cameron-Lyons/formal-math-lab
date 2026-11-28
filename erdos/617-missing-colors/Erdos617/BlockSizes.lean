module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Erdos617

private lemma succ_choose_two (v : ℕ) : (v+1).choose 2 = v.choose 2 + v := by
  rw [Nat.choose_succ_succ]
  simp [Nat.add_comm]

private lemma twice_choose_two (v : ℕ) : 2 * v.choose 2 + v = v*v := by
  induction v with
  | zero => decide
  | succ v ih =>
    rw [succ_choose_two]
    nlinarith only [ih]

/-- Excess above the affine lower bound for the number of pairs in a block. -/
def blockGap (t v : ℕ) := v.choose 2 + (t+1).choose 2 - t*v

lemma blockGap_spec (t v : ℕ) :
    t*v + blockGap t v = v.choose 2 + (t+1).choose 2 ∧ t ≤ v + blockGap t v := by
  have h : t*v ≤ v.choose 2 + (t+1).choose 2 ∧
      t*v+t ≤ v.choose 2 + (t+1).choose 2 + v := by
    rw [succ_choose_two]
    rcases lt_trichotomy v t with h | rfl | h
    · obtain ⟨k, rfl⟩ : ∃ k, t = v+k+1 := ⟨t-v-1, by omega⟩
      constructor <;> nlinarith only [twice_choose_two v, twice_choose_two (v+k+1),
        Nat.zero_le (k*k), Nat.zero_le k]
    · constructor <;> nlinarith only [twice_choose_two v]
    · obtain ⟨k, rfl⟩ : ∃ k, v = t+k+1 := ⟨v-t-1, by omega⟩
      constructor <;> nlinarith only [twice_choose_two t, twice_choose_two (t+k+1),
        Nat.zero_le (k*k), Nat.zero_le k]
  unfold blockGap
  omega

private lemma blockGap_sum (b : List ℕ) (t : ℕ) :
    t*b.sum + (b.map (blockGap t)).sum =
      (b.map (fun v => v.choose 2)).sum + b.length * (t+1).choose 2 := by
  induction b with
  | nil => simp
  | cons v b ih =>
    simp only [List.sum_cons, List.map_cons, List.length_cons, Nat.mul_add, Nat.add_mul, Nat.one_mul]
    have := (blockGap_spec t v).1
    omega

private lemma block_choose_sum_eq (b : List ℕ) {a t d : ℕ} (hd : a = b.length + d)
    (hsum : b.sum = t*a+1) :
    (b.map (fun v => v.choose 2)).sum =
      a*t.choose 2 + t + d*(t+1).choose 2 + (b.map (blockGap t)).sum := by
  have hc := blockGap_sum b t
  rw [hsum] at hc
  have hcenter : a*(t+1).choose 2 + a*t.choose 2 = t*(t*a) := by
    rw [succ_choose_two]
    nlinarith only [congrArg (a * ·) (twice_choose_two t)]
  have hparts := congrArg (· * (t+1).choose 2) hd
  nlinarith only [hc, hcenter, hparts]

/-- The total block gaps, edge costs, and the shortfall in the number of
blocks all fit into the excess edge budget. -/
theorem total_block_gap_bound (b : List ℕ) (a t C : ℕ) (ht : 2 ≤ t)
    (hlen : b.length ≤ a) (hsum : b.sum = t*a+1)
    (hbudget : (b.map (fun v => v.choose 2)).sum + C ≤ a*t.choose 2+t^2) :
    a + (b.map (blockGap t)).sum + C ≤ b.length+t^2 := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hlen
  have hid := block_choose_sum_eq b hd hsum
  have hq : 1 ≤ (t+1).choose 2 := by rw [succ_choose_two]; omega
  have hb := Nat.mul_le_mul_left d hq
  rw [Nat.mul_one] at hb
  omega

/-- At order `t*a+1`, a partition using at most `a` blocks and a small
quadratic edge budget uses all `a` blocks. Every block is larger than
`C+1`, and at least one block is larger than `t`. -/
theorem block_sizes_of_small_budget (b : List ℕ) (a t C : ℕ) (_ht : 2 ≤ t)
    (hlen : b.length ≤ a) (hsum : b.sum = t*a+1)
    (hbudget : (b.map (fun v => v.choose 2)).sum + C < a*t.choose 2 + 2*t - 1) :
    b.length = a ∧ (∃ v ∈ b, t < v) ∧ ∀ v ∈ b, C+1 < v := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hlen
  have hid := block_choose_sum_eq b hd hsum
  have hfull : d = 0 := by
    by_contra hn
    have hb : t ≤ (t+1).choose 2 := by rw [succ_choose_two]; omega
    have hbig := Nat.mul_le_mul_right ((t+1).choose 2) (show 1 ≤ d by omega)
    rw [Nat.one_mul] at hbig
    omega
  have hlen' : b.length = a := by omega
  refine ⟨hlen', ?_, ?_⟩
  · by_contra! h
    have lim (l : List ℕ) (hl : ∀ v ∈ l, v ≤ t) : l.sum ≤ t*l.length := by
      induction l with
      | nil => simp
      | cons v l ih =>
        have hv := hl v (by simp)
        have htail := ih (fun u hu => hl u (by simp [hu]))
        simp only [List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
        omega
    have := lim b h
    rw [hlen', hsum] at this
    omega
  · intro v hv
    have hmem : blockGap t v ∈ b.map (blockGap t) := List.mem_map_of_mem hv
    have hs := List.le_sum_of_mem hmem
    have hv' := (blockGap_spec t v).2
    omega

end Erdos617
