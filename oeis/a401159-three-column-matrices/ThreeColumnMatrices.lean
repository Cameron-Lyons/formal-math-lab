module

public import ThreeColumnMatrices.ColumnSupports
public import Mathlib.Data.Fintype.Pi
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Lattice

/-! # Binary matrices with three columns (OEIS A401159)

Each column chooses up to two of the `n` rows for its ones, giving
`H = 1 + n + n.choose 2` choices. This gives `H ^ 3` matrices before checking rows.
A specified all-ones row leaves `n` choices per column (no extra one, or one in
any other row). Two specified all-ones rows determine the whole matrix, and
three are impossible. Inclusion–exclusion gives `H ^ 3 - n ^ 4 + n.choose 2`.
-/

@[expose] public section

namespace ThreeColumnMatrices
open Finset

abbrev BinaryMatrix (n : ℕ) := Fin n → Fin 3 → Bool

/-- The column indices of the ones in a row. -/
def rowSupport {n : ℕ} (M : BinaryMatrix n) (i : Fin n) : Finset (Fin 3) :=
  univ.filter fun j => M i j = true

/-- The row indices of the ones in a column. -/
def columnSupport {n : ℕ} (M : BinaryMatrix n) (j : Fin 3) : Finset (Fin n) :=
  univ.filter fun i => M i j = true

abbrev ColumnsBounded {n : ℕ} (M : BinaryMatrix n) :=
  ∀ j, (columnSupport M j).card ≤ 2

/-- The finite set whose cardinality is the requested count. -/
def validMatrices (n : ℕ) : Finset (BinaryMatrix n) :=
  univ.filter fun M => (∀ i, (rowSupport M i).card ≤ 2) ∧ ColumnsBounded M

private def fullRow {n : ℕ} (i : Fin n) : Finset (BinaryMatrix n) :=
  univ.filter fun M => rowSupport M i = univ

private theorem avoiding_fullRows (n : ℕ) :
    ((univ.inf fun i : Fin n => (fullRow i)ᶜ).filter ColumnsBounded) = validMatrices n := by
  ext M
  simp [mem_inf, fullRow, validMatrices, ← card_lt_iff_ne_univ, Nat.lt_succ_iff]

/-- A matrix is determined by the rows occupied by ones in each column. -/
private def columnSupportEquiv (n : ℕ) : BinaryMatrix n ≃ (Fin 3 → Finset (Fin n)) where
  toFun := columnSupport
  invFun S i j := decide (i ∈ S j)
  left_inv M := by funext i j; simp [columnSupport]
  right_inv S := by funext j; ext i; simp [columnSupport]

/-- If every row in `t` must be full, each column chooses a support containing `t`. -/
private theorem card_prescribedRows {n : ℕ} (t : Finset (Fin n)) :
    ((t.inf fullRow).filter ColumnsBounded).card = (columnSupports t).card ^ 3 := by
  rw [← Fintype.card_piFinset_const (columnSupports t) 3]
  apply card_equiv (columnSupportEquiv n)
  intro M
  simp [mem_inf, fullRow, eq_univ_iff_forall, columnSupportEquiv, ColumnsBounded,
    rowSupport, columnSupport, subset_iff]
  aesop

/-- Inclusion–exclusion over full rows. The three surviving terms count zero,
one, or two prescribed full rows, respectively. -/
theorem card_validMatrices (n : ℕ) :
    ((validMatrices n).card : ℤ) =
      ((1 + n + n.choose 2 : ℕ) : ℤ) ^ 3 - (n : ℤ) ^ 4 + n.choose 2 := by
  let H : ℤ := (1 + n + n.choose 2 : ℕ)
  calc
    _ = ∑ t : Finset (Fin n), (-1 : ℤ) ^ t.card * ((columnSupports t).card : ℤ) ^ 3 := by
      simpa only [sum_boole, avoiding_fullRows, powerset_univ, Int.zsmul_eq_mul,
        card_prescribedRows, Nat.cast_pow] using
        inclusion_exclusion_sum_inf_compl (univ : Finset (Fin n)) fullRow
          (fun M => if ColumnsBounded M then (1 : ℤ) else 0)
    _ = ∑ t : Finset (Fin n),
        ((if t.card = 0 then H ^ 3 else 0) - (if t.card = 1 then (n : ℤ) ^ 3 else 0) +
         (if t.card = 2 then 1 else 0)) := by
      apply sum_congr rfl
      intro t _
      rw [card_columnSupports]
      match t.card with
      | 0 | 1 | 2 | _ + 3 => simp [H, pow_succ]
    _ = _ := by simp [sum_add_distrib, sum_sub_distrib, ← sum_filter, H, pow_succ']

private theorem card_balance (n : ℕ) :
    (validMatrices n).card + n ^ 4 = (1 + n + n.choose 2) ^ 3 + n.choose 2 := by
  have h := card_validMatrices n
  rw [sub_add_eq_add_sub, eq_sub_iff_add_eq] at h
  exact_mod_cast h

/-- Evaluate the count by arithmetic alone. Add the pair term before subtracting
so the whole calculation can use natural numbers. -/
def count (n : ℕ) : ℕ :=
  let pairs := n * (n - 1) / 2
  (1 + n + pairs) ^ 3 + pairs - n ^ 4

theorem count_correct (n : ℕ) : count n = (validMatrices n).card := by
  simp [count, ← Nat.choose_two_right, ← card_balance]

/-- Mathar's polynomial for the three-column count in OEIS A401159, with the
denominator cleared so the equality also proves exact divisibility by eight. -/
theorem mathar_polynomial (n : ℕ) : 8 * (validMatrices n).card =
    n ^ 6 + 3 * n ^ 5 + n ^ 4 + 13 * n ^ 3 + 22 * n ^ 2 + 8 * n + 8 := by
  have pairs := Nat.add_one_mul_choose_eq n 1
  rw [Nat.choose_succ_succ n 1, Nat.choose_one_right] at pairs
  have balance := card_balance n
  grobner

end ThreeColumnMatrices
