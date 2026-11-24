import E670.Basic

/-!
# Small models

Models of the law with 4, 5, 9 and 11 elements, and linear models `x ◇ y = a x + b y` modulo 19,
29, 31, 41, 59 and 61.  They are not used in the proof; they show that the law as stated here is
the intended one.
-/

namespace E670

/-- The operation on `Fin n` given by a table. -/
def ofTable {n : Nat} [NeZero n] (t : List (List Nat)) : Fin n → Fin n → Fin n :=
  fun x y => Fin.ofNat n ((t.getD x.val []).getD y.val 0)

def table4 : Fin 4 → Fin 4 → Fin 4 :=
  ofTable [[2, 0, 3, 1], [1, 3, 0, 2], [3, 0, 1, 2], [1, 2, 3, 0]]

theorem law4 : Law table4 := by unfold Law; decide

/-- The operation `x ◇ y = a x + b y` on the integers modulo `n`. -/
def linear (n : Nat) [NeZero n] (a b : Fin n) : Fin n → Fin n → Fin n := fun x y => a * x + b * y

theorem law5 : Law (linear 5 2 1) := by unfold Law linear; decide

def table9 : Fin 9 → Fin 9 → Fin 9 :=
  ofTable [[0, 3, 4, 6, 8, 1, 5, 2, 7], [2, 1, 6, 5, 0, 7, 4, 8, 3], [3, 5, 2, 8, 7, 4, 0, 1, 6],
    [4, 2, 7, 3, 5, 8, 1, 6, 0], [6, 8, 3, 1, 4, 0, 7, 5, 2], [7, 6, 0, 2, 1, 5, 8, 3, 4],
    [8, 7, 5, 4, 2, 3, 6, 0, 1], [1, 4, 8, 0, 3, 6, 2, 7, 5], [5, 0, 1, 7, 6, 2, 3, 4, 8]]

theorem law9 : Law table9 := by unfold Law; decide

theorem law11 : Law (linear 11 1 3) := by unfold Law linear; decide

theorem law19 : Law (linear 19 9 11) := by unfold Law linear; decide +kernel
theorem law29 : Law (linear 29 3 27) := by unfold Law linear; decide +kernel
theorem law31 : Law (linear 31 6 2) := by unfold Law linear; decide +kernel
theorem law41 : Law (linear 41 12 37) := by unfold Law linear; decide +kernel
theorem law59 : Law (linear 59 20 40) := by unfold Law linear; decide +kernel
theorem law61 : Law (linear 61 6 58) := by unfold Law linear; decide +kernel

end E670
