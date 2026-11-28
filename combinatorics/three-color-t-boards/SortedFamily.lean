import TBoards

namespace TBoards

/-- A convenient numeric fingerprint. Injectivity is not assumed: distinct
fingerprints alone suffice to prove distinct boards. -/
def boardCode (b : Board) : Nat :=
  b.flatten.foldl (fun n c => 3*n+c) 0

/-- Linear-time check that adjacent numeric fingerprints strictly increase. -/
def increasing : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: tail => decide (a < b) && increasing (b :: tail)

theorem increasing_tail {a : Nat} {xs : List Nat}
    (h : increasing (a :: xs) = true) : increasing xs = true := by
  cases xs with
  | nil => rfl
  | cons b tail => exact (Bool.and_eq_true_iff.mp h).2

theorem increasing_head {a : Nat} {xs : List Nat}
    (h : increasing (a :: xs) = true) : ∀ b ∈ xs, a < b := by
  induction xs generalizing a with
  | nil => simp
  | cons c tail ih =>
    have hp := Bool.and_eq_true_iff.mp h
    have hac : a < c := of_decide_eq_true hp.1
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hac
    · exact Nat.lt_trans hac (ih hp.2 b hb)

theorem increasing_nodup {xs : List Nat}
    (h : increasing xs = true) : xs.Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons a tail ih =>
    apply List.nodup_cons.mpr
    constructor
    · intro ha
      exact Nat.lt_irrefl a (increasing_head h a ha)
    · exact ih (increasing_tail h)

theorem nodup_of_increasing_codes {bs : List Board}
    (h : increasing (bs.map boardCode) = true) : bs.Nodup := by
  have hn := increasing_nodup h
  exact List.Pairwise.of_map boardCode
    (fun a b hne heq => hne (congrArg boardCode heq)) hn

end TBoards
