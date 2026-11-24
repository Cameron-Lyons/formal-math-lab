import Std
import Init.Data.Nat.Sqrt.Lemmas

namespace SquareTriples

/-- One of the nine required square conditions. -/
def Edge (a b : Nat) : Prop := ∃ r : Nat, r*r = a*b + 1

/-- All six labels must be positive and distinct. The square condition only crosses sides. -/
def Solution (a b c x y z : Nat) : Prop :=
  ([a,b,c,x,y,z].all (0 < ·)) ∧ [a,b,c,x,y,z].Nodup ∧
  (∀ i ∈ [a,b,c], ∀ j ∈ [x,y,z], Edge i j)

/-- Compute a decision for all nine square conditions, with no bound on the labels. -/
def check (a b c x y z : Nat) : Bool :=
  let labels := [a,b,c,x,y,z]
  labels.all (0 < ·) && decide labels.Nodup &&
    [a,b,c].all fun i => [x,y,z].all fun j =>
      let n := i*j+1
      n.sqrt*n.sqrt == n

private theorem sqrt_test (n : Nat) : n.sqrt*n.sqrt = n ↔ ∃ r, r*r = n := by
  constructor
  · exact fun h => ⟨_, h⟩
  · rintro ⟨r, hr⟩
    have h₁ : n.sqrt ≤ r := Nat.mul_self_le_mul_self_iff.mp (hr ▸ Nat.sqrt_le n)
    have hs := Nat.lt_succ_sqrt n
    have h₂ : r < n.sqrt.succ := Nat.mul_self_lt_mul_self_iff.mp (hr.symm ▸ hs)
    have heq : n.sqrt = r := by omega
    simpa [heq] using hr

instance (a b : Nat) : Decidable (Edge a b) :=
  decidable_of_iff _ (sqrt_test (a*b+1))

theorem Edge.symm {a b : Nat} (h : Edge a b) : Edge b a := by
  simpa only [Edge, Nat.mul_comm] using h

theorem check_iff (a b c x y z : Nat) : check a b c x y z = true ↔ Solution a b c x y z := by
  simp only [check, Solution, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq, sqrt_test, Edge, and_assoc]

end SquareTriples
