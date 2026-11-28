import TBoards

/-! Uniform three-coordinate marginals do not characterize ternary T boards.
The first six rows come from an extension splice cap; the remaining rows were
found by a prescribed-multiplicity search. Original attribution and license
terms are recorded in sources/LICENSE_SCOPE.txt. -/
namespace TBoards.MarginalCounterexample

abbrev Triple := Nat × Nat × Nat

def project (axis : Fin 4) (p : Pattern) : Triple :=
  match axis.val with
  | 0 => (p.2.1, p.2.2.1, p.2.2.2)
  | 1 => (p.1, p.2.2.1, p.2.2.2)
  | 2 => (p.1, p.2.1, p.2.2.2)
  | _ => (p.1, p.2.1, p.2.2.1)

def UniformTripleMarginals (b : Board) : Prop :=
  ∀ axis : Fin 4, ∀ a c d : Fin 3,
    ((patterns b).map (project axis)).count (a.val,c.val,d.val) = 3

instance (b : Board) : Decidable (UniformTripleMarginals b) := by
  unfold UniformTripleMarginals
  infer_instance

def witness : Board := [
  [1],
  [0,0,0],
  [0,1,0,0,1],
  [2,1,0,2,0,0,1],
  [0,1,0,0,0,0,2,2,1],
  [2,2,1,0,2,1,1,0,0,2,2],
  [0,0,1,2,0,1,1,1,0,1,1,2,1],
  [2,2,0,2,0,1,2,2,1,2,0,0,2,2,0],
  [2,1,1,2,1,1,1,1,0,1,2,1,2,2,2,2,2],
  [2,0,2,1,2,0,1,0,1,1,2,2,0,2,1,0,2,0,0]
]

theorem witness_wellFormed : WellFormed witness := by decide +kernel

theorem witness_uniform : UniformTripleMarginals witness := by decide +kernel

theorem witness_doubled : (patterns witness).count (1,1,1,1) = 2 := by decide +kernel

/-- Fifteen of the sixteen binary-cube count conditions also hold. -/
theorem witness_other_binary_counts : ∀ a l m r : Fin 2,
    (a.val,l.val,m.val,r.val) ≠ (1,1,1,1) →
      (patterns witness).count (a.val,l.val,m.val,r.val) = 1 := by decide +kernel

theorem witness_not_valid : ¬ Valid witness := by
  intro h
  have count := h.pattern_count 1 1 1 1 (by decide) (by decide) (by decide) (by decide)
  rw [witness_doubled] at count
  contradiction

/-- Even all four uniform triple marginals leave a genuine four-way obstruction. -/
theorem triple_marginals_insufficient :
    ∃ b : Board, WellFormed b ∧ UniformTripleMarginals b ∧ ¬ Valid b :=
  ⟨witness, witness_wellFormed, witness_uniform, witness_not_valid⟩

end TBoards.MarginalCounterexample

#print axioms TBoards.MarginalCounterexample.triple_marginals_insufficient
