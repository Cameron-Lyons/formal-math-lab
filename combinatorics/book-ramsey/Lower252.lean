import Lean
import BookRamsey

namespace BookRamsey.Lower252

/-! The symmetric conference construction of Dai and Lin for q = 125.
Nonzero squares in F₅[t]/(t³+t+1) are stored in a 125-bit mask. The index
of a + bt + ct² is a + 5b + 25c with digits in {0,1,2,3,4}. -/
def squareMask : Nat := 0xb8efd186036b682616bd71d47d221f2

def fieldSub (x y : Nat) : Nat :=
  let subDigit (a b : Nat) := (a % 5 + 5 - b % 5) % 5
  subDigit x y + 5 * subDigit (x / 5) (y / 5) + 25 * subDigit (x / 25) (y / 25)

/-- There are two copies of each point of F₁₂₅ ∪ {∞}. We encode
(x, s) as 2*x+s and encode ∞ as 125. -/
def graph : Graph 252 := Graph.ofUpper fun u v =>
  let x := u.val / 2
  let y := v.val / 2
  let positive := x == 125 || y == 125 || squareMask.testBit (fieldSub x y)
  x != y && ((u.val % 2 == v.val % 2) == positive)

/-- Store each adjacency bit in its own byte. Since 256 ≡ 1 modulo 255,
reducing the packed row modulo 255 sums the bytes. -/
private def bytes (p : α → Bool) : (xs : List α) → BitVec (8 * xs.length)
  | [] => 0
  | x :: xs => bytes p xs ++ (if p x then 1 else 0 : BitVec 8)

private theorem count_bytes (p q : α → Bool) (xs : List α) :
    ((bytes p xs &&& bytes q xs).toNat % 255) =
      xs.countP (fun x => p x && q x) % 255 := by
  induction xs with
  | nil => simp [bytes]
  | cons x xs ih =>
    change (((bytes p xs ++ (if p x then 1 else 0 : BitVec 8)) &&&
             (bytes q xs ++ (if q x then 1 else 0 : BitVec 8))).toNat % 255) = _
    rw [BitVec.and_append, BitVec.toNat_append_eq_mul_add, List.countP_cons]
    cases hp : p x <;> cases hq : q x <;>
      simp +decide [Nat.add_mod, Nat.mul_mod, -BitVec.toNat_and, ih]

private def row (g : Graph 252) (u : Fin 252) := (bytes (g.adj u) (List.finRange 252)).toNat

private theorem common_bytes (g : Graph 252) (u v : Fin 252) :
    g.commonCount u v = (row g u &&& row g v) % 255 := by
  rw [row, row, ← BitVec.toNat_and, count_bytes]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (List.countP_le_length ..) (by simp))).symm

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option Elab.async false

-- Compute each neighborhood once. The kernel checks each row against the graph.
private def table : List Nat := by
  run_tac
    Lean.Elab.Tactic.closeMainGoal `table (Lean.toExpr ((List.finRange 252).map (row graph)))

private theorem table_eq : table = (List.finRange 252).map (row graph) := by
  iterate 252
    refine (List.cons.injEq ..).mpr ⟨?_, ?_⟩
    · as_aux_lemma => decide +kernel
  rfl

private theorem separated : table.Pairwise (fun a b => (a &&& b) % 255 < 63) := by decide +kernel
private theorem row_sizes : ∀ r ∈ table, r % 255 = 125 := by decide +kernel

private theorem regular (u : Fin 252) : graph.degree u = 125 := by
  have size := row_sizes (row graph u) (by simp [table_eq, List.mem_finRange])
  simpa [Graph.degree, Graph.commonCount] using
    (common_bytes graph u u).trans (by simpa using size)

private theorem pair_bound (u v : Fin 252) (hne : u ≠ v) : graph.commonCount u v < 63 := by
  have lt (i j : Fin 252) (h : i.val < j.val) : (row graph i &&& row graph j) % 255 < 63 := by
    have pairs := separated
    rw [table_eq] at pairs
    simpa using pairs.rel_getElem_of_lt (i := i.val) (j := j.val) (by simp) (by simp) h
  rw [common_bytes]
  obtain h | h := Fin.lt_or_lt_of_ne hne
  · exact lt u v h
  · simpa [Nat.and_comm] using lt v u h

/-- Every vertex has 125 red neighbors. On a blue edge the two endpoint
neighborhoods therefore have the same intersection size in both colors. -/
theorem avoids_63_both : ¬graph.HasBook 63 ∧ ¬graph.complement.HasBook 63 := by
  constructor <;> rw [Graph.not_hasBook_iff] <;> intro u v edge
  · apply pair_bound
    rintro rfl
    simp [graph.loopless] at edge
  · obtain ⟨huv, he⟩ : u ≠ v ∧ graph.adj u v = false := by simpa [Graph.complement] using edge
    have counts := graph.nonedge_commonCount u v huv he
    rw [regular, regular] at counts
    have := pair_bound u v huv
    omega

theorem exists_252 : ∃ g : Graph 252, ¬g.HasBook 63 ∧ ¬g.complement.HasBook 64 :=
  ⟨graph, avoids_63_both.1, fun h => avoids_63_both.2 (h.mono (by decide))⟩

end BookRamsey.Lower252
