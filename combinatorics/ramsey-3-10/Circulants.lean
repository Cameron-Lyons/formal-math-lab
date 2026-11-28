import Std

/-!
A circulant on 40 vertices is specified by the subset of the 20 undirected
cyclic distances which give edges. Each candidate triangle or independent set
covers the distance assignments on which all its pairs have the required color.
Lean verifies that their union covers the full 1,048,576-row truth table.
-/

namespace Ramsey310.Circulants

abbrev Vertex := Fin 40
abbrev Steps := BitVec 20

def cyclicDistance (u v : Vertex) : Nat :=
  let d := u.val - v.val + (v.val - u.val)
  min d (40 - d)

/-- Vertices are adjacent if they differ by a selected undirected distance.
    Bit zero selects distance one, and bit nineteen selects distance twenty. -/
def Adj (s : Steps) (u v : Vertex) : Prop :=
  u ≠ v ∧ s.getLsbD (cyclicDistance u v - 1) = true

abbrev HasTriangle (s : Steps) : Prop :=
  ∃ vs : List Vertex, vs.length = 3 ∧ vs.Nodup ∧ vs.Pairwise (Adj s)

abbrev HasIndependentTen (s : Steps) : Prop :=
  ∃ vs : List Vertex, vs.length = 10 ∧ vs.Nodup ∧ vs.Pairwise (fun x y => ¬ Adj s x y)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

/-- Number of rows in the truth table on the first n distance bits. -/
private def width : Nat → Nat
  | 0 => 1
  | n + 1 => width n + width n

private def assignmentRow (s : BitVec 20) : Nat → Nat
  | 0 => 0
  | n + 1 => (if s.getLsbD n then width n else 0) + assignmentRow s n

private theorem row_lt (s : BitVec 20) (n : Nat) : assignmentRow s n < width n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ n ih =>
    cases h : s.getLsbD n <;> simp only [width, assignmentRow, h, Bool.false_eq_true,
      ↓reduceIte, Nat.zero_add] <;> omega

/-- Adding one distance doubles the table. If the witness needs that distance,
only the half matching its color is retained. -/
private def satisfyingRows (mask : Nat) (color : Bool) : (n : Nat) → BitVec (width n)
  | 0 => 1#1
  | n + 1 =>
    let lower := satisfyingRows mask color n
    (if mask.testBit n && !color then 0 else lower) ++
      (if mask.testBit n && color then 0 else lower)

private theorem satisfyingRows_sound (mask : Nat) (color : Bool) (s : BitVec 20) (n : Nat)
    (h : (satisfyingRows mask color n).getLsbD (assignmentRow s n) = true) :
    ∀ d < n, mask.testBit d = true → s.getLsbD d = color := by
  induction n with
  | zero => omega
  | succ n ih =>
    have low := row_lt s n
    have high : ¬width n + assignmentRow s n < width n := by omega
    unfold satisfyingRows at h
    change @BitVec.getLsbD (width n + width n) (_ ++ _) _ = true at h
    rw [BitVec.getLsbD_append] at h
    cases hm : mask.testBit n <;> cases hc : color <;> cases hs : s.getLsbD n <;>
      simp [assignmentRow, hm, hc, hs, low, high] at h <;>
      intro d hd hit <;> by_cases he : d = n
    all_goals first
      | subst d; simp_all
      | exact (ih (by simpa [hc, low] using h) d (by omega) hit).trans hc

/-- Multiplying each seed by an invertible residue modulo 40 supplies
additional ten-vertex witnesses. -/
private def seeds : List (List Vertex) := [
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
  [0, 1, 2, 3, 4, 20, 21, 22, 23, 24],
  [0, 2, 4, 6, 8, 10, 12, 14, 16, 18],
  [0, 1, 2, 10, 11, 12, 20, 21, 22, 30],
  [0, 1, 2, 6, 16, 20, 21, 22, 26, 36],
  [0, 1, 4, 5, 8, 9, 13, 17, 21, 25],
  [0, 2, 5, 8, 11, 13, 16, 19, 22, 24],
  [0, 1, 4, 5, 10, 14, 19, 20, 23, 24],
  [0, 2, 4, 7, 12, 14, 19, 22, 24, 26],
  [0, 1, 5, 6, 10, 11, 15, 16, 27, 28],
  [0, 2, 5, 7, 10, 12, 15, 23, 26, 28],
  [0, 1, 4, 7, 11, 14, 17, 18, 28, 29],
  [0, 1, 2, 4, 5, 14, 18, 19, 23, 28],
  [0, 1, 7, 8, 14, 15, 22, 23, 31, 32],
  [0, 1, 2, 3, 8, 16, 21, 22, 23, 24],
  [0, 1, 4, 10, 11, 21, 22, 28, 31, 34],
  [0, 2, 4, 6, 8, 10, 14, 23, 27, 36],
  [0, 1, 5, 6, 10, 11, 15, 16, 20, 21],
  [0, 2, 5, 8, 10, 13, 16, 18, 21, 24],
  [0, 1, 2, 3, 9, 10, 11, 19, 20, 33],
  [0, 1, 4, 8, 11, 12, 20, 21, 24, 28]]

private def independentSets : List (List Vertex) :=
  seeds.flatMap fun vs => [1, 3, 7, 9, 11, 13, 17, 19].map fun (u : Nat) =>
    vs.map fun v => Fin.ofNat 40 (u * v.val)

private def pairMask : List Vertex → Nat
  | [] => 0
  | x :: xs =>
    xs.foldr (fun y m => m ||| (1 <<< (cyclicDistance x y - 1))) (pairMask xs)

private def triangleSets : List (List Vertex) :=
  (List.finRange 40).flatMap fun x => ((List.finRange 40).filter
    (fun y => decide (0 < x ∧ x < y))).map (fun y => [0, x, y])

private structure Pattern where
  distances : Nat
  vertices : List Vertex

private def patterns : List Pattern :=
  let triangles : List Pattern := triangleSets.map (fun vs => ⟨pairMask vs, vs⟩)
  triangles.eraseDupsBy (fun a b => a.distances == b.distances) ++
    independentSets.map (fun vs => ⟨pairMask vs, vs⟩)

private def triangle (p : Pattern) : Bool := p.vertices.length == 3

private def cover : List Pattern → BitVec (width 20)
  | [] => 0
  | p :: ps => satisfyingRows p.distances (triangle p) 20 ||| cover ps

private theorem coverHit (ps : List Pattern) (i : Nat) (h : (cover ps).getLsbD i = true) :
    ∃ p ∈ ps, (satisfyingRows p.distances (triangle p) 20).getLsbD i = true := by
  induction ps with
  | nil => simp [cover] at h
  | cons p ps ih =>
    simp only [cover, BitVec.getLsbD_or, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨p, by simp, h⟩
    · obtain ⟨q, hq, hit⟩ := ih h
      exact ⟨q, List.mem_cons_of_mem _ hq, hit⟩

private def validPattern (p : Pattern) : Prop :=
  (p.vertices.length = 3 ∨ p.vertices.length = 10) ∧ p.vertices.Nodup ∧
    p.vertices.Pairwise (fun x y => x ≠ y ∧ cyclicDistance x y - 1 < 20 ∧
      p.distances.testBit (cyclicDistance x y - 1) = true)

private instance (p : Pattern) : Decidable (validPattern p) := by
  unfold validPattern
  infer_instance

private theorem valid : patterns.all (fun p => decide (validPattern p)) = true := by decide +kernel

private theorem complete : cover patterns = BitVec.allOnes (width 20) := by decide +kernel

/-- Every 40-vertex circulant contains a triangle or ten independent vertices. -/
theorem order40 (s : Steps) : HasTriangle s ∨ HasIndependentTen s := by
  have bit : (cover patterns).getLsbD (assignmentRow s 20) = true := by
    rw [complete, BitVec.getLsbD_allOnes]
    simp [row_lt]
  obtain ⟨p, mem, hit⟩ := coverHit patterns _ bit
  have hw := satisfyingRows_sound p.distances (triangle p) s 20 hit
  obtain ⟨size, distinct, allPairs⟩ := of_decide_eq_true (List.all_eq_true.mp valid _ mem)
  rcases size with ht | hi
  · refine Or.inl ⟨p.vertices, ht, distinct, allPairs.imp ?_⟩
    intro x y h
    exact ⟨h.1, by simpa [triangle, ht] using hw _ h.2.1 h.2.2⟩
  · refine Or.inr ⟨p.vertices, hi, distinct, allPairs.imp ?_⟩
    intro x y h adj
    have hn : s.getLsbD (cyclicDistance x y - 1) = false := by
      simpa [triangle, hi] using hw _ h.2.1 h.2.2
    exact Bool.noConfusion (adj.2.symm.trans hn)

end Ramsey310.Circulants
