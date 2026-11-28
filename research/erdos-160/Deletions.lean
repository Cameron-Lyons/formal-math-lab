import Lean

/-! Seven-colorings of `1,…,78` with a position or common difference omitted.
The kernel checks all coverage claims and the arithmetic progressions of each witness. -/

namespace Erdos160

/-- At least three of the four colors are distinct. -/
abbrev ThreeColors (a b c d : Fin 7) : Prop :=
  (a ≠ b ∧ a ≠ c ∧ b ≠ c) ∨ (a ≠ b ∧ a ≠ d ∧ b ≠ d) ∨
  (a ≠ c ∧ a ≠ d ∧ c ≠ d) ∨ (b ≠ c ∧ b ≠ d ∧ c ≠ d)

/-- A four-term progression is encoded by its one-based start and its positive step. -/
private abbrev AP := Nat × Nat
private abbrev Certificate := Nat × List AP

/-- Base-eight digit `i-1` is the color of position `i`. -/
private def color (word i : Nat) : Fin 7 :=
  Fin.ofNat 7 ((word >>> (3 * (i-1))) % 8)

private def progressions : List AP :=
  (List.range 25).flatMap fun k =>
    let d := k + 1
    (List.range (78 - 3*d)).map fun j => (j+1, d)

private def good (word : Nat) (p : AP) : Prop :=
  let (a,d) := p
  ThreeColors (color word a) (color word (a+d)) (color word (a+2*d)) (color word (a+3*d))

private instance (word : Nat) (p : AP) : Decidable (good word p) := by
  unfold good
  infer_instance

private def touches (i : Nat) (p : AP) : Bool :=
  let (a,d) := p
  i == a || i == a+d || i == a+2*d || i == a+3*d

-- Elaborate the external data to numerals and short lists. This code supplies
-- candidate certificates only; an incorrect list is rejected by the theorems below.
private meta def makeCertificate (digits : Array Nat) : Certificate := Id.run do
  let word := digits.toList.foldr (fun c n => 8*n+c) 0
  let mut bad := []
  for p in progressions do
    let (a,d) := p
    let values := (List.range 4).map fun j => digits[a-1+j*d]!
    if values.eraseDups.length < 3 then bad := p :: bad
  return (word, bad)

set_option maxHeartbeats 0 in
elab "puncturedColorings%" : term => do
  let mut data : List Certificate := []
  for row in (include_str "colorings.txt").splitOn "\n" do
    unless row.isEmpty do
      let chars := row.toList
      unless chars.length == 78 && chars.all (fun c => '0' ≤ c && c ≤ '6') do
        throwError "expected exactly 78 digits between 0 and 6"
      let digits := chars.toArray.map fun c => c.toNat - '0'.toNat
      data := makeCertificate digits :: makeCertificate digits.reverse :: data
  return Lean.toExpr data

private def certificates : List Certificate := puncturedColorings%

private def audits (w : Certificate) : Bool :=
  progressions.all fun p => w.2.contains p || decide (good w.1 p)

private def covers (x : Nat) (w : Certificate) : Bool :=
  w.2.all (touches x)

set_option maxRecDepth 16384
set_option maxHeartbeats 0

private theorem audit_cons {w : Certificate} {ws : List Certificate}
    (head : audits w = true) (tail : ws.all audits = true) : (w::ws).all audits = true := by
  simp [head, tail]

-- Check each word in its own kernel reduction to bound peak memory.
private theorem audited : certificates.all audits = true := by
  unfold certificates
  repeat' (apply audit_cons; case head => decide +kernel)
  rfl

private theorem coverage : (List.range 78).all (fun i =>
    certificates.any (covers (i+1))) = true := by decide +kernel

private theorem mem_progressions {a d : Nat} (ha : 0 < a) (hd : 0 < d)
    (h : a+3*d ≤ 78) : (a,d) ∈ progressions := by
  apply List.mem_flatMap.mpr
  refine ⟨d-1, List.mem_range.mpr (by omega), ?_⟩
  have hstep : d-1+1 = d := by omega
  dsimp
  rw [hstep]
  apply List.mem_map.mpr
  exact ⟨a-1, List.mem_range.mpr (by omega), by simp [show a-1+1 = a by omega]⟩

/-- Every deletion of one position of `{1,…,78}` allows a seven-coloring in
which every retained four-term arithmetic progression sees at least three colors. -/
theorem single_deletion_colorable {x : Nat} (hx : 0 < x ∧ x ≤ 78) :
    ∃ c : Nat → Fin 7, ∀ a d : Nat, 0 < a → 0 < d → a+3*d ≤ 78 →
      (∀ j : Nat, j < 4 → a+j*d ≠ x) →
      ThreeColors (c a) (c (a+d)) (c (a+2*d)) (c (a+3*d)) := by
  have cell := List.all_eq_true.mp coverage (x-1) (List.mem_range.mpr (by omega))
  have existsWord : certificates.any (covers x) = true := by
    simpa [show x-1+1=x by omega] using cell
  obtain ⟨w, hw, hcover⟩ := List.any_eq_true.mp existsWord
  refine ⟨color w.1, ?_⟩
  intro a d ha hd hbound retained
  have checked := List.all_eq_true.mp (List.all_eq_true.mp audited w hw)
    (a,d) (mem_progressions ha hd hbound)
  change (w.2.contains (a,d) || decide (good w.1 (a,d))) = true at checked
  simp only [Bool.or_eq_true] at checked
  rcases checked with bad | ok
  · have hit := List.all_eq_true.mp hcover (a,d) (List.contains_iff_mem.mp bad)
    have h0 := retained 0 (by decide)
    have h1 := retained 1 (by decide)
    have h2 := retained 2 (by decide)
    have h3 := retained 3 (by decide)
    simp [touches] at hit
    simp at h0 h1
    omega
  · exact of_decide_eq_true ok

/-- Every proper subset of `{1,…,78}` admits such a coloring. The predicate
`S` records membership in the subset; the coloring is defined on all naturals. -/
theorem proper_subset_colorable (S : Nat → Prop)
    (inside : ∀ i, S i → 0 < i ∧ i ≤ 78)
    (proper : ∃ x, 0 < x ∧ x ≤ 78 ∧ ¬ S x) :
    ∃ c : Nat → Fin 7, ∀ a d : Nat, 0 < d → (∀ j : Nat, j < 4 → S (a+j*d)) →
      ThreeColors (c a) (c (a+d)) (c (a+2*d)) (c (a+3*d)) := by
  obtain ⟨x, hxpos, hxle, absent⟩ := proper
  obtain ⟨c, h⟩ := single_deletion_colorable ⟨hxpos, hxle⟩
  refine ⟨c, ?_⟩
  intro a d hd retained
  have first : S a := by simpa using retained 0 (by decide)
  apply h a d (inside a first).1 hd (inside (a+3*d) (retained 3 (by decide))).2
  intro j hj eq
  exact absent (eq ▸ retained j hj)

private abbrev DifferenceWitness := Nat × Nat

elab "differenceWitnesses%" : term => do
  let mut data : List DifferenceWitness := []
  for row in (include_str "difference_colorings.txt").splitOn "\n" do
    unless row.isEmpty do
      let [step, digits] := row.splitOn " " | throwError "expected a step and a word"
      let some d := step.toNat? | throwError "expected a natural number"
      let chars := digits.toList
      unless chars.length == 78 && chars.all (fun c => '0' ≤ c && c ≤ '6') do
        throwError "expected 78 digits between 0 and 6"
      let word := chars.foldr (fun c n => 8*n + (c.toNat - '0'.toNat)) 0
      data := (d, word) :: data
  return Lean.toExpr data

private def differenceWitnesses : List DifferenceWitness := differenceWitnesses%

private def auditsDifference (w : DifferenceWitness) : Bool :=
  progressions.all fun p => p.2 == w.1 || decide (good w.2 p)

private theorem difference_cons {w : DifferenceWitness} {ws : List DifferenceWitness}
    (head : auditsDifference w = true) (tail : ws.all auditsDifference = true) :
    (w::ws).all auditsDifference = true := by simp [head, tail]

private theorem differences_audited : differenceWitnesses.all auditsDifference = true := by
  unfold differenceWitnesses
  repeat' (apply difference_cons; case head => decide +kernel)
  rfl

private theorem difference_coverage : (List.range 25).all (fun i =>
    i+1 == 24 || differenceWitnesses.any (fun w => w.1 == i+1)) = true := by decide +kernel

/-- Omitting any specified difference other than 24 from the 25 possible positive
differences suffices for a seven-coloring on all 78 positions. -/
theorem omit_difference_colorable {d : Nat} (hd : 0 < d ∧ d ≤ 25) (hne : d ≠ 24) :
    ∃ c : Nat → Fin 7, ∀ a e : Nat, 0 < a → 0 < e → a+3*e ≤ 78 → e ≠ d →
      ThreeColors (c a) (c (a+e)) (c (a+2*e)) (c (a+3*e)) := by
  have cell := List.all_eq_true.mp difference_coverage (d-1) (List.mem_range.mpr (by omega))
  have existsWord : differenceWitnesses.any (fun w => w.1 == d) = true := by
    simpa only [show d-1+1 = d by omega, Bool.or_eq_true, beq_iff_eq, hne, false_or]
      using cell
  obtain ⟨w, hw, heq⟩ := List.any_eq_true.mp existsWord
  have hstep : w.1 = d := beq_iff_eq.mp heq
  refine ⟨color w.2, ?_⟩
  intro a e ha he hbound hdiff
  have checked := List.all_eq_true.mp (List.all_eq_true.mp differences_audited w hw)
    (a,e) (mem_progressions ha he hbound)
  change (e == w.1 || decide (good w.2 (a,e))) = true at checked
  have ok : decide (good w.2 (a,e)) = true := by
    simpa only [hstep, Bool.or_eq_true, beq_iff_eq, hdiff, false_or] using checked
  exact of_decide_eq_true ok

end Erdos160
