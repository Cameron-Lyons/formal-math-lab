import Lean

namespace Erdos160

/-- The total weight of rows selected by a Boolean predicate. Duplicate rows count separately. -/
def selectedWeight (weight : α → Nat) (select : α → Bool) : List α → Nat
  | [] => 0
  | x :: xs => (if select x then weight x else 0) + selectedWeight weight select xs

private theorem weight_or_le (w : α → Nat) (p q : α → Bool) (xs : List α) :
    selectedWeight w (fun x => p x || q x) xs ≤ selectedWeight w p xs + selectedWeight w q xs := by
  induction xs with
  | nil => simp [selectedWeight]
  | cons x xs ih =>
    cases hp : p x <;> cases hq : q x <;> simp [selectedWeight, hp, hq] at * <;> omega

private theorem weight_false (w : α → Nat) (xs : List α) :
    selectedWeight w (fun _ => false) xs = 0 := by
  induction xs <;> simp_all [selectedWeight]

private theorem exists_missed (w : α → Nat) (p : α → Bool) (xs : List α)
    (gap : selectedWeight w p xs < selectedWeight w (fun _ => true) xs) :
    ∃ x ∈ xs, p x = false := by
  induction xs with
  | nil => simp [selectedWeight] at gap
  | cons x xs ih =>
    cases h : p x with
    | false => exact ⟨x, by simp, h⟩
    | true =>
      have smaller : selectedWeight w p xs < selectedWeight w (fun _ => true) xs := by
        simpa [selectedWeight, h] using gap
      obtain ⟨y, hy, close⟩ := ih smaller
      exact ⟨y, List.mem_cons_of_mem _ hy, close⟩

private theorem failure_weight_le (w : α → Nat) (bad : α → β → Bool)
    (rows : List α) (cs : List β) (M : Nat)
    (bound : ∀ c ∈ cs, selectedWeight w (fun x => bad x c) rows ≤ M) :
    selectedWeight w (fun x => cs.any (bad x)) rows ≤ cs.length * M := by
  induction cs with
  | nil => simpa using (Nat.le_of_eq (weight_false w rows))
  | cons c cs ih =>
    have head := bound c (by simp)
    have tail := ih (fun d hd => bound d (List.mem_cons_of_mem _ hd))
    have h := weight_or_le w (fun x => bad x c) (fun x => cs.any (bad x)) rows
    simp only [List.any_cons, List.length_cons, Nat.succ_mul]
    omega

/-- If each constraint rejects weight at most M, fewer than the total weight can be
rejected by the entire list whenever its length times M is below that total. -/
theorem weighted_union_bound (w : α → Nat) (bad : α → β → Bool)
    (rows : List α) (cs : List β) (M : Nat)
    (bound : ∀ c ∈ cs, selectedWeight w (fun x => bad x c) rows ≤ M)
    (budget : cs.length * M < selectedWeight w (fun _ => true) rows) :
    ∃ x ∈ rows, ∀ c ∈ cs, bad x c = false := by
  have gap := Nat.lt_of_le_of_lt (failure_weight_le w bad rows cs M bound) budget
  obtain ⟨x, hx, none⟩ := exists_missed w (fun x => cs.any (bad x)) rows gap
  refine ⟨x, hx, ?_⟩
  intro c hc
  cases e : bad x c with
  | false => rfl
  | true => exact Bool.noConfusion (none.symm.trans (List.any_eq_true.mpr ⟨c,hc,e⟩))

end Erdos160

namespace Erdos160.ProgressionFamily

private abbrev AP := Nat × Nat
private abbrev Row := Nat × Nat

/-- The four colors include a triple of pairwise distinct colors. -/
abbrev Three (a b c d : Fin 7) : Prop :=
  (a ≠ b ∧ a ≠ c ∧ b ≠ c) ∨ (a ≠ b ∧ a ≠ d ∧ b ≠ d) ∨
  (a ≠ c ∧ a ≠ d ∧ c ≠ d) ∨ (b ≠ c ∧ b ≠ d ∧ c ≠ d)

private def color (word i : Nat) : Fin 7 :=
  Fin.ofNat 7 ((word >>> (3*(i-1))) % 8)

private def fails (row : Row) (p : AP) : Bool :=
  let c := color row.2
  let (a,d) := p
  !decide (Three (c a) (c (a+d)) (c (a+2*d)) (c (a+3*d)))

private def progressions : List AP :=
  (List.range 25).flatMap fun k =>
    let d := k+1
    (List.range (78-3*d)).map fun j => (j+1,d)

-- This elaborator supplies concrete rows. The theorem below uses them only
-- after its audit verifies their total weight and every failure-weight bound.
set_option maxHeartbeats 0 in
elab "weightedColorings%" : term => do
  let mut result : List Row := []
  for line in (include_str "progression_families.txt").splitOn "\n" do
    unless line.isEmpty do
      let [rawWeight, word] := line.splitOn " " | throwError "expected a weight and word"
      let some weight := rawWeight.toNat? | throwError "invalid weight"
      let chars := word.toList
      unless weight > 0 && chars.length == 78 && chars.all (fun c => '0' ≤ c && c ≤ '6') do
        throwError "expected a positive weight and 78 seven-color digits"
      let digits := chars.map (fun c => c.toNat-'0'.toNat)
      let pack := fun (ds : List Nat) => ds.foldr (fun c n => 8*n+c) 0
      result := (weight, pack digits) :: (weight, pack digits.reverse) :: result
  return Lean.toExpr result

set_option maxRecDepth 16384

private def rows : List Row := weightedColorings%
private def total := selectedWeight Prod.fst (fun _ => true) rows

/-- The number of chosen progressions covered by the certificate. -/
abbrev cutoff : Nat := 330

private def allowance := (total-1)/cutoff

private theorem audited :
    (progressions.all fun p => decide (selectedWeight Prod.fst (fun r => fails r p) rows ≤ allowance)) = true ∧
    cutoff * allowance < total := by native_decide

private theorem valid_mem {a d : Nat} (ha : 0<a) (hd : 0<d) (h : a+3*d≤78) :
    (a,d) ∈ progressions := by
  apply List.mem_flatMap.mpr
  refine ⟨d-1, List.mem_range.mpr (by omega), ?_⟩
  have eq : d-1+1 = d := by omega
  dsimp
  rw [eq]
  apply List.mem_map.mpr
  exact ⟨a-1, List.mem_range.mpr (by omega), by simp [show a-1+1=a by omega]⟩

/-- Every list of at most `cutoff` four-term progressions in [1,78] is
simultaneously satisfied by some seven-coloring. Repeated progressions are allowed. -/
theorem progression_family_colorable (chosen : List (Nat × Nat)) (size : chosen.length ≤ cutoff)
    (valid : ∀ p ∈ chosen, 0 < p.1 ∧ 0 < p.2 ∧ p.1 + 3*p.2 ≤ 78) :
    ∃ c : Nat → Fin 7, ∀ p ∈ chosen,
      Three (c p.1) (c (p.1+p.2)) (c (p.1+2*p.2)) (c (p.1+3*p.2)) := by
  have bounded : ∀ p ∈ chosen, selectedWeight Prod.fst (fun r => fails r p) rows ≤ allowance := by
    intro p hp
    obtain ⟨ha, hd, he⟩ := valid p hp
    exact of_decide_eq_true (List.all_eq_true.mp audited.1 p (valid_mem ha hd he))
  have budget := Nat.lt_of_le_of_lt (Nat.mul_le_mul_right allowance size) audited.2
  obtain ⟨row, _, satisfied⟩ := weighted_union_bound Prod.fst fails rows chosen allowance bounded budget
  refine ⟨color row.2, ?_⟩
  intro p hp
  have unnegate : ∀ b : Bool, (!b) = false → b = true := by decide
  exact of_decide_eq_true (unnegate _ (satisfied p hp))

end Erdos160.ProgressionFamily

#print axioms Erdos160.weighted_union_bound
#print axioms Erdos160.ProgressionFamily.progression_family_colorable
