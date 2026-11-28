import MirroredBlocks

/-! No sequence of fifteen permutation blocks, each followed by its reverse,
can give five fair 30-sided dice. The integer weights below certify a lower
bound; the solver that found them is not used in the verification. -/
namespace FiveDice.Mirrored

/-- In a ranking, mark the selected die 0, the other two members of the triple
1, and the two outside dice 2. These are the nonzero certificate weights. -/
private def weight (j : Fin 3) (r : Fin 120) : Int :=
  let key := (perm r).map fun d => if d.val = j.val then 0 else if d.val < 3 then 1 else 2
  match (key : List Nat) with
  | [0, 1, 1, 2, 2] => -43144
  | [0, 2, 1, 1, 2] => 42872
  | [0, 2, 1, 2, 1] => -28
  | [1, 0, 1, 2, 2] => -52066
  | [1, 0, 2, 1, 2] => -38923
  | [1, 0, 2, 2, 1] => 17420
  | [1, 2, 0, 1, 2] => -46607
  | [1, 2, 1, 0, 2] => 136
  | [1, 2, 2, 0, 1] => -17420
  | [2, 0, 1, 1, 2] => -10896
  | [2, 0, 1, 2, 1] => 28672
  | [2, 0, 2, 1, 1] => 25040
  | [2, 1, 0, 1, 2] => 21658
  | [2, 1, 0, 2, 1] => -25185
  | [2, 1, 2, 0, 1] => -7865
  | [2, 2, 0, 1, 1] => 50080
  | [2, 2, 1, 0, 1] => 1746
  | _ => 0

private def weights : Array (Array Int) :=
  ((List.finRange 3).map fun j => ((List.finRange 120).map (weight j)).toArray).toArray

/-- Half of (t − 7)(t − 8) at positions 0 through 14. -/
private def load (t : Nat) : Int :=
  (#[28, 21, 15, 10, 6, 3, 1, 0, 0, 1, 3, 6, 10, 15, 21] : Array Int)[t]?.getD 0

private def share (j : Fin 3) (t : Nat) (p : Fin 120) : Int :=
  let first := ((perm p).filter fun d => d.val < 3).headD 0
  if first.val = j.val then load t else 0

private abbrev Indexed := Fin 120 × Nat

private def score (j : Fin 3) (f : Fin 120 → Int) : Int :=
  ((List.finRange 120).map (fun r => weights[j.val]![r.val]! * f r)).sum

private def floorAt (j : Fin 3) (t : Nat) : Int :=
  if j.val = 0 then 3456000 * load t - 36000 else if j.val = 1 then -43200 else 0

private def target (r : Fin 120) : Int := 202500 - base r

/-- Each row is one exact integer inequality for one possible local block. -/
private theorem local_bounds : ∀ (j : Fin 3) (t : Fin 15) (p : Fin 120),
    floorAt j t.val + score j (delta t.val p) ≤ 3456000 * share j t.val p := by
  native_decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private theorem total_lower : ∀ j : Fin 3,
    158976000 < ((List.range' 0 15).map (floorAt j)).sum + score j target := by
  decide +kernel

private theorem distributed : ∀ (t : Fin 15) (p : Fin 120),
    share 0 t.val p + share 1 t.val p + share 2 t.val p = load t.val := by
  intro t p
  generalize h : (perm p).filter (fun d => decide (d.val < 3)) = l
  have bound : (l.headD 0).val < 3 := by
    cases l with
    | nil => decide
    | cons x xs =>
      have hx : x ∈ (perm p).filter (fun d => decide (d.val < 3)) := by simp [h]
      exact of_decide_eq_true (List.mem_filter.mp hx).2
  simp only [share, h]
  have : (l.headD 0).val = 0 ∨ (l.headD 0).val = 1 ∨ (l.headD 0).val = 2 := by omega
  rcases this with e | e | e <;> rw [e] <;> simp

private theorem sum_add_f {α : Type} (as : List α) (f g : α → Int) :
    (as.map fun a => f a + g a).sum = (as.map f).sum + (as.map g).sum := by
  induction as with
  | nil => simp
  | cons a as ih => simp only [List.map_cons, List.sum_cons, ih]; omega

private theorem sum_mul_f {α : Type} (as : List α) (c : Int) (f : α → Int) :
    (as.map fun a => c * f a).sum = c * (as.map f).sum := by
  induction as with
  | nil => simp
  | cons a as ih => simp [ih, Int.mul_add]

private theorem sum_le_f {α : Type} (as : List α) (f g : α → Int)
    (h : ∀ a ∈ as, f a ≤ g a) : (as.map f).sum ≤ (as.map g).sum := by
  induction as with
  | nil => simp
  | cons a as ih =>
    have ha := h a (by simp)
    have hb := ih (fun b hb => h b (by simp [hb]))
    simp only [List.map_cons, List.sum_cons]
    omega

private theorem score_add (j : Fin 3) (f g : Fin 120 → Int) :
    score j (fun r => f r + g r) = score j f + score j g := by
  simp only [score, Int.mul_add, sum_add_f]

private theorem score_sum (j : Fin 3) (xs : List Indexed) :
    score j (fun r => (xs.map fun x => delta x.2 x.1 r).sum) =
      (xs.map fun x => score j (delta x.2 x.1)).sum := by
  induction xs with
  | nil =>
    simp [score]
    induction (List.finRange 120) with
    | nil => simp
    | cons h t ih => simp [ih]
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, score_add, ih]

private theorem sum_indices (f : Nat → Int) (ps : List (Fin 120)) (len : ps.length = 15) :
    (ps.zipIdx.map fun pt => f pt.2).sum = ((List.range' 0 15).map f).sum := by
  change (ps.zipIdx.map (f ∘ Prod.snd)).sum = _
  rw [← List.map_map, List.zipIdx_map_snd, len]

/-- A block awards its full weight to the first of dice 0, 1, and 2 in its permutation. -/
private def points (j : Fin 3) (ps : List (Fin 120)) : Int :=
  (ps.zipIdx.map fun pt => share j pt.2 pt.1).sum

/-- Summing the certified local inequalities gives strictly more than 46 points per die. -/
private theorem points_of_fair (j : Fin 3) (ps : List (Fin 120)) (len : ps.length = 15)
    (fair : Fair 30 (word ps)) : 47 ≤ points j ps := by
  have ht : target = fun r => (ps.zipIdx.map fun pt => delta pt.2 pt.1 r).sum := by
    funext r
    have blocks := ways_blocks ps len r
    have count := fair.2.2 (perm r) (perm_valid r).1 (perm_valid r).2
    rw [← ways_eq_labelChoices_length] at count
    unfold target
    omega
  have H := sum_le_f ps.zipIdx
    (fun x => floorAt j x.2 + score j (delta x.2 x.1))
    (fun x => 3456000 * share j x.2 x.1) (by
      intro x hx
      have hlt : x.2 < 15 := by simpa [len] using List.snd_lt_of_mem_zipIdx hx
      exact local_bounds j ⟨x.2, hlt⟩ x.1)
  rw [sum_add_f, sum_mul_f, ← score_sum, ← ht, sum_indices _ ps len] at H
  have lb := total_lower j
  unfold points
  omega

/-- Every point is awarded exactly once, and the fifteen block weights sum to 140. -/
private theorem points_total (ps : List (Fin 120)) (len : ps.length = 15) :
    points 0 ps + points 1 ps + points 2 ps = 140 := by
  unfold points
  rw [← sum_add_f, ← sum_add_f]
  have eqs : ps.zipIdx.map (fun x => share 0 x.2 x.1 + share 1 x.2 x.1 + share 2 x.2 x.1) =
      ps.zipIdx.map (fun x => load x.2) := by
    apply List.map_congr_left
    intro x hx
    have hlt : x.2 < 15 := by simpa [len] using List.snd_lt_of_mem_zipIdx hx
    exact distributed ⟨x.2, hlt⟩ x.1
  rw [eqs, sum_indices _ ps len]
  decide

/-- Fairness would require at least 141 points, but the blocks award only 140. -/
theorem no_fifteen_mirrored (ps : List (Fin 120)) (len : ps.length = 15) :
    ¬ Fair 30 (word ps) := by
  intro fair
  have h0 := points_of_fair 0 ps len fair
  have h1 := points_of_fair 1 ps len fair
  have h2 := points_of_fair 2 ps len fair
  have total := points_total ps len
  omega

end FiveDice.Mirrored
