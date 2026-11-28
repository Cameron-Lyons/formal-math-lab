import Ramsey556.Extension

namespace Ramsey556

namespace DensePath

private abbrev Side := List (Fin 7)
private abbrev Table := Fin 7 → Fin 7 → Bool

private def degree (r : Table) (i : Fin 7) (ys : Side) := (ys.filter (r i)).length
private def count (r : Table) (xs ys : Side) := (xs.map (fun i => degree r i ys)).sum
private def flip (r : Table) : Table := fun j i => r i j

private theorem count_cons (r : Table) (i : Fin 7) (xs ys : Side) :
    count r (i :: xs) ys = degree r i ys + count r xs ys := by simp [count]

private theorem count_cons_right (r : Table) (j : Fin 7) (xs ys : Side) :
    count r xs (j :: ys) = degree (flip r) j xs + count r xs ys := by
  induction xs with
  | nil => simp [count, degree]
  | cons i xs ih =>
    rw [count_cons, count_cons, ih]
    cases h : r i j <;> simp [degree, flip, h] <;> omega

private theorem count_flip (r : Table) (xs ys : Side) :
    count (flip r) ys xs = count r xs ys := by
  induction xs with
  | nil =>
    induction ys with
    | nil => rfl
    | cons j ys ih => rw [count_cons, ih]; rfl
  | cons i xs ih =>
    rw [count_cons, count_cons_right, ih]
    rfl

private theorem count_bound (r : Table) (xs ys : Side) :
    count r xs ys ≤ xs.length * ys.length := by
  induction xs with
  | nil => simp [count]
  | cons i xs ih =>
    rw [count_cons, List.length_cons, Nat.succ_mul]
    have hi : degree r i ys ≤ ys.length := List.length_filter_le _ _
    omega

/-- Delete a vertex of degree at most three, preserving the strict inequality
`edges + 9 > 3 * vertices`. A side of size three would violate the inequality. -/
private theorem core (r : Table) (xs ys : Side)
    (hx : xs.Nodup) (hy : ys.Nodup) (mx : 3 ≤ xs.length) (my : 3 ≤ ys.length)
    (dense : 3 * (xs.length + ys.length) < count r xs ys + 9) :
    ∃ X Y : Side, X.Nodup ∧ Y.Nodup ∧ 3 ≤ X.length ∧
      (∀ i ∈ X, 4 ≤ degree r i Y) ∧ (∀ j ∈ Y, 4 ≤ degree (flip r) j X) := by
  have cap := count_bound r xs ys
  have mx' : 3 < xs.length := by
    apply Nat.lt_of_le_of_ne mx
    intro h
    rw [← h] at dense cap
    omega
  have my' : 3 < ys.length := by
    apply Nat.lt_of_le_of_ne my
    intro h
    rw [← h] at dense cap
    simp [Nat.mul_succ] at cap
    omega
  by_cases low : ∃ i ∈ xs, degree r i ys ≤ 3
  · obtain ⟨i, hi, hl⟩ := low
    have perm := List.perm_cons_erase hi
    have size := perm.length_eq
    simp only [List.length_cons] at size
    have count' : count r xs ys = degree r i ys + count r (xs.erase i) ys := by
      rw [← count_cons]
      exact (perm.map _).sum_nat
    exact core r (xs.erase i) ys (hx.erase _) hy (by omega) my (by omega)
  by_cases low' : ∃ j ∈ ys, degree (flip r) j xs ≤ 3
  · obtain ⟨j, hj, hl⟩ := low'
    have perm := List.perm_cons_erase hj
    have size := perm.length_eq
    simp only [List.length_cons] at size
    have count' : count r xs ys = degree (flip r) j xs + count r xs (ys.erase j) := by
      rw [← count_flip, ← count_flip r xs (ys.erase j), ← count_cons]
      exact (perm.map _).sum_nat
    exact core r xs (ys.erase j) hx (hy.erase _) mx (by omega) (by omega)
  exact ⟨xs,ys,hx,hy,mx, fun i hi => Nat.lt_of_not_ge (fun h => low ⟨i,hi,h⟩),
    fun j hj => Nat.lt_of_not_ge (fun h => low' ⟨j,hj,h⟩)⟩
termination_by xs.length + ys.length
decreasing_by all_goals simp only [List.length_cons] at *; omega

private theorem one_color (xs : Side) (p : Fin 7 → Bool) (nd : xs.Nodup)
    (uniq : ∀ i j, p i → p j → i = j) : (xs.filter p).length ≤ 1 := by
  by_cases he : ∃ i, p i
  · obtain ⟨i, hi⟩ := he
    have sub : xs.filter p ⊆ [i] := by
      intro j hj
      simpa using uniq j i (List.mem_filter.mp hj).2 hi
    exact List.Nodup.length_le_of_subset (nd.filter _) sub
  · have he' : xs.filter p = [] := List.filter_eq_nil_iff.mpr (fun j _ hj => he ⟨j,hj⟩)
    simp [he']

private theorem count_le_seven (r : Table) (uniq : ∀ i j j', r i j → r i j' → j = j') :
    count r (List.finRange 7) (List.finRange 7) ≤ 7 := by
  suffices ∀ xs, count r xs (List.finRange 7) ≤ xs.length by simpa using this (List.finRange 7)
  intro xs
  induction xs with
  | nil => simp [count]
  | cons i xs ih =>
    rw [count_cons, List.length_cons]
    have h : degree r i (List.finRange 7) ≤ 1 := one_color _ _ (List.nodup_finRange _) (uniq i)
    omega

private theorem count_colors (f : Fin 7 → Fin 7 → Fin 3) (xs ys : Side) :
    let eqk := fun k (i j : Fin 7) => decide (f i j = k)
    count (eqk 0) xs ys + count (eqk 1) xs ys + count (eqk 2) xs ys = xs.length * ys.length := by
  let eqk := fun k (i j : Fin 7) => decide (f i j = k)
  change count (eqk 0) xs ys + count (eqk 1) xs ys + count (eqk 2) xs ys = _
  have row (i : Fin 7) : degree (eqk 0) i ys + degree (eqk 1) i ys + degree (eqk 2) i ys = ys.length := by
    induction ys with
    | nil => rfl
    | cons j ys ih =>
      have h : f i j = 0 ∨ f i j = 1 ∨ f i j = 2 := by omega
      rcases h with h|h|h <;> simp [degree, eqk, h] at * <;> omega
  induction xs with
  | nil => simp [count]
  | cons i xs ih =>
    simp only [count_cons, List.length_cons, Nat.succ_mul]
    have := row i
    omega

private theorem chooseFresh (xs : Side) (p : Fin 7 → Bool) (nd : xs.Nodup)
    (h : 4 ≤ (xs.filter p).length) (used : Side) (len : used.length ≤ 3) :
    ∃ i ∈ xs, p i ∧ i ∉ used := by
  apply Classical.byContradiction
  intro missing
  have sub : xs.filter p ⊆ used := by
    intro i hi
    obtain ⟨hm, hp⟩ := List.mem_filter.mp hi
    exact Classical.byContradiction (fun hnot => missing ⟨i,hm,hp,hnot⟩)
  have := List.Nodup.length_le_of_subset (nd.filter _) sub
  omega

end DensePath

/-- Two seven-vertex sets have red spokes to z. Among their cross edges
color 1 can occur at most once per column and color 2 at most once per row.
At least 35 edges are red. Their bipartite graph has a nonempty subgraph of
minimum degree four, in which a greedy alternating path closes through z. -/
theorem dense_mixed_octets_cycle {n : Nat} (c : Coloring n) (a b : Fin 7 → Fin n) (z : Fin n)
    (ha : ∀ ⦃i j⦄, a i = a j → i = j) (hb : ∀ ⦃i j⦄, b i = b j → i = j)
    (hab : ∀ i j, a i ≠ b j) (haz : ∀ i, a i ≠ z) (hbz : ∀ j, b j ≠ z)
    (sa : ∀ i, c.edge z (a i) = 0) (sb : ∀ j, c.edge z (b j) = 0)
    (h₁ : ∀ i i' j, c.edge (a i) (b j) = 1 → c.edge (a i') (b j) = 1 → i = i')
    (h₂ : ∀ i j j', c.edge (a i) (b j) = 2 → c.edge (a i) (b j') = 2 → j = j') :
    HasMonoC9 c := by
  let eqk (k : Fin 3) (i j : Fin 7) := decide (c.edge (a i) (b j) = k)
  let all := List.finRange 7
  have size : all.length = 7 := by simp [all]
  have bound₁ : DensePath.count (eqk 1) all all ≤ 7 := by
    rw [← DensePath.count_flip]
    apply DensePath.count_le_seven
    intro j i i' hi hi'
    exact h₁ i i' j (of_decide_eq_true hi) (of_decide_eq_true hi')
  have bound₂ : DensePath.count (eqk 2) all all ≤ 7 := by
    apply DensePath.count_le_seven
    intro i j j' hj hj'
    exact h₂ i j j' (of_decide_eq_true hj) (of_decide_eq_true hj')
  have total : DensePath.count (eqk 0) all all + DensePath.count (eqk 1) all all
      + DensePath.count (eqk 2) all all = 49 := by
    simpa only [size] using DensePath.count_colors (fun i j => c.edge (a i) (b j)) all all
  obtain ⟨X, Y, nx, ny, hasX, rows, cols⟩ :=
    DensePath.core (eqk 0) all all (List.nodup_finRange _) (List.nodup_finRange _)
      (by omega) (by omega) (by omega)
  have nextB (i : Fin 7) (hi : i ∈ X) (used : List (Fin 7)) (len : used.length ≤ 3) :
      ∃ j ∈ Y, c.edge (a i) (b j) = 0 ∧ j ∉ used := by
    obtain ⟨j,hj,e,fresh⟩ := DensePath.chooseFresh Y (eqk 0 i) ny (rows i hi) used len
    exact ⟨j,hj,of_decide_eq_true e,fresh⟩
  have nextA (j : Fin 7) (hj : j ∈ Y) (used : List (Fin 7)) (len : used.length ≤ 3) :
      ∃ i ∈ X, c.edge (b j) (a i) = 0 ∧ i ∉ used := by
    obtain ⟨i,hi,e,fresh⟩ := DensePath.chooseFresh X (DensePath.flip (eqk 0) j)
      nx (cols j hj) used len
    exact ⟨i,hi,(c.symm _ _).trans (of_decide_eq_true e),fresh⟩
  obtain ⟨u,hu⟩ := List.exists_mem_of_length_pos (l := X) (by omega)
  obtain ⟨v,hv,e₀,_⟩ := nextB u hu [] (by decide)
  obtain ⟨w,hw,e₁,fw⟩ := nextA v hv [u] (by simp)
  obtain ⟨x,hx,e₂,fx⟩ := nextB w hw [v] (by simp)
  obtain ⟨y,hy,e₃,fy⟩ := nextA x hx [u,w] (by simp)
  obtain ⟨t,ht,e₄,ft⟩ := nextB y hy [v,x] (by simp)
  obtain ⟨s,hs,e₅,fs⟩ := nextA t ht [u,w,y] (by simp)
  obtain ⟨r,_,e₆,fr⟩ := nextB s hs [v,x,t] (by simp)
  let path := [a u,b v,a w,b x,a y,b t,a s,b r]
  have distinct : path.Nodup := by
    have ae (i j : Fin 7) : a i = a j ↔ i = j := ⟨fun h => ha h, congrArg a⟩
    have be (i j : Fin 7) : b i = b j ↔ i = j := ⟨fun h => hb h, congrArg b⟩
    have ba (i j : Fin 7) := Ne.symm (hab j i)
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at fw fx fy ft fs fr
    simp only [path,List.nodup_cons,List.nodup_nil,List.mem_cons,List.mem_nil_iff,or_false,
      not_or,ae,be,hab,ba,and_true]
    grind
  let p (i : Fin 8) := path[i.val]'(by change _ < 8; exact i.isLt)
  have slots (i : Fin 8) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
  apply closeC9Through c 0 p z
  · exact fun {_ _} h => Fin.ext (distinct.eq_of_getElem_eq _ _ h)
  · intro i
    rcases slots i with h|h|h|h|h|h|h|h <;> subst i <;> first | exact haz _ | exact hbz _
  · intro i h
    rcases slots i with h'|h'|h'|h'|h'|h'|h'|h' <;> subst i
    · exact e₀
    · exact e₁
    · exact e₂
    · exact e₃
    · exact e₄
    · exact e₅
    · exact e₆
    · omega
  · exact sa _
  · exact sb _

end Ramsey556
