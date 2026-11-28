import Ramsey556.Bipartite
import Ramsey556.BetweenCliques

namespace Ramsey556

/-- Four eight-vertex cliques in color 2, with five vertices of each clique
    free of color 2 on every edge to a different clique. The row and column
    restrictions record the two original bipartitions. -/
structure CleanSquare (c : Coloring 32) where
  vertex : Fin 4 → Fin 8 → Fin 32
  inj : ∀ ⦃a b i j⦄, vertex a i = vertex b j → a = b ∧ i = j
  inside : ∀ a i j, i ≠ j → c.edge (vertex a i) (vertex a j) = 2
  clean : ∀ a b i j, a ≠ b → i.val < 5 → c.edge (vertex a i) (vertex b j) ≠ 2
  row : ∀ a b i j, a ≠ b → a.val / 2 = b.val / 2 → c.edge (vertex a i) (vertex b j) ≠ 0
  col : ∀ a b i j, a ≠ b → a.val % 2 = b.val % 2 → c.edge (vertex a i) (vertex b j) ≠ 1

namespace CleanSquare

private def whichCell (r s : Bool) : Fin 4 := ⟨r.toNat * 2 + s.toNat, by cases r <;> cases s <;> decide⟩

private def part {α : Type} (tag : α → Fin 4) (xs : List α) (a : Fin 4) : List α :=
  xs.filter (fun x => tag x == a)

private theorem part_total {α : Type} (tag : α → Fin 4) (xs : List α) :
    (part tag xs 0).length + (part tag xs 1).length +
    (part tag xs 2).length + (part tag xs 3).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have h : tag x = 0 ∨ tag x = 1 ∨ tag x = 2 ∨ tag x = 3 := by omega
    simp only [part] at *
    rcases h with h | h | h | h <;> simp [h] <;> omega

private theorem part_sizes (c : Coloring 32) (tag : Fin 32 → Fin 4)
    (clique : ∀ u v, u ≠ v → tag u = tag v → c.edge u v = 2)
    (free : ¬ HasMonoC9 c) :
    ∀ a, (part tag (List.finRange 32) a).length = 8 := by
  let cell := part tag (List.finRange 32)
  have bound (a : Fin 4) : (cell a).length ≤ 8 := by
    apply Nat.le_of_not_gt
    intro h
    let v (i : Fin 9) := (cell a)[i.val]'(by omega)
    have nd : (cell a).Nodup := (List.nodup_finRange 32).filter _
    have hi : ∀ ⦃i j⦄, v i = v j → i = j := fun {_ _} he =>
      Fin.ext (nd.eq_of_getElem_eq _ _ he)
    have inCell (i : Fin 9) : tag (v i) = a := by
      have hm : v i ∈ cell a := List.getElem_mem ..
      simpa [cell, part] using hm
    apply free
    refine ⟨2, v, hi, fun i => clique _ _ ?_ ((inCell i).trans (inCell (i+1)).symm)⟩
    exact fun he => (show ∀ j : Fin 9, j ≠ j + 1 by decide) i (hi he)
  have total := part_total tag (List.finRange 32)
  change (cell 0).length + (cell 1).length + (cell 2).length + (cell 3).length = 32 at total
  have h0 := bound 0
  have h1 := bound 1
  have h2 := bound 2
  have h3 := bound 3
  intro a
  change (cell a).length = 8
  have h : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> omega

/-- Put the slots avoiding three marked vertices first. Repeated marks are allowed. -/
private theorem reorder (x y z : Fin 8) :
    ∃ f : Fin 8 → Fin 8, (∀ ⦃i j⦄, f i = f j → i = j) ∧
      ∀ i, i.val < 5 → f i ≠ x ∧ f i ≠ y ∧ f i ≠ z := by
  let good (i : Fin 8) := !(i == x || i == y || i == z)
  let slots := (List.finRange 8).filter good
  let rest := (List.finRange 8).filter (fun i => !good i)
  have hp : (slots ++ rest).Perm (List.finRange 8) := List.filter_append_perm good _
  have len : (slots ++ rest).length = 8 := by simpa using hp.length_eq
  have sub : ∀ ⦃i⦄, i ∈ rest → i ∈ [x, y, z] := by
    intro i hi
    simpa [rest, good, or_assoc] using hi
  have nd : rest.Nodup := (List.nodup_finRange 8).filter _
  have bound : rest.length ≤ 3 := nd.length_le_of_subset sub
  have len' : 5 ≤ slots.length := by rw [List.length_append] at len; omega
  let f (i : Fin 8) := (slots ++ rest)[i.val]'(by omega)
  refine ⟨f, fun {_ _} he => Fin.ext ((hp.nodup_iff.mpr (List.nodup_finRange 8)).eq_of_getElem_eq _ _ he), ?_⟩
  intro i hi
  have hf : f i ∈ slots := by
    dsimp only [f]
    rw [List.getElem_append_left (by omega)]
    exact List.getElem_mem ..
  simpa [slots, good, and_assoc] using hf

end CleanSquare

/-- A cycle-free coloring on 32 vertices whose first two colors are bipartite
    admits four balanced cliques and five clean representatives in each. -/
theorem exists_cleanSquare (c : Coloring 32) (free : ¬ HasMonoC9 c)
    (hr : IsBipartiteColor c 0) (hb : IsBipartiteColor c 1) : Nonempty (CleanSquare c) := by
  classical
  obtain ⟨row, hrow⟩ := hr
  obtain ⟨col, hcol⟩ := hb
  let tag (v : Fin 32) := CleanSquare.whichCell (row v) (col v)
  have rowBit : ∀ r s : Bool, (CleanSquare.whichCell r s).val / 2 = r.toNat := by decide
  have colBit : ∀ r s : Bool, (CleanSquare.whichCell r s).val % 2 = s.toNat := by decide
  have boolInj : ∀ (r s : Bool), r.toNat = s.toNat → r = s := by decide
  have noR (u v : Fin 32) (hd : u ≠ v) (h : (tag u).val / 2 = (tag v).val / 2) :
      c.edge u v ≠ 0 := by
    intro e
    exact hrow u v hd e (boolInj _ _ (by simpa [tag, rowBit] using h))
  have noB (u v : Fin 32) (hd : u ≠ v) (h : (tag u).val % 2 = (tag v).val % 2) :
      c.edge u v ≠ 1 := by
    intro e
    exact hcol u v hd e (boolInj _ _ (by simpa [tag, colBit] using h))
  have clique (u v : Fin 32) (hd : u ≠ v) (h : tag u = tag v) : c.edge u v = 2 := by
    have h0 := noR u v hd (by rw [h])
    have h1 := noB u v hd (by rw [h])
    omega
  -- A ninth vertex in one cell would close a cycle. Since the cells partition
  -- 32 vertices, each has precisely eight and can be indexed by Fin 8.
  let cell := CleanSquare.part tag (List.finRange 32)
  have size := CleanSquare.part_sizes c tag clique free
  let base (a : Fin 4) (i : Fin 8) := (cell a)[i.val]'(by rw [size]; exact i.isLt)
  have label (a i) : tag (base a i) = a := by
    have hm : base a i ∈ cell a := List.getElem_mem ..
    simpa [cell, CleanSquare.part] using hm
  have slotInj (a) : ∀ ⦃i j⦄, base a i = base a j → i = j := by
    have nd : (cell a).Nodup := (List.nodup_finRange 32).filter _
    exact fun {_ _} he => Fin.ext (nd.eq_of_getElem_eq _ _ he)
  have disj {a b : Fin 4} (hab : a ≠ b) (i j : Fin 8) : base a i ≠ base b j := by
    intro e
    exact hab ((label a i).symm.trans ((congrArg tag e).trans (label b j)))
  have inside (a i j) (hd : i ≠ j) : c.edge (base a i) (base a j) = 2 :=
    clique _ _ (fun e => hd (slotInj _ e)) ((label _ _).trans (label _ _).symm)
  -- For each of the other three cells there is at most one exceptional endpoint.
  let active (a b : Fin 4) := ∃ i j, c.edge (base a i) (base b j) = 2
  let mark (a b : Fin 4) : Fin 8 := if h : active a b then h.choose else 0
  have uniqueMark (a b i j) (hab : a ≠ b) (e : c.edge (base a i) (base b j) = 2) :
      i = mark a b := by
    have h : active a b := ⟨i, j, e⟩
    obtain ⟨j', e'⟩ := h.choose_spec
    simp only [mark, dite_eq_left h]
    exact clique_cross_unique c 2 (base a) (base b) (slotInj a) (slotInj b) (disj hab)
      (inside a) (inside b) free e e'
  have perm (a : Fin 4) := CleanSquare.reorder (mark a (a+1)) (mark a (a+2)) (mark a (a+3))
  let v (a i) := base a ((perm a).choose i)
  have tagV (a i) : tag (v a i) = a := label _ _
  have vi (a) : ∀ ⦃i j⦄, v a i = v a j → i = j :=
    fun {_ _} e => (perm a).choose_spec.1 (slotInj a e)
  refine ⟨⟨v, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro a b i j e
    have eq := (tagV a i).symm.trans ((congrArg tag e).trans (tagV b j))
    subst b
    exact ⟨rfl, vi _ e⟩
  · intro a i j hd
    exact clique _ _ (fun e => hd (vi _ e)) ((tagV _ _).trans (tagV _ _).symm)
  · intro a b i j hab hi e
    have bad := uniqueMark a b _ _ hab e
    obtain ⟨h1, h2, h3⟩ := (perm a).choose_spec.2 i hi
    have cases : ∀ a b : Fin 4, a ≠ b → b = a+1 ∨ b = a+2 ∨ b = a+3 := by decide
    rcases cases a b hab with rfl | rfl | rfl
    · exact h1 bad
    · exact h2 bad
    · exact h3 bad
  · intro a b i j hab h
    exact noR _ _ (disj hab _ _) (by rwa [tagV, tagV])
  · intro a b i j hab h
    exact noB _ _ (disj hab _ _) (by rwa [tagV, tagV])

end Ramsey556
