import SpliceRanges

namespace TBoards.Splice

/-- Global palette permutations, with the row orientation fixed. -/
def paletteActions : List Action := colorPermutations.map fun p => (p, false)

/-- First appearances of the three colors recover the permutation on a canonical prefix. -/
def readPalette (rows : Board) : Nat := actions.idxOf (rows.flatten.eraseDups, false)

/-- Every renamed cap and pivot has palindromic rows and identifies the applied palette. -/
def PalChecked (g : Group) : Prop := ∀ cap ∈ g.caps, ∀ op ∈ paletteActions,
  let rows := (cap ++ [g.pivot]).map (actRow op)
  rows.map List.reverse = rows ∧ readPalette rows = actions.idxOf op

instance (g : Group) : Decidable (PalChecked g) := by unfold PalChecked; infer_instance

private theorem pal_prefix {k : Nat} {groups : List Group}
    (checked : ∀ g ∈ groups, g.Checked) (cut : ∀ g ∈ groups, g.k = k)
    (pal : ∀ g ∈ groups, PalChecked g) {op : Action} (ho : op ∈ paletteActions)
    {b : Board} (hb : b ∈ groups.flatMap Group.boards) :
    let rows := (b.map (actRow op)).take (k+1)
    rows.map List.reverse = rows ∧ readPalette rows = actions.idxOf op := by
  obtain ⟨g, hg, hgb⟩ := List.mem_flatMap.mp hb
  obtain ⟨cap, hc, hbs⟩ := List.mem_flatMap.mp hgb
  obtain ⟨tail, _, rfl⟩ := List.mem_map.mp hbs
  have hlen : (cap ++ [g.pivot]).length = k+1 := by
    simp [g.cap_length (checked g hg) hc, cut g hg]
  dsimp only
  rw [← List.map_take, show cap ++ g.pivot :: tail = (cap ++ [g.pivot]) ++ tail by simp,
    List.take_left' hlen]
  exact pal g hg cap hc op ho

private theorem opposite_image (b : Board) (p : List Nat) (r : Bool) :
    b.map (actRow (p,!r)) = (b.map (actRow (p,r))).map List.reverse := by
  cases r <;> simp [actRow, List.map_map, Function.comp_def, ← List.map_reverse]

/-- A symmetric upper prefix would give the same classifier input for the two orientations. -/
theorem classified_prefix_not_pal {k : Nat} {groups : List Group} {classify : Nat → Nat}
    (checked : ∀ g ∈ groups, g.Checked) (cut : ∀ g ∈ groups, g.k = k)
    (classified : ∀ g ∈ groups, PrefixClassified classify g)
    {b : Board} (hb : b ∈ actionImages actions groups) :
    (b.take (k+1)).map List.reverse ≠ b.take (k+1) := by
  obtain ⟨⟨p, r⟩, ho, hm⟩ := List.mem_flatMap.mp hb
  obtain ⟨base, hbase, rfl⟩ := List.mem_map.mp hm
  have pair : ∀ op ∈ actions, (op.1, !op.2) ∈ actions ∧
      actions.idxOf (op.1,!op.2) ≠ actions.idxOf op := by decide
  obtain ⟨hop, hdiff⟩ := pair (p,r) ho
  have hleft := prefix_action_identified checked cut classified hop hbase
  have hright := prefix_action_identified checked cut classified ho hbase
  intro eq
  change classify (boardCode ((base.map (actRow (p,!r))).take (k+1))) = _ at hleft
  rw [opposite_image, ← List.map_take, eq] at hleft
  exact hdiff (hleft.symm.trans hright)

/-- Join the twelve-image families to six palette images of each palindromic-prefix product. -/
theorem pal_supplement_lower_bound (k : Nat) (ordinary pal : List Group) (classify : Nat → Nat) (n : Nat)
    (checked : ∀ g ∈ ordinary, g.Checked) (cut : ∀ g ∈ ordinary, g.k = k)
    (distinct : (ordinary.flatMap Group.boards).Nodup)
    (classified : ∀ g ∈ ordinary, PrefixClassified classify g)
    (checkedP : ∀ g ∈ pal, g.Checked) (cutP : ∀ g ∈ pal, g.k = k)
    (distinctP : (pal.map Group.signature).Nodup) (palP : ∀ g ∈ pal, PalChecked g)
    (count : n ≤ 12 * (ordinary.map Group.size).sum + 6 * (pal.map Group.size).sum) :
    ∃ f : Fin n → Board, (∀ i, Valid (f i)) ∧ (∀ i j, f i = f j → i = j) := by
  have included : ∀ op ∈ paletteActions, op ∈ actions := by decide
  apply injective_family_of_list (actionImages actions ordinary ++ actionImages paletteActions pal) n
  · rw [List.length_append, actionImages_length, actionImages_length,
      show actions.length = 12 by decide, show paletteActions.length = 6 by decide]
    exact count
  · apply List.nodup_append.mpr
    refine ⟨?_, ?_, ?_⟩
    · apply actionImages_nodup (fun b => classify (boardCode (b.take (k+1))))
        (fun _ h => h) checked distinct (by decide)
      exact fun _ h _ hb => prefix_action_identified checked cut classified h hb
    · apply actionImages_nodup (fun b => readPalette (b.take (k+1))) included checkedP
        (groups_nodup k pal checkedP cutP distinctP) (by decide)
      exact fun _ h _ hb => (pal_prefix checkedP cutP palP h hb).2
    · intro b hb c hc eq
      obtain ⟨op, ho, hm⟩ := List.mem_flatMap.mp hc
      obtain ⟨base, hbase, rfl⟩ := List.mem_map.mp hm
      rw [eq] at hb
      exact classified_prefix_not_pal checked cut classified hb (pal_prefix checkedP cutP palP ho hbase).1
  · exact List.forall_mem_append.mpr ⟨actionImages_valid (fun _ h => h) checked, actionImages_valid included checkedP⟩

end TBoards.Splice
