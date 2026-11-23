import SpliceSymmetry

namespace TBoards.Splice

/-- A finite decision tree for action indices. The kernel checks its output
on every transformed upper section used by the certificate. -/
inductive PrefixClassifier where
  | label (action : Nat)
  | branch (boundary : Nat) (left right : PrefixClassifier)

def PrefixClassifier.lookup : PrefixClassifier → Nat → Nat
  | .label action, _ => action
  | .branch boundary left right, key =>
    if key ≤ boundary then left.lookup key else right.lookup key

/-- Each transformed upper section must identify the action that produced it. -/
def PrefixClassified (classify : Nat → Nat) (g : Group) : Prop :=
  ∀ cap ∈ g.caps, ∀ op ∈ actions,
    classify (boardCode ((cap ++ [g.pivot]).map (actRow op))) = actions.idxOf op

instance (classify : Nat → Nat) (g : Group) : Decidable (PrefixClassified classify g) := by
  unfold PrefixClassified
  infer_instance

theorem prefix_action_identified {classify : Nat → Nat} {k : Nat} {groups : List Group}
    (checked : ∀ g ∈ groups, g.Checked) (cut : ∀ g ∈ groups, g.k = k)
    (classified : ∀ g ∈ groups, PrefixClassified classify g)
    {op : Action} (ho : op ∈ actions) {b : Board} (hb : b ∈ groups.flatMap Group.boards) :
    classify (boardCode ((b.map (actRow op)).take (k+1))) = actions.idxOf op := by
  obtain ⟨g, hg, hgb⟩ := List.mem_flatMap.mp hb
  obtain ⟨cap, hc, hbs⟩ := List.mem_flatMap.mp hgb
  obtain ⟨tail, _, rfl⟩ := List.mem_map.mp hbs
  have hlen : (cap ++ [g.pivot]).length = k+1 := by
    simp [g.cap_length (checked g hg) hc, cut g hg]
  rw [← List.map_take]
  have hj : cap ++ g.pivot :: tail = (cap ++ [g.pivot]) ++ tail := by simp
  rw [hj]
  rw [← hlen, List.take_left]
  exact classified g hg cap hc op ho

private theorem palette_mem {op : Action} (ho : op ∈ actions) : op.1 ∈ colorPermutations := by
  obtain ⟨p, hp, h⟩ := List.mem_flatMap.mp ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> exact hp

private theorem action_valid {op : Action} (ho : op ∈ actions) {b : Board} (h : Valid b) :
    Valid (b.map (actRow op)) := by
  obtain ⟨p, r⟩ := op
  have hp := palette_mem ho
  cases r with
  | false => exact valid_transform_colors h p hp
  | true =>
    change Valid (b.map (fun row => row.reverse.map (fun c => p.getD c 0)))
    simpa [actRow, transform, List.map_map, Function.comp_def, ← List.map_reverse]
      using valid_transform_colors (valid_reverse h) p hp

private theorem undo_action {b : Board} (h : WellFormed b) {p q : List Nat}
    (inverse : PaletteInverse p q) (r : Bool) :
    (b.map (actRow (p,r))).map (actRow (q,r)) = b := by
  rw [List.map_map]
  apply Eq.trans ?_ (List.map_id b)
  apply List.map_congr_left
  intro row hr
  have undo : row.map (fun c => q.getD (p.getD c 0) 0) = row := by
    apply Eq.trans ?_ (List.map_id row)
    exact List.map_congr_left fun c hc => inverse.2.2.1 ⟨c, h.2.2 _ hr _ hc⟩
  cases r <;> simpa [actRow, List.map_map, Function.comp_def, ← List.map_reverse] using undo

/-- Apply each listed symmetry to every splice product. -/
def actionImages (ops : List Action) (groups : List Group) : List Board :=
  ops.flatMap fun op => (groups.flatMap Group.boards).map (List.map (actRow op))

theorem actionImages_length (ops : List Action) (groups : List Group) :
    (actionImages ops groups).length = ops.length * (groups.map Group.size).sum := by
  simp [actionImages, List.length_flatMap, Group.boards_length, List.map_const', List.sum_replicate_nat]

theorem actionImages_valid {ops : List Action} {groups : List Group}
    (included : ∀ op ∈ ops, op ∈ actions) (checked : ∀ g ∈ groups, g.Checked) :
    ∀ b ∈ actionImages ops groups, Valid b := by
  intro b hb
  obtain ⟨op, ho, hm⟩ := List.mem_flatMap.mp hb
  obtain ⟨base, hbase, rfl⟩ := List.mem_map.mp hm
  exact action_valid (included op ho) (groups_valid checked base hbase)

theorem actionImages_nodup {ops : List Action} {groups : List Group} (readAction : Board → Nat)
    (included : ∀ op ∈ ops, op ∈ actions) (checked : ∀ g ∈ groups, g.Checked)
    (distinct : (groups.flatMap Group.boards).Nodup)
    (idx : ops.Pairwise (fun a b => actions.idxOf a ≠ actions.idxOf b))
    (identified : ∀ op ∈ ops, ∀ b ∈ groups.flatMap Group.boards,
      readAction (b.map (actRow op)) = actions.idxOf op) : (actionImages ops groups).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro op ho
    apply List.pairwise_map.mpr
    apply distinct.imp_of_mem
    intro a b ha hb hab he
    obtain ⟨q, _, hq⟩ := colorPermutations_have_inverse op.1 (palette_mem (included op ho))
    have hh := congrArg (List.map (actRow (q, op.2))) he
    exact hab ((undo_action (groups_valid checked a ha).1 hq op.2).symm.trans
      (hh.trans (undo_action (groups_valid checked b hb).1 hq op.2)))
  · apply idx.imp_of_mem
    intro op op' ho ho' hne x hx y hy he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
    exact hne ((identified op ho a ha).symm.trans ((congrArg readAction he).trans (identified op' ho' b hb)))

/-- Count the twelve symmetry images when their actions can be read from a
finite table of transformed cap-and-pivot prefixes. -/
theorem prefix_orbit_lower_bound_of_nodup (k : Nat) (groups : List Group) (classify : Nat → Nat) (n : Nat)
    (checked : ∀ g ∈ groups, g.Checked)
    (cut : ∀ g ∈ groups, g.k = k)
    (distinct : (groups.flatMap Group.boards).Nodup)
    (classified : ∀ g ∈ groups, PrefixClassified classify g)
    (count : n ≤ 12 * (groups.map Group.size).sum) :
    ∃ f : Fin n → Board, (∀ i, Valid (f i)) ∧ (∀ i j, f i = f j → i = j) := by
  apply injective_family_of_list (actionImages actions groups) n
  · rw [actionImages_length, show actions.length = 12 by decide]
    exact count
  · apply actionImages_nodup (fun b => classify (boardCode (b.take (k+1))))
      (fun _ h => h) checked distinct (by decide)
    exact fun _ ho _ hb => prefix_action_identified checked cut classified ho hb
  · exact actionImages_valid (fun _ h => h) checked

/-- Count the twelve symmetry images when their actions can be read from a
finite table of transformed cap-and-pivot prefixes, and distinct signatures identify the groups. -/
theorem prefix_orbit_lower_bound (k : Nat) (groups : List Group) (classify : Nat → Nat) (n : Nat)
    (checked : ∀ g ∈ groups, g.Checked)
    (cut : ∀ g ∈ groups, g.k = k)
    (distinct : (groups.map Group.signature).Nodup)
    (classified : ∀ g ∈ groups, PrefixClassified classify g)
    (count : n ≤ 12 * (groups.map Group.size).sum) :
    ∃ f : Fin n → Board, (∀ i, Valid (f i)) ∧ (∀ i j, f i = f j → i = j) :=
  prefix_orbit_lower_bound_of_nodup k groups classify n checked cut
    (groups_nodup k groups checked cut distinct) classified count

end TBoards.Splice
