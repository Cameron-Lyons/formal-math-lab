import Splice
import ColorSymmetry

namespace TBoards.Splice

private theorem cell_reverse {b : Board} (h : WellFormed b)
    {r j : Nat} (hr : r < 10) (hj : j < 2*r+1) :
    cell (b.map List.reverse) r j = cell b r (2*r-j) := by
  have hrow := h.2.1 r (List.mem_range.mpr hr)
  have hr' : r < b.length := h.1 ▸ hr
  have h1 : j < (b.getD r []).reverse.length := by rw [List.length_reverse, hrow]; exact hj
  have h2 : 2*r-j < (b.getD r []).length := by omega
  unfold cell
  rw [map_getD_in_bounds _ _ _ _ _ hr', ← List.getElem_eq_getD 0 (h := h1),
    ← List.getElem_eq_getD 0 (h := h2), List.getElem_reverse]
  congr 1
  omega

private theorem reverse_row_count {b : Board} (h : WellFormed b) (r : Nat) (hr : r < 9)
    (a l m u : Nat) :
    (((List.range (2*r+1)).map fun j => patternAt (b.map List.reverse) (r,j)).count (a,l,m,u)) =
    (((List.range (2*r+1)).map fun j => patternAt b (r,j)).count (a,u,m,l)) := by
  have rev : (List.range (2*r+1)).reverse = (List.range (2*r+1)).map (fun j => 2*r-j) := by
    simpa [List.range_eq_range'] using (List.reverse_range' (s := 0) (n := 2*r+1))
  simp only [List.count_eq_countP, List.countP_map]
  rw [← List.countP_reverse (l := List.range (2*r+1)) (p := ((fun x => x == (a,u,m,l)) ∘
    fun j => patternAt b (r,j))), rev, List.countP_map]
  apply List.countP_congr
  intro j hj
  have hj' := List.mem_range.mp hj
  simp only [Function.comp_apply, beq_iff_eq, patternAt, Prod.ext_iff]
  rw [cell_reverse h (by omega) (by omega), cell_reverse h (by omega) (by omega),
    cell_reverse h (by omega) (by omega), cell_reverse h (by omega) (by omega)]
  have e1 : 2*(r+1)-j = (2*r-j)+2 := by omega
  have e2 : 2*(r+1)-(j+1) = (2*r-j)+1 := by omega
  have e3 : 2*(r+1)-(j+2) = 2*r-j := by omega
  rw [e1, e2, e3]
  exact ⟨fun ⟨x,y,z,w⟩ => ⟨x,w,z,y⟩, fun ⟨x,y,z,w⟩ => ⟨x,w,z,y⟩⟩

/-- Horizontal reflection interchanges the left and right entries of each pattern. -/
theorem valid_reverse {b : Board} (h : Valid b) : Valid (b.map List.reverse) := by
  constructor
  · refine ⟨by simpa using h.1.1, ?_, ?_⟩
    · intro r hr
      have hb : r < b.length := h.1.1 ▸ List.mem_range.mp hr
      rw [map_getD_in_bounds _ _ _ _ _ hb, List.length_reverse]
      exact h.1.2.1 r hr
    · intro row hr c hc
      obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hr
      exact h.1.2.2 r hr' c (by simpa using hc)
  · intro a l m u
    have target := h.2 a u m l
    simp only [patterns, placements, List.map_flatMap, List.map_map, List.count_flatMap,
      List.map_flatMap, Function.comp_def] at target ⊢
    apply Eq.trans ?_ target
    apply congrArg List.sum
    apply List.map_congr_left
    intro r hr
    exact reverse_row_count h.1 r (List.mem_range.mp hr) _ _ _ _

abbrev Action := List Nat × Bool

def actions : List Action :=
  colorPermutations.flatMap fun p => [(p, false), (p, true)]

private theorem action_mem {op : Action} (hop : op ∈ actions) : op.1 ∈ colorPermutations := by
  obtain ⟨p, hp, h⟩ := List.mem_flatMap.mp hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> exact hp

def actRow (op : Action) (row : List Nat) : List Nat :=
  (if op.2 then row.reverse else row).map (fun c => op.1.getD c 0)

private theorem act_valid {op : Action} (hop : op ∈ actions) {b : Board} (hb : Valid b) :
    Valid (b.map (actRow op)) := by
  obtain ⟨p, r⟩ := op
  have hp := action_mem hop
  cases r with
  | false => exact valid_transform_colors hb p hp
  | true =>
    change Valid (b.map (fun row => row.reverse.map (fun c => p.getD c 0)))
    simpa [transform, List.map_map, Function.comp_def, ← List.map_reverse] using valid_transform_colors (valid_reverse hb) p hp

private theorem undo {p q : List Nat} (reflect : Bool) (hb : WellFormed b)
    (h : PaletteInverse p q) : (b.map (actRow (p,reflect))).map (actRow (q,reflect)) = b := by
  rw [List.map_map]
  apply Eq.trans ?_ (List.map_id b)
  apply List.map_congr_left
  intro row hr
  have he : row.map (fun c => q.getD (p.getD c 0) 0) = row := by
    apply Eq.trans ?_ (List.map_id row)
    exact List.map_congr_left fun c hc => h.2.2.1 ⟨c, hb.2.2 _ hr _ hc⟩
  cases reflect <;> simpa [actRow, List.map_map, Function.comp_def, ← List.map_reverse] using he

private theorem act_inj {op : Action} (hop : op ∈ actions) {a b : Board} (ha : Valid a)
    (hb : Valid b) (he : a.map (actRow op) = b.map (actRow op)) : a = b := by
  obtain ⟨q, _, hq⟩ := colorPermutations_have_inverse op.1 (action_mem hop)
  have h := congrArg (List.map (actRow (q,op.2))) he
  exact (undo op.2 ha.1 hq).symm.trans (h.trans (undo op.2 hb.1 hq))

/-- Padding the pivot with the apex on both sides commutes with reflection. -/
def marker (apex pivot : List Nat) := apex ++ pivot ++ apex

private theorem act_marker (op : Action) (apex pivot : List Nat) :
    marker (actRow op apex) (actRow op pivot) = actRow op (marker apex pivot) := by
  rcases op with ⟨p, r⟩
  cases r <;> simp [marker, actRow, List.reverse_append, List.append_assoc]

/-- Different actions must have disjoint sets of transformed markers. -/
def Separated (markers : List (List Nat)) : Prop :=
  actions.Pairwise (fun op op' => ∀ r ∈ markers, ∀ s ∈ markers, actRow op r ≠ actRow op' s)

instance (markers : List (List Nat)) : Decidable (Separated markers) := by
  unfold Separated
  infer_instance

private def readMarker (k : Nat) (b : Board) :=
  marker ((b.drop 0).headD []) ((b.drop k).headD [])

def Covers (g : Group) (markers : List (List Nat)) : Prop :=
  ∀ cap ∈ g.caps, marker ((cap ++ [g.pivot]).headD []) g.pivot ∈ markers

instance (g : Group) (markers : List (List Nat)) : Decidable (Covers g markers) := by
  unfold Covers
  infer_instance

private theorem marker_mem {k : Nat} {groups : List Group} {markers : List (List Nat)}
    (checked : ∀ g ∈ groups, g.Checked)
    (cut : ∀ g ∈ groups, g.k = k) (covers : ∀ g ∈ groups, Covers g markers)
    {b : Board} (hb : b ∈ groups.flatMap Group.boards) : readMarker k b ∈ markers := by
  obtain ⟨g, hg, hgb⟩ := List.mem_flatMap.mp hb
  obtain ⟨cap, hcap, hbs⟩ := List.mem_flatMap.mp hgb
  obtain ⟨tail, _, rfl⟩ := List.mem_map.mp hbs
  unfold readMarker
  rw [List.drop_left' ((g.cap_length (checked g hg) hcap).trans (cut g hg))]
  have hh : (cap ++ g.pivot :: tail).headD [] = (cap ++ [g.pivot]).headD [] := by
    cases cap <;> rfl
  simpa only [List.drop_zero, List.headD_cons, hh] using covers g hg cap hcap

private theorem read_act (op : Action) (b : Board) (k : Nat) :
    ((b.map (actRow op)).drop k).headD [] = actRow op ((b.drop k).headD []) := by
  rw [← List.map_drop]
  have he : actRow op [] = [] := by simp [actRow]
  simpa only [he] using List.headD_map (f := actRow op) (l := b.drop k) (a := [])

private theorem read_marker_act (op : Action) (b : Board) (k : Nat) :
    readMarker k (b.map (actRow op)) = actRow op (readMarker k b) := by
  unfold readMarker
  rw [read_act, read_act, act_marker]

/-- Symmetry amplification checks the apex and pivot markers once. Both the splice products and
their twelve labeled images are counted algebraically. -/
theorem orbit_lower_bound (k : Nat) (groups : List Group) (markers : List (List Nat)) (n : Nat)
    (checked : ∀ g ∈ groups, g.Checked)
    (cut : ∀ g ∈ groups, g.k = k)
    (distinct : (groups.map Group.signature).Nodup)
    (covers : ∀ g ∈ groups, Covers g markers)
    (sep : Separated markers)
    (count : n ≤ 12 * (groups.map Group.size).sum) :
    ∃ f : Fin n → Board, (∀ i, Valid (f i)) ∧ (∀ i j, f i = f j → i = j) := by
  let bs := groups.flatMap Group.boards
  let image := fun op : Action => bs.map (List.map (actRow op))
  apply injective_family_of_list (actions.flatMap image) n
  · have hlen : actions.length = 12 := by decide
    rw [List.length_flatMap]
    change n ≤ (actions.map (fun op => (bs.map (List.map (actRow op))).length)).sum
    simp only [List.length_map, List.map_const', List.sum_replicate_nat, hlen]
    simpa only [bs, List.length_flatMap, Group.boards_length] using count
  · apply List.pairwise_flatMap.mpr
    constructor
    · intro op hop
      apply List.pairwise_map.mpr
      apply (groups_nodup k groups checked cut distinct).imp_of_mem
      intro a b ha hb hab he
      exact hab (act_inj hop (groups_valid checked a ha) (groups_valid checked b hb) he)
    · apply sep.imp
      intro op op' hne x hx y hy he
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
      have hem := congrArg (readMarker k) he
      change readMarker k (a.map (actRow op)) = readMarker k (b.map (actRow op')) at hem
      rw [read_marker_act, read_marker_act] at hem
      exact hne _ (marker_mem checked cut covers ha) _ (marker_mem checked cut covers hb) hem
  · intro b hb
    obtain ⟨op, hop, hm⟩ := List.mem_flatMap.mp hb
    obtain ⟨base, hbase, rfl⟩ := List.mem_map.mp hm
    exact act_valid hop (groups_valid checked base hbase)

end TBoards.Splice
