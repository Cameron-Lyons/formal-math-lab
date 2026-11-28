module

public import SlabSearch.Shapes

/-! Enumeration of shape lists with the required volume, with a completeness proof. -/

@[expose] public section

namespace SevenSlabs

instance (n order : Nat) (s : Shape) : Decidable (Shape.Valid n order s) := by
  unfold Shape.Valid
  infer_instance

/-- All sorted slabs of this order small enough to fit in the cube. -/
def shapeChoices (n order : Nat) : List Shape :=
  let lengths := List.range (n + 1)
  (lengths.flatMap (fun a => lengths.map fun b => (⟨order, a, b⟩ : Shape))).filter
    (fun s => decide (Shape.Valid n order s))

theorem mem_shapeChoices {n k : Nat} {s : Shape} (h : Shape.Valid n k s) :
    s ∈ shapeChoices n k := by
  rcases s with ⟨j,a,b⟩
  change j = k ∧ 0 < k ∧ j ≤ a ∧ a ≤ b ∧ b ≤ n ∧ j ∣ a ∧ j ∣ b at h
  obtain ⟨rfl, hpos, hja, hab, hbn, hda, hdb⟩ := h
  apply List.mem_filter.mpr
  refine ⟨List.mem_flatMap.mpr ⟨a, List.mem_range.mpr (by omega), ?_⟩, ?_⟩
  · exact List.mem_map.mpr ⟨b, List.mem_range.mpr (by omega), rfl⟩
  · exact decide_eq_true ⟨rfl, hpos, hja, hab, hbn, hda, hdb⟩

def rowMax : List Shape → Nat
  | [] => 0
  | s :: ss => max s.vol (rowMax ss)

private theorem le_rowMax {row : List Shape} {s : Shape} (h : s ∈ row) :
    s.vol ≤ rowMax row := by
  induction row with
  | nil => simp at h
  | cons t ts ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- The upper bound is precomputed once per remaining suffix of orders. -/
structure VolumeSearch where
  upper : Nat
  atVolume : Nat → List (List Shape)

def buildSearch : List (List Shape) → VolumeSearch
  | [] => ⟨0, fun rem => if rem = 0 then [[]] else []⟩
  | row :: rows =>
    let tail := buildSearch rows
    let upper := rowMax row + tail.upper
    ⟨upper, fun rem => if rem ≤ upper then
      row.flatMap fun s => if s.vol ≤ rem then
        (tail.atVolume (rem - s.vol)).map (s :: ·)
        else []
      else []⟩

private def fitsRows : List (List Shape) → List Shape → Prop
  | [], [] => True
  | row :: rows, s :: ss => s ∈ row ∧ fitsRows rows ss
  | _, _ => False

private theorem buildSearch_complete {rows : List (List Shape)} {ss : List Shape}
    (h : fitsRows rows ss) :
    (ss.map Shape.vol).sum ≤ (buildSearch rows).upper ∧
    ss ∈ (buildSearch rows).atVolume (ss.map Shape.vol).sum := by
  induction rows generalizing ss with
  | nil =>
    cases ss with
    | nil => simp [buildSearch]
    | cons => contradiction
  | cons row rows ih =>
    cases ss with
    | nil => contradiction
    | cons s ss =>
      obtain ⟨hs, hrest⟩ := h
      obtain ⟨hle, hm⟩ := ih hrest
      have hbound := Nat.add_le_add (le_rowMax hs) hle
      refine ⟨hbound, ?_⟩
      simp only [buildSearch, List.map_cons, List.sum_cons, ite_eq_left hbound]
      apply List.mem_flatMap.mpr
      refine ⟨s, hs, ?_⟩
      simp only [Nat.le_add_right, ↓reduceIte, Nat.add_sub_cancel_left]
      exact List.mem_map_of_mem hm

/-- Work from largest order to smallest to prune early. Output is in increasing order. -/
def volumeShapes (n : Nat) : List (List Shape) :=
  let rows := [7,6,5,4,3,2,1].map (shapeChoices n)
  ((buildSearch rows).atVolume (n ^ 3)).map List.reverse

theorem mem_volumeShapes {n : Nat} {s1 s2 s3 s4 s5 s6 s7 : Shape}
    (h1 : Shape.Valid n 1 s1) (h2 : Shape.Valid n 2 s2)
    (h3 : Shape.Valid n 3 s3) (h4 : Shape.Valid n 4 s4)
    (h5 : Shape.Valid n 5 s5) (h6 : Shape.Valid n 6 s6) (h7 : Shape.Valid n 7 s7)
    (hvol : ([s1,s2,s3,s4,s5,s6,s7].map Shape.vol).sum = n ^ 3) :
    [s1,s2,s3,s4,s5,s6,s7] ∈ volumeShapes n := by
  let rows := [7,6,5,4,3,2,1].map (shapeChoices n)
  let desc := [s7,s6,s5,s4,s3,s2,s1]
  have hfits : fitsRows rows desc :=
    ⟨mem_shapeChoices h7, mem_shapeChoices h6, mem_shapeChoices h5, mem_shapeChoices h4,
      mem_shapeChoices h3, mem_shapeChoices h2, mem_shapeChoices h1, trivial⟩
  have hr : (desc.map Shape.vol).sum = n ^ 3 := by
    simp only [desc, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hvol ⊢
    omega
  have hm := (buildSearch_complete hfits).2
  rw [hr] at hm
  exact List.mem_map.mpr ⟨desc, hm, rfl⟩

private theorem split_legal {n k : Nat} {ks : List Nat} {ss : List Shape}
    (h : LegalShapes n (k :: ks) ss) :
    ∃ s tail, ss = s :: tail ∧ s.Valid n k ∧ LegalShapes n ks tail := by
  cases ss with
  | nil => contradiction
  | cons s tail => exact ⟨s, tail, rfl, h⟩

theorem mem_volumeShapes_of_legal {n : Nat} {ss : List Shape}
    (h : LegalShapes n [1,2,3,4,5,6,7] ss) (v : (ss.map Shape.vol).sum = n ^ 3) :
    ss ∈ volumeShapes n := by
  obtain ⟨s1, _, rfl, h1, h⟩ := split_legal h
  obtain ⟨s2, _, rfl, h2, h⟩ := split_legal h
  obtain ⟨s3, _, rfl, h3, h⟩ := split_legal h
  obtain ⟨s4, _, rfl, h4, h⟩ := split_legal h
  obtain ⟨s5, _, rfl, h5, h⟩ := split_legal h
  obtain ⟨s6, _, rfl, h6, h⟩ := split_legal h
  obtain ⟨s7, tail, rfl, h7, h⟩ := split_legal h
  cases tail with
  | nil => exact mem_volumeShapes h1 h2 h3 h4 h5 h6 h7 v
  | cons => contradiction

/-- Lift a successful Boolean test over the entire enumeration to every candidate. -/
theorem all_volumeShapes {test : Nat → List Shape → Bool}
    (checked : (List.range 29).all (fun n => (volumeShapes n).all (test n)) = true)
    {n : Nat} (hn : n ≤ 28) {ss : List Shape} (hs : ss ∈ volumeShapes n) :
    test n ss = true :=
  List.all_eq_true.mp (List.all_eq_true.mp checked n (List.mem_range.mpr (by omega))) ss hs

end SevenSlabs
