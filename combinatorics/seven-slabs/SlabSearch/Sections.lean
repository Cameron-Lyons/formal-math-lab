module

public import SlabSearch.Shapes

/-! Necessary area and length tests on the faces and coordinate lines of a cube. -/

@[expose] public section

namespace SevenSlabs

/-- Shapes and placed boxes in corresponding order. -/
inductive Matches : List Shape → List Box → Prop where
  | nil : Matches [] []
  | cons {s b ss bs} : b.size ∈ s.orientations → Matches ss bs → Matches (s::ss) (b::bs)

def FaceWitnesses (n : Nat) (bs : List Box) : Prop :=
  ∀ a : Axis, ∃ L R : Box → Bool,
    (bs.map (fun b => if L b then b.size.area a else 0)).sum = n*n ∧
    (bs.map (fun b => if R b then b.size.area a else 0)).sum = n*n ∧
    ∀ b ∈ bs, (b.size.along a = n → L b = true ∧ R b = true) ∧
              (L b = true → R b = true → b.size.along a = n)

def LineWitnesses (n : Nat) (bs : List Box) : Prop :=
  ∀ (a : Axis) (t : Box), t ∈ bs → ∃ L : Box → Bool, L t = true ∧
    (bs.map (fun b => if L b then b.size.along a else 0)).sum = n

/-- Along one axis a box contributes its length and its transverse area. -/
abbrev SectionRow := Nat × Nat

def rowOf (a : Axis) (b : Box) : SectionRow := (b.size.along a, b.size.area a)

def rowOptions (s : Shape) : List SectionRow :=
  [(s.k, s.a*s.b), (s.a, s.b*s.k), (s.b, s.k*s.a)].eraseDups

def profiles : List Shape → List (List SectionRow)
  | [] => [[]]
  | s::ss =>
    let tails := profiles ss
    (rowOptions s).flatMap (fun r => tails.map (r :: ·))

theorem row_mem_options {s : Shape} {b : Box} (h : b.size ∈ s.orientations) (a : Axis) :
    rowOf a b ∈ rowOptions s := by
  simp only [Shape.orientations, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h|h|h|h|h|h <;> cases a <;>
    simp [rowOf, rowOptions, h, Triple.along, Triple.area, Nat.mul_comm]

theorem mem_profiles {ss bs} (h : Matches ss bs) (a : Axis) :
    bs.map (rowOf a) ∈ profiles ss := by
  induction h with
  | nil => simp [profiles]
  | cons h _ ih =>
    exact List.mem_flatMap.mpr ⟨_, row_mem_options h a, List.mem_map.mpr ⟨_, ih, rfl⟩⟩

/-- Can the two opposite faces receive the requested areas from these rows?
Full-length boxes contribute on both faces and shorter boxes on at most one. -/
def faceFit (n : Nat) : List SectionRow → Nat → Nat → Bool
  | [], l, r => l == 0 && r == 0
  | (w,v)::rs, l, r =>
    if w = n then
      v ≤ l && v ≤ r && faceFit n rs (l-v) (r-v)
    else
      faceFit n rs l r ||
      (v ≤ l && faceFit n rs (l-v) r) ||
      (v ≤ r && faceFit n rs l (r-v))

/-- Can a line use the requested total length and contain some box of width w? -/
def lineFit (w : Nat) : List SectionRow → Nat → Bool → Bool
  | [], t, hit => t == 0 && hit
  | (d,_)::rs, t, hit =>
    (d ≤ t && lineFit w rs (t-d) (hit || d == w)) || lineFit w rs t hit

def axisFits (n : Nat) (rs : List SectionRow) : Bool :=
  rs.all (fun r => lineFit r.1 rs n false) && faceFit n rs (n*n) (n*n)

private def areaSum (a : Axis) (bs : List Box) (L : Box → Bool) :=
  (bs.map (fun b => if L b then b.size.area a else 0)).sum

private def lengthSum (a : Axis) (bs : List Box) (L : Box → Bool) :=
  (bs.map (fun b => if L b then b.size.along a else 0)).sum

private theorem faceFit_of_masks (n : Nat) (a : Axis) (L R : Box → Bool) (bs : List Box)
    (h : ∀ b ∈ bs, (b.size.along a = n → L b = true ∧ R b = true) ∧
                    (L b = true → R b = true → b.size.along a = n)) :
    faceFit n (bs.map (rowOf a)) (areaSum a bs L) (areaSum a bs R) = true := by
  induction bs with
  | nil => simp [faceFit, areaSum]
  | cons b bs ih =>
    have head := h b (by simp)
    have tail := ih (fun c hc => h c (by simp [hc]))
    change faceFit n (bs.map (rowOf a)) _ _ = true at tail
    by_cases full : b.size.along a = n
    · have ⟨hl,hr⟩ := head.1 full
      simpa [rowOf, faceFit, areaSum, full, hl, hr] using tail
    · cases hl : L b <;> cases hr : R b
      · simp [rowOf, faceFit, areaSum, full, hl, hr, areaSum] at tail ⊢
        simp [tail]
      · simp [rowOf, faceFit, areaSum, full, hl, hr] at tail ⊢
        exact Or.inr tail
      · simp [rowOf, faceFit, areaSum, full, hl, hr] at tail ⊢
        exact Or.inl (Or.inr tail)
      · exact (full (head.2 hl hr)).elim

private theorem lineFit_of_mask (a : Axis) (L : Box → Bool) (w : Nat) (bs : List Box)
    (hit : Bool) (h : hit = true ∨ ∃ b ∈ bs, L b = true ∧ b.size.along a = w) :
    lineFit w (bs.map (rowOf a)) (lengthSum a bs L) hit = true := by
  induction bs generalizing hit with
  | nil => simpa [lineFit, lengthSum] using h
  | cons b bs ih =>
    cases hb : L b with
    | false =>
      have tail := ih hit (by simpa [hb] using h)
      simp [rowOf, lengthSum, lineFit, hb] at tail ⊢
      exact Or.inr tail
    | true =>
      have hh : (hit || (b.size.along a == w)) = true ∨
                ∃ c ∈ bs, L c = true ∧ c.size.along a = w := by
        simpa [hb, or_assoc] using h
      have tail := ih _ hh
      simp [rowOf, lengthSum, lineFit, hb] at tail ⊢
      exact Or.inl tail

private theorem axisFits_of_witnesses {n bs} (hf : FaceWitnesses n bs)
    (hl : LineWitnesses n bs) (a : Axis) : axisFits n (bs.map (rowOf a)) = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply List.all_eq_true.mpr
    intro r hr
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hr
    obtain ⟨L,hL,hs⟩ := hl a b hb
    have hh := lineFit_of_mask a L (b.size.along a) bs false (.inr ⟨b,hb,hL,rfl⟩)
    simpa [lengthSum, hs, rowOf] using hh
  · obtain ⟨L,R,hL,hR,h⟩ := hf a
    simpa [areaSum, hL, hR] using faceFit_of_masks n a L R bs h

def compatible : List Shape → List SectionRow → List SectionRow → List SectionRow → Bool
  | [], [], [], [] => true
  | s::ss, x::xs, y::ys, z::zs =>
    (s.orientations.any fun d => decide (d = ⟨x.1,y.1,z.1⟩)) && compatible ss xs ys zs
  | _, _, _, _ => false

private theorem compatible_of_matches {ss bs} (h : Matches ss bs) :
    compatible ss (bs.map (rowOf .x)) (bs.map (rowOf .y)) (bs.map (rowOf .z)) = true := by
  induction h with
  | nil => rfl
  | cons h _ ih => simpa [compatible, rowOf, Triple.along, ih] using h

def checkShapes (n : Nat) (ss : List Shape) : Bool :=
  let good := (profiles ss).filter (axisFits n)
  good.any fun x => good.any fun y => good.any fun z => compatible ss x y z

theorem checkShapes_of_boxes {n ss bs} (h : Matches ss bs) (hf : FaceWitnesses n bs)
    (hl : LineWitnesses n bs) : checkShapes n ss = true := by
  have good (a : Axis) : bs.map (rowOf a) ∈ (profiles ss).filter (axisFits n) :=
    List.mem_filter.mpr ⟨mem_profiles h a, axisFits_of_witnesses hf hl a⟩
  apply List.any_eq_true.mpr
  exact ⟨_, good .x, List.any_eq_true.mpr ⟨_, good .y,
    List.any_eq_true.mpr ⟨_, good .z, compatible_of_matches h⟩⟩⟩

end SevenSlabs
