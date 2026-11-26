module

public import SlabSearch.Shapes

/-! Exact coverage of unit cells implies the volume, face-area, and line-length identities. -/

@[expose] public section

namespace SevenSlabs

-- Add the values at cell coordinates 0,...,n-1.
def cellSum : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n+1, f => cellSum n f + f n

theorem cellSum_congr {n} {f g : Nat → Nat} (h : ∀ t < n, f t = g t) :
    cellSum n f = cellSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cellSum]
    rw [ih (fun t ht => h t (by omega)), h n (by omega)]

theorem cellSum_const (n c : Nat) : cellSum n (fun _ => c) = n*c := by
  induction n with
  | zero => simp [cellSum]
  | succ n ih => simp [cellSum, ih, Nat.succ_mul]

theorem cellSum_add (n : Nat) (f g : Nat → Nat) :
    cellSum n (fun i => f i + g i) = cellSum n f + cellSum n g := by
  induction n with
  | zero => simp [cellSum]
  | succ n ih => simp [cellSum, ih]; omega

theorem cellSum_mul_right (n c : Nat) (f : Nat → Nat) :
    cellSum n (fun i => f i * c) = cellSum n f * c := by
  induction n with
  | zero => simp [cellSum]
  | succ n ih => simp [cellSum, ih, Nat.add_mul]

theorem cellSum_mul_left (n c : Nat) (f : Nat → Nat) :
    cellSum n (fun i => c * f i) = c * cellSum n f := by
  simpa only [Nat.mul_comm c] using cellSum_mul_right n c f

theorem cellSum_list {α} (n : Nat) (bs : List α) (f : α → Nat → Nat) :
    cellSum n (fun i => (bs.map (fun b => f b i)).sum) =
      (bs.map (fun b => cellSum n (f b))).sum := by
  induction bs with
  | nil => simp [cellSum_const]
  | cons b bs ih => simp only [List.map_cons, List.sum_cons]; rw [cellSum_add, ih]

def hit (o d i : Nat) : Nat := if o ≤ i ∧ i < o+d then 1 else 0

theorem intervalCount (n o d : Nat) :
    cellSum n (hit o d) = min (n-o) d := by
  induction n with
  | zero => simp [cellSum]
  | succ n ih =>
    simp only [cellSum, ih, hit]
    split <;> omega

theorem fullIntervalCount {n o d : Nat} (h : o+d ≤ n) :
    cellSum n (hit o d) = d := by rw [intervalCount]; omega

def Axis.next : Axis → Axis | .x => .y | .y => .z | .z => .x

theorem area_next (d : Triple) (a : Axis) :
    d.area a = d.along a.next * d.along a.next.next := by cases a <;> rfl

def Box.hits (b : Box) (a : Axis) (i : Nat) : Bool :=
  decide (b.lo.along a ≤ i ∧ i < b.lo.along a + b.size.along a)

def Box.weight (b : Box) (a : Axis) (i : Nat) : Nat :=
  hit (b.lo.along a) (b.size.along a) i

theorem weight_eq (b : Box) (a : Axis) (i : Nat) :
    b.weight a i = if b.hits a i then 1 else 0 := by
  simp [Box.weight, hit, Box.hits]

/-- Each box has positive lengths, lies in the cube, and covers each unit cell
jointly with the other boxes exactly once. -/
structure Tiling (n : Nat) (bs : List Box) : Prop where
  pos : ∀ b ∈ bs, ∀ a, 0 < b.size.along a
  bound : ∀ b ∈ bs, ∀ a, b.lo.along a + b.size.along a ≤ n
  cover : ∀ x < n, ∀ y < n, ∀ z < n,
    (bs.map (fun b => b.weight .x x * b.weight .y y * b.weight .z z)).sum = 1

namespace Tiling
variable {n : Nat} {bs : List Box} (H : Tiling n bs)
include H

theorem rotated (a : Axis) {x y z : Nat} (hx : x < n) (hy : y < n) (hz : z < n) :
    (bs.map (fun b => b.weight a x * b.weight a.next y *
                      b.weight a.next.next z)).sum = 1 := by
  cases a with
  | x => exact H.cover x hx y hy z hz
  | y => simpa only [Axis.next, Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using
           H.cover z hz x hx y hy
  | z => simpa only [Axis.next, Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using
           H.cover y hy z hz x hx

theorem count_weight (b : Box) (hb : b ∈ bs) (a : Axis) :
    cellSum n (b.weight a) = b.size.along a := fullIntervalCount (H.bound b hb a)

theorem along_line_weight (a : Axis) {y z : Nat} (hy : y < n) (hz : z < n) :
    (bs.map (fun b => b.size.along a * b.weight a.next y *
                       b.weight a.next.next z)).sum = n := by
  let f := fun (b : Box) x => b.weight a x * b.weight a.next y * b.weight a.next.next z
  have h : cellSum n (fun x => (bs.map (fun b => f b x)).sum) = n := by
    rw [cellSum_congr (g := fun _ => 1) (fun x hx => H.rotated a hx hy hz), cellSum_const]
    simp
  rw [cellSum_list] at h
  refine Eq.trans (congrArg List.sum (List.map_congr_left ?_)) h
  intro b hb
  simp [f, cellSum_mul_right, H.count_weight b hb]

theorem section_weight (a : Axis) {x : Nat} (hx : x < n) :
    (bs.map (fun b => b.weight a x * b.size.area a)).sum = n*n := by
  let f := fun (b : Box) (y z : Nat) =>
    b.weight a x * b.weight a.next y * b.weight a.next.next z
  have inner (y : Nat) (hy : y < n) :
      (bs.map (fun b => b.weight a x * b.weight a.next y *
                 b.size.along a.next.next)).sum = n := by
    have h : cellSum n (fun z => (bs.map (fun b => f b y z)).sum) = n := by
      rw [cellSum_congr (g := fun _ => 1) (fun z hz => H.rotated a hx hy hz), cellSum_const]
      simp
    rw [cellSum_list] at h
    refine Eq.trans (congrArg List.sum (List.map_congr_left ?_)) h
    intro b hb
    simp [f, cellSum_mul_left, H.count_weight b hb]
  let g := fun (b : Box) y => b.weight a x * b.weight a.next y * b.size.along a.next.next
  have h : cellSum n (fun y => (bs.map (fun b => g b y)).sum) = n*n := by
    rw [cellSum_congr (g := fun _ => n) inner, cellSum_const]
  rw [cellSum_list] at h
  refine Eq.trans (congrArg List.sum (List.map_congr_left ?_)) h
  intro b hb
  simp [g, cellSum_mul_left, cellSum_mul_right, H.count_weight b hb, area_next, Nat.mul_assoc]

theorem volume :
    (bs.map (fun b => b.size.vol)).sum = n*n*n := by
  let f := fun (b : Box) x => b.weight .x x * b.size.area .x
  have h : cellSum n (fun x => (bs.map (fun b => f b x)).sum) = n*(n*n) := by
    rw [cellSum_congr (g := fun _ => n*n) (fun x hx => H.section_weight .x hx), cellSum_const]
  rw [cellSum_list, ← Nat.mul_assoc] at h
  refine Eq.trans (congrArg List.sum (List.map_congr_left ?_)) h
  intro b hb
  simp [f, cellSum_mul_right, H.count_weight b hb, Triple.area, Triple.along,
        Triple.vol, Nat.mul_assoc]

theorem sectionArea (a : Axis) {x : Nat} (hx : x < n) :
    (bs.map (fun b => if b.hits a x then b.size.area a else 0)).sum = n*n := by
  have h := H.section_weight a hx
  refine Eq.trans (congrArg List.sum (List.map_congr_left ?_)) h
  intro b _
  rw [weight_eq]
  split <;> simp_all

theorem line (a : Axis) {y z : Nat} (hy : y < n) (hz : z < n) :
    (bs.map (fun b => if b.hits a.next y && b.hits a.next.next z
              then b.size.along a else 0)).sum = n := by
  have h := H.along_line_weight a hy hz
  refine Eq.trans (congrArg List.sum (List.map_congr_left ?_)) h
  intro b _
  simp only [weight_eq]
  cases b.hits a.next y <;> cases b.hits a.next.next z <;> simp

theorem oppositeFaces (hn : 0 < n) (a : Axis) :
    ∃ L R : Box → Bool,
      (bs.map (fun b => if L b then b.size.area a else 0)).sum = n*n ∧
      (bs.map (fun b => if R b then b.size.area a else 0)).sum = n*n ∧
      ∀ b ∈ bs, (b.size.along a = n → L b = true ∧ R b = true) ∧
                (L b = true → R b = true → b.size.along a = n) := by
  refine ⟨fun b => b.hits a 0, fun b => b.hits a (n-1),
    H.sectionArea a hn, H.sectionArea a (by omega), ?_⟩
  intro b hb
  have bound := H.bound b hb a
  simp only [Box.hits, decide_eq_true_eq]
  omega

theorem lineThrough (a : Axis) (target : Box) (hm : target ∈ bs) :
    ∃ choose : Box → Bool, choose target = true ∧
      (bs.map (fun b => if choose b then b.size.along a else 0)).sum = n := by
  have hy := H.bound target hm a.next
  have hz := H.bound target hm a.next.next
  have dy := H.pos target hm a.next
  have dz := H.pos target hm a.next.next
  let y := target.lo.along a.next
  let z := target.lo.along a.next.next
  refine ⟨fun b => b.hits a.next y && b.hits a.next.next z, ?_,
    H.line a (y := y) (z := z) (by dsimp [y]; omega) (by dsimp [z]; omega)⟩
  simp [Box.hits, y, z, dy, dz]

end Tiling
end SevenSlabs
