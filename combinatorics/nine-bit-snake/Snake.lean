import Std

namespace Snake

abbrev Vertex := BitVec 9

/-- Bit 0 is the least significant bit. An out-of-range step leaves the
    vertex fixed, which the snake check rejects. -/
def vertices (steps : List Nat) : List Vertex :=
  steps.scanl (fun v d => v ^^^ ((1 : Vertex) <<< d)) 0

/-- XOR has a 1 in exactly the coordinates where its operands differ. -/
def hamming (v w : Vertex) : Nat := (v ^^^ w).cpop.toNat

/-- At each vertex, its successor has distance one and all later vertices
    have distance at least two. The same obligations hold along the suffix. -/
def ValidFrom : Vertex → List Vertex → Prop
  | _, [] => True
  | x, y :: ys => hamming x y = 1 ∧ (∀ z ∈ ys, 2 ≤ hamming x z) ∧ ValidFrom y ys

def IsSnake : List Vertex → Prop
  | [] => True
  | x :: xs => ValidFrom x xs

private def units : List Vertex := [1, 2, 4, 8, 16, 32, 64, 128, 256]

def neighbors (x : Vertex) : List Vertex := units.map (x ^^^ ·)

section
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private theorem weight_one : ∀ d : Vertex, d.cpop.toNat = 1 ↔ d ∈ units := by decide +kernel

private theorem weight_zero : ∀ d : Vertex, d.cpop.toNat = 0 ↔ d = 0 := by decide +kernel

end

private theorem hamming_zero {x y : Vertex} : hamming x y = 0 ↔ x = y :=
  (weight_zero (x ^^^ y)).trans BitVec.xor_eq_zero_iff

private theorem xor_cancel (x y : Vertex) : x ^^^ (x ^^^ y) = y := by
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem mem_neighbors {x y : Vertex} : y ∈ neighbors x ↔ hamming x y = 1 := by
  rw [neighbors, List.mem_map, hamming, weight_one]
  constructor
  · rintro ⟨_, hd, rfl⟩
    simpa only [xor_cancel] using hd
  · intro hd
    exact ⟨x ^^^ y, hd, xor_cancel x y⟩

abbrev Mask := BitVec 512

def blocked (mask : Mask) (x : Vertex) : Bool := mask.getLsbD x.toNat

/-- A packed bitmap of the vertex and all nine of its one-bit neighbors.
    Compute the shifts on naturals and convert to a bit vector only once. -/
private def closedMask (x : Vertex) : Mask :=
  let n := x.toNat
  BitVec.ofNat 512 (
    (1 <<< n) ||| (1 <<< (n ^^^ 1)) ||| (1 <<< (n ^^^ 2)) |||
    (1 <<< (n ^^^ 4)) ||| (1 <<< (n ^^^ 8)) ||| (1 <<< (n ^^^ 16)) |||
    (1 <<< (n ^^^ 32)) ||| (1 <<< (n ^^^ 64)) ||| (1 <<< (n ^^^ 128)) |||
    (1 <<< (n ^^^ 256)))


def markClosed (mask : Mask) (x : Vertex) : Mask := mask ||| closedMask x

private theorem blocked_closedMask (x z : Vertex) :
    blocked (closedMask x) z = true ↔ z = x ∨ z ∈ neighbors x := by
  simp only [blocked, closedMask, BitVec.getLsbD_ofNat, z.isLt, decide_true, Bool.true_and,
    Nat.testBit_or, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow, Bool.or_eq_true,
    decide_eq_true_eq, or_assoc]
  simp [neighbors, units, ← BitVec.toNat_inj, eq_comm]

theorem unblocked_mark (mask : Mask) (x z : Vertex) :
    blocked (markClosed mask x) z = false ↔ blocked mask z = false ∧ 2 ≤ hamming x z := by
  have near := blocked_closedMask x z
  rw [mem_neighbors, eq_comm (a := z), ← hamming_zero] at near
  have far : blocked (closedMask x) z = false ↔ 2 ≤ hamming x z := by
    rw [← Bool.not_eq_true, near]
    omega
  simp only [markClosed, blocked, BitVec.getLsbD_or, Bool.or_eq_false_iff]
  exact and_congr_right (fun _ => far)

private def checkFrom (mask : Mask) (x : Vertex) : List Vertex → Bool
  | [] => true
  | y :: ys => !blocked mask y && (x ^^^ y ∈ units) && checkFrom (markClosed mask x) y ys

private theorem checkFrom_spec (mask : Mask) (x : Vertex) (ys : List Vertex) :
    checkFrom mask x ys = true ↔ ValidFrom x ys ∧ ∀ z ∈ ys, blocked mask z = false := by
  induction ys generalizing mask x with
  | nil => simp [checkFrom, ValidFrom]
  | cons y ys ih =>
    have hu : (x ^^^ y ∈ units) ↔ hamming x y = 1 := (weight_one (x ^^^ y)).symm
    simp only [checkFrom, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      hu, ih, unblocked_mark, ValidFrom, List.forall_mem_cons]
    grind

def isSnake : List Vertex → Bool
  | [] => true
  | x :: xs => checkFrom 0 x xs

theorem isSnake_iff {vs : List Vertex} : isSnake vs = true ↔ IsSnake vs := by
  cases vs with
  | nil => simp [IsSnake, isSnake]
  | cons x xs =>
    simp [isSnake, IsSnake, checkFrom_spec, blocked]

theorem isSnake_sound {vs : List Vertex} (h : isSnake vs = true) : IsSnake vs :=
  isSnake_iff.mp h

theorem IsSnake.nodup {vs : List Vertex} (h : IsSnake vs) : vs.Nodup := by
  induction vs with
  | nil => simp
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y ys =>
      obtain ⟨adjacent, far, rest⟩ := h
      apply List.nodup_cons.mpr
      refine ⟨?_, ih rest⟩
      intro hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simp [hamming, BitVec.cpop_zero] at adjacent
      · simpa [hamming, BitVec.cpop_zero] using far x hx

/-- The recursive definition gives the Hamming-distance condition at any
    two explicit indices in increasing order. -/
theorem IsSnake.pair {vs : List Vertex} (h : IsSnake vs)
    (i j : Nat) (hij : i < j) (hj : j < vs.length) :
    if j = i + 1 then hamming vs[i] vs[j] = 1 else 2 ≤ hamming vs[i] vs[j] := by
  induction vs generalizing i j with
  | nil => simp at hj
  | cons x xs ih =>
    cases xs with
    | nil => simp at hj; omega
    | cons y ys =>
      obtain ⟨adjacent, far, rest⟩ := h
      match i, j with
      | _, 0 => omega
      | 0, 1 => exact adjacent
      | 0, j+2 =>
        have hj' : j < ys.length := by simpa using hj
        simpa using far ys[j] (List.getElem_mem hj')
      | i+1, j+1 => simpa using ih rest i j (by omega) (by simpa using hj)

/-- Check a predicate at all reachable leaves. The callback receives the suffix
in path order. Only vertices strictly before the current endpoint are marked. -/
private def everyLeaf (mask : Mask) (x : Vertex) (k : Nat) (accept : List Vertex → Bool) : Bool :=
  match k with
  | 0 => accept []
  | n + 1 =>
    let nextMask := markClosed mask x
    (neighbors x).all fun y =>
      blocked mask y || everyLeaf nextMask y n (fun tail => accept (y :: tail))

private theorem everyLeaf_sound {mask : Mask} {x : Vertex} {ys : List Vertex}
    {accept : List Vertex → Bool} (h : everyLeaf mask x ys.length accept = true)
    (valid : ValidFrom x ys) (free : ∀ z ∈ ys, blocked mask z = false) : accept ys = true := by
  induction ys generalizing mask x accept with
  | nil => exact h
  | cons y ys ih =>
    obtain ⟨adj, dist, rest⟩ := valid
    have branch := List.all_eq_true.mp h y (mem_neighbors.mpr adj)
    simp only [free y (by simp), Bool.false_or] at branch
    apply ih branch rest
    intro z hz
    exact (unblocked_mark _ _ _).mpr ⟨free z (by simp [hz]), dist z hz⟩

private def afterPrefix (k : Nat) (accept : List Vertex → Bool) (mask : Mask)
    (x : Vertex) : List Vertex → Bool
  | [] => everyLeaf mask x k accept
  | y :: ys => afterPrefix k accept (markClosed mask x) y ys

private theorem afterPrefix_sound {k : Nat} {accept : List Vertex → Bool} {mask : Mask}
    {x : Vertex} {xs tail : List Vertex} (h : afterPrefix k accept mask x xs = true)
    (valid : ValidFrom x (xs ++ tail)) (len : tail.length = k)
    (free : ∀ z ∈ tail, blocked mask z = false) : accept tail = true := by
  induction xs generalizing mask x with
  | nil =>
    subst k
    exact everyLeaf_sound h valid free
  | cons y ys ih =>
    obtain ⟨_, dist, rest⟩ := valid
    apply ih h rest
    intro z hz
    exact (unblocked_mark _ _ _).mpr ⟨free z hz, dist z (List.mem_append_right _ hz)⟩

/-- Check each full path obtained by adding `k` vertices to the prefix. The empty prefix
has no endpoint from which to start the search, so the check returns false. -/
def allContinuations (vs : List Vertex) (k : Nat) (accept : List Vertex → Bool) : Bool :=
  match vs with
  | [] => false
  | x :: xs => afterPrefix k (fun tail => accept (vs ++ tail)) 0 x xs

theorem allContinuations_sound {vs tail : List Vertex} {k : Nat} {accept : List Vertex → Bool}
    (h : allContinuations vs k accept = true) (len : tail.length = k)
    (valid : IsSnake (vs ++ tail)) : accept (vs ++ tail) = true := by
  cases vs with
  | nil => simp [allContinuations] at h
  | cons x xs =>
    exact afterPrefix_sound (accept := fun rest => accept ((x :: xs) ++ rest))
      h valid len (by simp [blocked])

/-- Search for a suffix of length `k`. The search succeeds if some branch
reaches depth `k`. An empty prefix conservatively returns true. -/
def canExtend (vs : List Vertex) (k : Nat) : Bool :=
  !allContinuations vs k (fun _ => false)

theorem no_extension {vs : List Vertex} {k : Nat} (h : canExtend vs k = false)
    (tail : List Vertex) (len : tail.length = k) : ¬ IsSnake (vs ++ tail) := by
  simp only [canExtend, Bool.not_eq_false'] at h
  intro valid
  exact Bool.false_ne_true (allContinuations_sound h len valid)

/-- The values of one coordinate down the entire path, in path order. -/
def column (vs : List Vertex) (i : Fin 9) : List Bool :=
  vs.map (fun v => v.getLsbD i.val)

/-- A signed coordinate permutation from `vs` to `ws`. An injective map of
    nine coordinates to themselves is a permutation. Each output coordinate
    picks one input coordinate and optionally complements it at every vertex. -/
def SignedPermutation (vs ws : List Vertex) : Prop :=
  ∃ perm : Fin 9 → Fin 9, (∀ i j, perm i = perm j → i = j) ∧
    ∃ flips : Fin 9 → Bool, ∀ j,
      column ws j = if flips j then (column vs (perm j)).map Bool.not
                    else column vs (perm j)

/-- Equivalent transition sequences give paths identified by a signed
    coordinate permutation, with either orientation allowed. -/
def Equivalent (p q : List Nat) : Prop :=
  SignedPermutation (vertices q) (vertices p) ∨
  SignedPermutation (vertices q).reverse (vertices p)

private def columns (vs : List Vertex) : List (List Bool) :=
  (List.finRange 9).map (column vs)

private def couldMatch (outCols inCols : List (List Bool)) : Bool :=
  outCols.all fun a => inCols.any fun b => a == b || a == b.map Bool.not

private theorem match_of_signed {vs ws : List Vertex} (h : SignedPermutation vs ws) :
    couldMatch (columns ws) (columns vs) = true := by
  obtain ⟨perm, _, flips, hf⟩ := h
  apply List.all_eq_true.mpr
  intro a ha
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
  apply List.any_eq_true.mpr
  refine ⟨column vs (perm j), List.mem_map.mpr ⟨perm j, by simp, rfl⟩, ?_⟩
  cases he : flips j <;> simp [hf j, he]

private theorem columns_reverse (vs : List Vertex) :
    columns vs.reverse = (columns vs).map List.reverse := by
  simp [columns, column, List.map_map, Function.comp_def]

/-- A mismatch in even one coordinate column, allowing complements, rules out
    the given orientation. Check both orientations against every supplied path. -/
def fresh (p : List Nat) (db : List (List Nat)) : Bool :=
  let a := columns (vertices p)
  db.all fun q =>
    let b := columns (vertices q)
    !(couldMatch a b || couldMatch a (b.map List.reverse))

theorem fresh_sound {p : List Nat} {db : List (List Nat)} (h : fresh p db = true) :
    ∀ q ∈ db, ¬ Equivalent p q := by
  intro q hq he
  have hno := List.all_eq_true.mp h q hq
  change (!(couldMatch (columns (vertices p)) (columns (vertices q)) ||
            couldMatch (columns (vertices p)) ((columns (vertices q)).map List.reverse))) = true at hno
  cases he with
  | inl hfor => simp [match_of_signed hfor] at hno
  | inr hrev =>
    have hm := match_of_signed hrev
    rw [columns_reverse] at hm
    simp [hm] at hno

end Snake
