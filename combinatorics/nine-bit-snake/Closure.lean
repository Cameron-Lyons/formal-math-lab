import Results
import EndProfiles

namespace Snake

/-- In a snake, each step changes one coordinate. A used coordinate is
therefore identified by the first vertex where it differs from its initial bit. -/
private def firstChange (path : List Vertex) (i : Fin 9) : Nat :=
  let initial := (path.headD 0).getLsbD i
  path.findIdx fun v => v.getLsbD i != initial

/-- Verify that the proposed coordinate map is injective and reproduces every column. -/
private def signedMatch (src dst : List Vertex) : Bool :=
  let starts := Vector.ofFn (firstChange src)
  let perm := Vector.ofFn fun j =>
    let start := firstChange dst j
    ((List.finRange 9).find? fun i => starts[i] == start).getD 0
  let flip (j : Fin 9) := (dst.headD 0).getLsbD j != (src.headD 0).getLsbD perm[j]
  decide ((∀ i j : Fin 9, perm[i] = perm[j] → i = j) ∧ ∀ j : Fin 9,
    column dst j = if flip j then (column src perm[j]).map Bool.not else column src perm[j])

private theorem signedMatch_sound {src dst : List Vertex}
    (h : signedMatch src dst = true) : SignedPermutation src dst := by
  obtain ⟨hinj, hcols⟩ := of_decide_eq_true h
  exact ⟨_, hinj, _, hcols⟩

private def publishedOrientations : List (List Vertex × List Vertex) := bank.map fun w =>
  let path := vertices w
  (path, path.reverse)

private def recognized (vs : List Vertex) : Bool :=
  publishedOrientations.any (fun (a, b) => signedMatch a vs || signedMatch b vs)

/-- A concrete equality after a signed coordinate permutation of a published
path, with either orientation allowed. -/
def InCollection (vs : List Vertex) : Prop :=
  ∃ w ∈ bank, SignedPermutation (vertices w) vs ∨ SignedPermutation (vertices w).reverse vs

private theorem recognized_sound {vs : List Vertex} (h : recognized vs = true) : InCollection vs := by
  obtain ⟨pair, hp, hm⟩ := List.any_eq_true.mp h
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hp
  refine ⟨w, hw, ?_⟩
  simp only [Bool.or_eq_true] at hm
  exact hm.imp signedMatch_sound signedMatch_sound

private theorem all_finishes_recognized : ∀ row ∈ bank, ∀ backwards : Bool,
    allContinuations (bankPrefix row backwards) 35 recognized = true := by native_decide

/-- Every way to finish an oriented 156-step prefix from the published bank to
191 steps gives an image of a published snake under the allowed symmetries. -/
theorem bank_no_new_191 (row : List Nat) (mem : row ∈ bank) (backwards : Bool)
    (tail : List Vertex) (len : tail.length = 35)
    (valid : IsSnake (bankPrefix row backwards ++ tail)) :
    InCollection (bankPrefix row backwards ++ tail) :=
  recognized_sound (allContinuations_sound (all_finishes_recognized row mem backwards) len valid)

/-- Taking a prefix preserves every required distance between the retained vertices. -/
theorem IsSnake.takePrefix {path : List Vertex} (h : IsSnake path) (n : Nat) :
    IsSnake (path.take n) := by
  match path, n with
  | [], _ => simp [IsSnake]
  | _ :: _, 0 | _ :: _, 1 | [_], _ + 2 => trivial
  | x :: y :: ys, k + 2 =>
    obtain ⟨adjacent, separated, tail⟩ := h
    exact ⟨adjacent, fun z hz => separated z (List.mem_of_mem_take hz),
      IsSnake.takePrefix (path := y :: ys) tail (k + 1)⟩

/-- Some 193 vertices of the nine-cube form an induced path in the given order. -/
def Has192StepSnake : Prop :=
  ∃ p : List Vertex, p.length = 193 ∧ IsSnake p

/-- A Hamming isometry aligns an entire path with one orientation of a bank entry.
In particular this allows coordinate permutations and coordinate flips. -/
def AlignsWithBank (p : List Vertex) : Prop :=
  ∃ w ∈ bank, ∃ backwards : Bool, ∃ f : Vertex → Vertex,
    (∀ x y, hamming (f x) (f y) = hamming x y) ∧
    p.map f = orientedPath w backwards

/-- The 191-step prefix of any 192-step witness would already give a solution
to the second challenge, even allowing all Hamming isometries. -/
theorem new_prefix_of_192 {p : List Vertex} (len : p.length = 193) (valid : IsSnake p) :
    (p.take 192).length = 192 ∧ IsSnake (p.take 192) ∧ ¬ AlignsWithBank (p.take 192) := by
  refine ⟨by simp [len], valid.takePrefix 192, ?_⟩
  rintro ⟨row, mem, backwards, f, isometry, same191⟩
  -- An alignment for 191 steps also aligns the 171-step prefix checked by the kernel.
  have sameStart : (p.map f).take 172 = (orientedPath row backwards).take 172 := by
    simpa [List.take_take] using congrArg (List.take 172) same191
  apply bank_no_192_kernel row mem backwards ((p.map f).drop 172) (by simp [len])
  rw [← sameStart, List.take_append_drop]
  exact valid.map f isometry

theorem new_191_of_192 (h : Has192StepSnake) :
    ∃ p : List Vertex, p.length = 192 ∧ IsSnake p ∧ ¬ AlignsWithBank p := by
  obtain ⟨p, len, valid⟩ := h
  exact ⟨p.take 192, new_prefix_of_192 len valid⟩

/-- Any path whose first and last 17 steps give the same sequence of distances
from the respective endpoint is inequivalent to every published record. -/
theorem outside_bank_of_end_profiles {p : List Vertex}
    (agree : endProfile p = endProfile p.reverse) : ¬ AlignsWithBank p := by
  rintro ⟨w, hw, b, f, hf, align⟩
  have hne := bank_end_profiles_differ w hw
  have heq : endProfile (p.map f) = endProfile (p.map f).reverse := by
    simpa only [← List.map_reverse, endProfile_map f hf] using agree
  rw [align] at heq
  cases b with
  | false => exact hne heq
  | true => exact hne (by simpa [orientedPath] using heq.symm)

end Snake
