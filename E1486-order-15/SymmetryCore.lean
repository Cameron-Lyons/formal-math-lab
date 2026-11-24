import LabelMoves

namespace E1486
namespace Symmetry
open Encoding

local instance : Std.IsLinearOrder Bool where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  le_total := by decide

local instance : Std.LawfulOrderLT Bool where
  lt_iff := by decide

def sv (k : Nat) := verts.filter fun v => v.val < k

def matrix (k : Nat) (r : V → V → Bool) : List Bool :=
  (sv k).flatMap fun x => (sv k).map fun y => r x y

def profile (k : Nat) (r : V → V → Bool) (a : V) : List Bool :=
  (sv k).map (r · a) ++ (sv k).map (r a)

def score (k : Nat) (r : V → V → Bool) : List Bool :=
  matrix k r ++ verts.flatMap (profile k r)

private theorem matrix_length (k : Nat) (r s : V → V → Bool) :
    (matrix k r).length = (matrix k s).length := by
  simp [matrix,List.length_flatMap]

theorem project_left {x y u v : List Bool} (hlen : x.length = y.length)
    (h : x ++ u ≤ y ++ v) : x ≤ y := by
  rcases (List.append_le_append_iff_of_length_eq hlen).mp h with hlt | ⟨rfl,_⟩
  · exact Std.le_of_lt hlt
  · exact Std.le_refl _

theorem matrix_le {k : Nat} {r s : V → V → Bool} (h : score k r ≤ score k s) :
    matrix k r ≤ matrix k s :=
  project_left (matrix_length ..) h

private theorem mem_before (a : V) :
    ∃ t, verts = verts.takeWhile (· < a) ++ a :: t := by
  refine ⟨verts.drop (a.val+1), ?_⟩
  revert a
  decide

theorem swapped_profile_le {k : Nat} {r s : V → V → Bool} {a : V}
    (h : score k r ≤ score k s) (hm : matrix k r = matrix k s)
    (hp : ∀ b : V, b < a → profile k r b = profile k s b) :
    profile k r a ≤ profile k s a := by
  unfold score at h
  rw [hm] at h
  have hs := (List.append_left_le_iff _).mp h
  obtain ⟨t,ht⟩ := mem_before a
  rw [ht] at hs
  simp only [List.flatMap_append, List.flatMap_cons] at hs
  have he : (verts.takeWhile (· < a)).flatMap (profile k r) =
      (verts.takeWhile (· < a)).flatMap (profile k s) := by
    simp only [List.flatMap_def]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro b hb
    have hall : ∀ a b : V, b ∈ verts.takeWhile (· < a) → b < a := by decide
    exact hp b (hall a b hb)
  rw [he] at hs
  apply project_left _ ((List.append_left_le_iff _).mp hs)
  simp [profile]

end Symmetry
end E1486
