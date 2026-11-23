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

private theorem maximum_mem (x : List Bool) (l : List (List Bool)) :
    ∃ v ∈ x :: l, ∀ w ∈ x :: l, w ≤ v := by
  induction l generalizing x with
  | nil => exact ⟨x, by simp, by simp⟩
  | cons y ys ih =>
    obtain ⟨v, hv, hm⟩ := ih y
    rcases List.le_total x v with hx | hx
    · refine ⟨v, by simp [hv], ?_⟩
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hx
      · exact hm w hw
    · refine ⟨x, by simp, ?_⟩
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact Std.le_refl _
      · exact List.le_trans (hm w hw) hx

/-- All Boolean words of a fixed length. Used only in the existence proof for a maximum. -/
private def words : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (words n).map (false :: ·) ++ (words n).map (true :: ·)

private theorem mem_words (xs : List Bool) : xs ∈ words xs.length := by
  induction xs with
  | nil => simp [words]
  | cons b bs ih => cases b <;> simp [words, ih]

theorem exists_max_key {α : Type} (P : α → Prop) (f : α → List Bool) (n : Nat)
    (lengths : ∀ a, (f a).length = n) (start : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → f b ≤ f a := by
  classical
  let L := (words n).filter fun v => decide (∃ a, P a ∧ f a = v)
  have memL (a : α) (ha : P a) : f a ∈ L := by
    have hw := mem_words (f a)
    rw [lengths] at hw
    exact List.mem_filter.mpr ⟨hw, decide_eq_true ⟨a,ha,rfl⟩⟩
  obtain ⟨a₀,ha₀⟩ := start
  obtain ⟨v,hv,hm⟩ := maximum_mem (f a₀) L
  have ev : ∃ a, P a ∧ f a = v := by
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨a₀,ha₀,rfl⟩
    · exact of_decide_eq_true (List.mem_filter.mp hv).2
  obtain ⟨a,ha,rfl⟩ := ev
  exact ⟨a,ha,fun b hb => hm _ (List.mem_cons_of_mem _ (memL b hb))⟩

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
