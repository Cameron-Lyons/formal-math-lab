import ColorSymmetry
import EfficientCheck
import SortedFamily

namespace TBoards

/-- The validity proof travels with each concrete board. -/
abbrev CertifiedBoard := {b : Board // Valid b}

def renameCertified (b : CertifiedBoard) (p : Fin 6) : CertifiedBoard :=
  ⟨transform b.val (colorPermutations[p.val]'(by exact p.isLt)) false,
   valid_transform_colors b.property _ (List.getElem_mem (by exact p.isLt))⟩

def certifiedValues (bs : List CertifiedBoard) : List Board := bs.map Subtype.val

theorem certifiedValues_valid (bs : List CertifiedBoard) :
    ∀ b ∈ certifiedValues bs, Valid b := by
  intro b hb
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
  exact c.property

theorem certified_lower_bound (bs : List CertifiedBoard) (n : Nat)
    (hlen : n ≤ (certifiedValues bs).length)
    (hsorted : increasing ((certifiedValues bs).map boardCode) = true) :
    ∃ f : Fin n → Board, (∀ i, Valid (f i)) ∧
      (∀ i j, f i = f j → i = j) :=
  injective_family_of_list _ n hlen (nodup_of_increasing_codes hsorted)
    (certifiedValues_valid bs)

/-- Small blocks keep each numeric-fingerprint computation bounded. -/
structure CodeBlock where
  boards : List CertifiedBoard
  codes : List Nat
  correct : (certifiedValues boards).map boardCode = codes

theorem codeBlocks_correct (blocks : List CodeBlock) :
    (certifiedValues (blocks.flatMap CodeBlock.boards)).map boardCode =
      blocks.flatMap CodeBlock.codes := by
  induction blocks with
  | nil => rfl
  | cons b bs ih =>
    change (((b.boards ++ bs.flatMap CodeBlock.boards).map Subtype.val).map boardCode) =
      b.codes ++ bs.flatMap CodeBlock.codes
    rw [List.map_append, List.map_append]
    exact (congrArg (fun xs => xs ++ (certifiedValues (bs.flatMap CodeBlock.boards)).map boardCode) b.correct).trans
      (congrArg (fun xs => b.codes ++ xs) ih)

theorem codeBlocks_lower_bound (blocks : List CodeBlock) (n : Nat)
    (hlen : n ≤ (blocks.flatMap CodeBlock.codes).length)
    (hsorted : increasing (blocks.flatMap CodeBlock.codes) = true) :
    ∃ f : Fin n → Board, (∀ i, Valid (f i)) ∧
      (∀ i j, f i = f j → i = j) := by
  have hl : (certifiedValues (blocks.flatMap CodeBlock.boards)).length =
      (blocks.flatMap CodeBlock.codes).length := by
    have hc := congrArg List.length (codeBlocks_correct blocks)
    simpa only [List.length_map] using hc
  apply certified_lower_bound (blocks.flatMap CodeBlock.boards) n
  · rw [hl]
    exact hlen
  · rw [codeBlocks_correct]
    exact hsorted

end TBoards
