import ThreeStacks.Contraction
import ThreeStacks.Dual
import ThreeStacks.Join
import ThreeStacks.Normalize
import ThreeStacks.Saved

namespace ThreeStacks

/-- Evidence for one deck. Each constructor describes a sound method used
    by the computation. Positive claims about layouts require actual runs. -/
inductive DeckCertificate : Nat → List Nat → Prop where
  | word {n p} (moves : List Nat) :
      checkRun moves p [] [] [] (target n) = true → DeckCertificate n p
  | split {n p} : HasSplitCertificate n p → DeckCertificate n p
  | dual {n p} : IsDeck n p → DeckCertificate n (ThreeStacks.dual n p) → DeckCertificate n p
  | pair {n p k} : 1 ≤ k → k ≤ n → DeckCertificate n p →
      DeckCertificate (n+1) (p.flatMap (descendingPair k))
  | saved {p moves} : (p, moves) ∈ residual19 → DeckCertificate 19 p

theorem DeckCertificate.sound {n p} (h : DeckCertificate n p) : Sortable n p := by
  induction h with
  | word _ checked => exact (run_iff_sortsTo _ _).mp (checkRun_sound checked)
  | split cut => exact splitCertificate_sorts cut
  | dual deck _ ih => exact dual_sorts deck ih
  | pair lo hi _ ih => exact sortable_expand_descending_pair ih lo hi
  | saved entry => exact residual19_sorts entry

/-- The external coverage obligation. Lean checks the individually saved
    words separately. The C++ enumeration accounts for this remaining set. -/
def Bulk19Coverage : Prop :=
  ∀ p, IsDeck 19 p → p.getLast? = some 1 →
    (¬ ∃ ms, (p, ms) ∈ residual19) → DeckCertificate 19 p

theorem all19_of_bulk (bulk : Bulk19Coverage) : ∀ p, IsDeck 19 p → Sortable 19 p := by
  apply allFromEndingOne 18
  intro p deck last
  by_cases saved : ∃ ms, (p, ms) ∈ residual19
  · obtain ⟨_, entry⟩ := saved
    exact residual19_sorts entry
  · exact (bulk p deck last saved).sound

end ThreeStacks
