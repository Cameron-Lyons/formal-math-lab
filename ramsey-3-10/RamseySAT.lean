import RamseyNumber

namespace Ramsey310.SAT

/-- One Boolean variable for each unordered pair of distinct vertices. -/
structure EdgeVar where
  lo : Fin 40
  hi : Fin 40
  increasing : lo < hi

/-- Each increasing triple indexes a clause of three negative literals.
    Each increasing ten-element list indexes a clause of 45 positive literals. -/
def Satisfies (assign : EdgeVar → Bool) : Prop :=
  (∀ a b c (ab : a < b) (bc : b < c),
    assign ⟨a, b, ab⟩ = false ∨ assign ⟨b, c, bc⟩ = false ∨
      assign ⟨a, c, Fin.lt_trans ab bc⟩ = false) ∧
  ∀ s : List (Fin 40), s.length = 10 → s.Pairwise (· < ·) →
    ∃ p : EdgeVar, p.lo ∈ s ∧ p.hi ∈ s ∧ assign p = true

private def decode (assign : EdgeVar → Bool) (x y : Fin 40) : Bool :=
  if xy : x < y then assign ⟨x, y, xy⟩
  else if yx : y < x then assign ⟨y, x, yx⟩ else false

private theorem decode_simple (assign : EdgeVar → Bool) : Simple (decode assign) := by
  grind [Simple, decode, Fin.lt_def]

private theorem clauses_iff (e : Fin 40 → Fin 40 → Bool) (hs : Simple e) :
    Satisfies (fun p => e p.lo p.hi) ↔
      TriangleFree e ∧ ¬∃ s, Independent e s ∧ 10 ≤ orderOf s := by
  obtain ⟨loopless, symm⟩ := hs
  unfold Satisfies
  apply and_congr
  · simp only [TriangleFree]
    grind [Fin.lt_def]
  · constructor
    · rintro tens ⟨s, indep, size⟩
      -- Take the first ten selected vertices in increasing order.
      let vs := (List.finRange 40).filter s
      have len : 10 ≤ vs.length := size
      have sorted := ((List.pairwise_lt_finRange 40).filter s).take (i := 10)
      obtain ⟨p, hlo, hhi, edge⟩ := tens (vs.take 10) (by simp [len]) sorted
      have inside (v) (hv : v ∈ vs.take 10) : s v = true :=
        (List.mem_filter.mp (List.mem_of_mem_take hv)).2
      exact Bool.eq_false_iff.mp (indep _ _ (inside _ hlo) (inside _ hhi)) edge
    · intro bound s size sorted
      apply Classical.byContradiction
      intro missing
      -- A ten-set whose clause fails is itself independent.
      have noEdge (a b : Fin 40) (ab : a < b) (ha : a ∈ s) (hb : b ∈ s) : e a b = false :=
        Bool.eq_false_iff.mpr (fun h => missing ⟨⟨a, b, ab⟩, ha, hb, h⟩)
      apply bound
      refine ⟨s.contains, ?_, ?_⟩
      · unfold Independent
        simp only [List.contains_iff_mem]
        grind [Fin.lt_def]
      · rw [← size]
        apply List.Nodup.length_le_of_subset (sorted.imp Fin.ne_of_lt)
        exact fun v hv => List.mem_filter.mpr ⟨List.mem_finRange v, List.contains_iff_mem.mpr hv⟩

/-- Satisfiability of the unrestricted edge CNF is exactly failure of the
    ordinary Ramsey property on 40 vertices. -/
theorem satisfiable_iff : (∃ assign, Satisfies assign) ↔ ¬RamseyProperty 40 := by
  constructor
  · rintro ⟨assign, passes⟩ ramsey
    have same : (fun p : EdgeVar => decode assign p.lo p.hi) = assign := by
      funext p; simp [decode, p.increasing]
    rw [← same] at passes
    obtain ⟨free, bound⟩ := (clauses_iff _ (decode_simple assign)).mp passes
    exact bound (ramsey _ (decode_simple assign) free)
  · intro h
    simp only [RamseyProperty, Classical.not_forall] at h
    obtain ⟨e, hs, free, bound⟩ := h
    exact ⟨_, (clauses_iff _ hs).mpr ⟨free, bound⟩⟩

/-- An unsatisfiability proof for the unrestricted formula would settle the value at 40. -/
theorem value40_iff_unsat : IsRamseyNumber 40 ↔ ¬∃ assign, Satisfies assign := by
  rw [forty_iff, satisfiable_iff]
  exact Classical.not_not.symm

/-- With the published upper bound, a satisfying assignment would settle the value at 41. -/
theorem value41_iff_sat (upper : RamseyProperty 41) :
    IsRamseyNumber 41 ↔ ∃ assign, Satisfies assign :=
  (fortyOne_iff upper).trans satisfiable_iff.symm

end Ramsey310.SAT
