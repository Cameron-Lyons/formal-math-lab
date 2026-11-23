import Ramsey556.TwoVertexFrame
import Ramsey556.OneBipartite

namespace Ramsey556

/-- If the two exterior types contain no two disjoint cross edges, deleting
a single exterior vertex removes all their red cross edges. -/
private theorem outer_star {c : Coloring 33} (S : SupportedOctets c) (big : Fin 2)
    (noMatch : ¬ Nonempty (OuterMatching S big)) :
    ∃ z : Fin 17, ∀ i j, S.tag i = big → S.tag j ≠ big →
      c.edge (S.outer i) (S.outer j) = 0 → i = z ∨ j = z := by
  let red (i j : Fin 17) := S.tag i = big ∧ S.tag j ≠ big ∧ c.edge (S.outer i) (S.outer j) = 0
  have meet {a b x y} (h₁ : red a b) (h₂ : red x y) (left : a ≠ x) : b = y := by
    apply Classical.byContradiction
    intro right
    apply noMatch
    let l (t : Fin 2) := if t = 0 then a else x
    let r (t : Fin 2) := if t = 0 then b else y
    have one (t : Fin 2) : red (l t) (r t) := by
      by_cases e : t = 0 <;> simp only [l, r, e, ↓reduceIte] <;> assumption
    exact ⟨⟨l, r, fun t => (one t).1, fun t => (one t).2.1,
      by simpa [l] using left, by simpa [r] using right, fun t => (one t).2.2⟩⟩
  by_cases any : ∃ a b, red a b
  · obtain ⟨a,b,e⟩ := any
    by_cases second : ∃ x y, red x y ∧ x ≠ a
    · obtain ⟨x,y,f,sep⟩ := second
      have same := meet f e sep
      subst y
      refine ⟨b, fun i j hi hj edge => Or.inr ?_⟩
      have ij : red i j := ⟨hi,hj,edge⟩
      by_cases eq : i = a
      · exact meet ij f (eq ▸ sep.symm)
      · exact meet ij e eq
    · exact ⟨a, fun i j hi hj edge => Or.inl (Classical.byContradiction
        (fun ne => second ⟨i,j,⟨hi,hj,edge⟩,ne⟩))⟩
  · exact ⟨0, fun i j hi hj edge => (any ⟨i,j,hi,hj,edge⟩).elim⟩

private def skipOuter (z : Fin 17) (i : Fin 16) : Fin 17 :=
  ⟨if i.val < z.val then i.val else i.val+1, by split <;> omega⟩

private theorem skipOuter_spec : ∀ z : Fin 17, (∀ i : Fin 16, skipOuter z i ≠ z) ∧
    ∀ i j : Fin 16, skipOuter z i = skipOuter z j → i = j := by decide

/-- The anchors and any sixteen exterior vertices make an induced K₃₂.
A red bipartition on these vertices suffices by the one-deletion theorem. -/
private theorem finish_with_cut {c : Coloring 33} (classify : TwoColorOctets16)
    (S : SupportedOctets c) (w : Fin 16 → Fin 17) (wi : ∀ ⦃i j⦄, w i = w j → i = j)
    (left : Fin 2 → Fin 8 → Bool) (right : Fin 17 → Bool)
    (cross : ∀ s i j, c.edge (S.anchor s i) (S.outer (w j)) = 0 → left s i ≠ right (w j))
    (exterior : ∀ i j, i ≠ j → c.edge (S.outer (w i)) (S.outer (w j)) = 0 →
      right (w i) ≠ right (w j)) : HasMonoC9 c := by
  let block (i : Fin 16) : Fin 2 := ⟨i.val / 8, by omega⟩
  let slot (i : Fin 16) : Fin 8 := ⟨i.val % 8, by omega⟩
  let anchor (i : Fin 16) := S.anchor (block i) (slot i)
  have pair {i j : Fin 16} (a : block i = block j) (b : slot i = slot j) : i = j := by
    have ha := congrArg Fin.val a
    have hb := congrArg Fin.val b
    dsimp [block, slot] at ha hb
    exact Fin.ext (by omega)
  let v : Fin (16+16) → Fin 33 := Fin.addCases anchor (fun i => S.outer (w i))
  have inj : ∀ ⦃i j⦄, v i = v j → i = j := by
    intro i j h
    induction i using Fin.addCases (m := 16) (n := 16) <;> induction j using Fin.addCases (m := 16) (n := 16) <;>
      simp only [v, Fin.addCases_left, Fin.addCases_right] at h
    · exact congrArg (Fin.castAdd 16) (pair (S.anchorInj h).1 (S.anchorInj h).2)
    · exact (S.disjoint _ _ _ h).elim
    · exact (S.disjoint _ _ _ h.symm).elim
    · exact congrArg (Fin.natAdd 16) (wi (S.outerInj h))
  apply hasMonoC9_of_one_bipartite_on_32 classify c v inj 0
  let side : Fin (16+16) → Bool :=
    Fin.addCases (fun i => left (block i) (slot i)) (fun j => right (w j))
  refine ⟨side, ?_⟩
  intro i j hd e
  induction i using Fin.addCases (m := 16) (n := 16) <;> induction j using Fin.addCases (m := 16) (n := 16) <;>
    simp only [Coloring.induce, v, Fin.addCases_left, Fin.addCases_right] at e <;>
    simp only [side, Fin.addCases_left, Fin.addCases_right]
  · rename_i i j
    exact (S.independent _ _ _ _ (fun p => hd (congrArg (Fin.castAdd 16)
      (pair (congrArg Prod.fst p) (congrArg Prod.snd p)))) e).elim
  · exact cross _ _ _ e
  · exact (cross _ _ _ ((c.symm _ _).trans e)).symm
  · exact exterior _ _ (fun eq => hd (congrArg (Fin.natAdd 16) eq)) e

/-- For two independent exterior types, a red matching forces each anchor
to see at most one type, so it can be assigned the opposite side. Without
a red matching one exterior deletion makes all exterior vertices independent. -/
theorem finish_two_independent_types {c : Coloring 33} (classify : TwoColorOctets16)
    (S : SupportedOctets c) (big : Fin 2)
    (inner : ∀ i j, i ≠ j → S.tag i = S.tag j → c.edge (S.outer i) (S.outer j) ≠ 0)
    (noMix : OuterMatching S big → ∀ s a i j, S.tag i = big → S.tag j ≠ big →
      c.edge (S.anchor s a) (S.outer i) = 0 → c.edge (S.anchor s a) (S.outer j) ≠ 0) :
    HasMonoC9 c := by
  classical
  have tags {i j} (neq : S.tag i ≠ S.tag j) : S.tag i = big ∨ S.tag j = big := by
    have two : ∀ a b t : Fin 2, a ≠ b → a=t ∨ b=t := by decide
    exact two _ _ _ neq
  by_cases matching : Nonempty (OuterMatching S big)
  · obtain ⟨M⟩ := matching
    let hit (s a) := ∃ i, S.tag i = big ∧ c.edge (S.anchor s a) (S.outer i) = 0
    apply finish_with_cut classify S Fin.castSucc (fun {_ _} h => Fin.castSucc_inj.mp h)
      (fun s a => decide (hit s a)) (fun i => decide (S.tag i ≠ big))
    · intro s a j e
      by_cases hj : S.tag j.castSucc = big
      · simp [hj, show hit s a from ⟨j.castSucc,hj,e⟩]
      · have clear : ¬ hit s a := by
          rintro ⟨i, hi, edge⟩
          exact noMix M s a i _ hi hj edge e
        simp [hj, clear]
    · intro i j ne e
      have diff := fun h => inner i.castSucc j.castSucc (fun eq => ne (Fin.castSucc_inj.mp eq)) h e
      rcases tags diff with h | h
      · have nj : S.tag j.castSucc ≠ big := fun eq => diff (h.trans eq.symm)
        simp [h, nj]
      · have ni : S.tag i.castSucc ≠ big := fun eq => diff (eq.trans h.symm)
        simp [h, ni]
  · obtain ⟨z, star⟩ := outer_star S big matching
    apply finish_with_cut classify S (skipOuter z) (fun {_ _} => (skipOuter_spec z).2 _ _)
      (fun _ _ => true) (fun _ => false) (fun _ _ _ _ => by decide)
    intro i j ne e
    let p := skipOuter z i
    let q := skipOuter z j
    have pq : p ≠ q := fun h => ne ((skipOuter_spec z).2 _ _ h)
    have diff : S.tag p ≠ S.tag q := fun eq => inner p q pq eq e
    have hp : p ≠ z := (skipOuter_spec z).1 _
    have hq : q ≠ z := (skipOuter_spec z).1 _
    rcases tags diff with h | h
    · rcases star p q h (fun he => diff (h.trans he.symm)) e with h' | h'
      · exact (hp h').elim
      · exact (hq h').elim
    · rcases star q p h (fun he => diff (he.trans h.symm)) ((c.symm _ _).trans e) with h' | h'
      · exact (hq h').elim
      · exact (hp h').elim

end Ramsey556
