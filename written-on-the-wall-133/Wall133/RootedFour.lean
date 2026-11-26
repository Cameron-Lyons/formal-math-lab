module

public import Wall133.OddSmallSix

@[expose] public section

namespace Wall133
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

private theorem castVertex {i j : ℕ} (e : i = j) (P : Chain G i) (a : ℕ) :
    (e ▸ P : Chain G j).vertex a = P.vertex a := by subst j; rfl

/-- Reverse the prefix up to a private contact at k. The old vertex k-2
becomes the endpoint and the suffix beginning at k is preserved. -/
private def rotateAt (P : Chain G n) (k : ℕ) (hk : 4 ≤ k) (hkn : k ≤ n)
    {x : V} (hx : G.Adj (P.vertex 0) x) (hxk : G.Adj (P.vertex k) x)
    (only : ∀ i ≤ n, i ≠ 0 → G.Adj (P.vertex i) x → i = k) : Chain G n where
  vertex i := if k ≤ i then P.vertex i else if i+1=k then x else P.vertex (k-2-i)
  inj := by
    have fresh (i) (hi : i ≤ n) : x ≠ P.vertex i := by
      intro e
      have h₁ := (P.edges (Nat.zero_le _) hi).1 (e ▸ hx)
      have h₂ := (P.edges hkn hi).1 (e ▸ hxk)
      omega
    intro i j hi hj
    split_ifs <;> intro e
    all_goals first
      | omega
      | exact (fresh _ (by omega) e).elim
      | exact (fresh _ (by omega) e.symm).elim
      | have := P.inj (by omega) (by omega) e; omega
  edges := by
    have toX (i) (hi : i ≤ n) : G.Adj (P.vertex i) x ↔ i=0 ∨ i=k := by
      constructor
      · intro ha; by_cases he : i=0
        · exact Or.inl he
        · exact Or.inr (only i hi he ha)
      · rintro (rfl|rfl) <;> assumption
    have fromX (i) (hi : i ≤ n) := (G.adj_comm x (P.vertex i)).trans (toX i hi)
    intro i j hi hj
    split_ifs <;> simp (disch := omega) only [P.edges,toX,fromX,SimpleGraph.irrefl,false_iff] <;> omega

variable [Fintype V] [DecidableRel G.Adj]

private theorem seedFour (T : Chain G 4) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    {d : ℕ} (hmin : ∀ x, d ≤ G.degree x) (j : ℕ) (hj : j+4 ≤ 2*d) :
    ∃ Q : Chain G (j+4), Q.vertex (j+4) = T.vertex 4 ∧ Q.vertex j = T.vertex 0 := by
  induction j with
  | zero => exact ⟨T,rfl,rfl⟩
  | succ j ih =>
    obtain ⟨Q,hv,hw⟩ := ih (by omega)
    classical
    let A := (G.neighborFinset (Q.vertex 0)).filter (Good Q)
    have h := good_card Q c h4 (by omega)
    change G.degree (Q.vertex 0) ≤ A.card+(j+4)/2 at h
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < A.card by have := hmin (Q.vertex 0); omega)
    exact ⟨grow Q x (Finset.mem_filter.mp hx).2,hv,hw⟩

private theorem rotate_saturated (P : Chain G n) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    {k : ℕ} (hk : 4 ≤ k) (hkn : k ≤ n) (he : k%2=0)
    (hd : n/2 ≤ G.degree (P.vertex 0)) (sat : ∀ z, ¬Good P z) :
    ∃ Q : Chain G n, Q.vertex n = P.vertex n ∧ Q.vertex 0 = P.vertex (k-2) ∧
      Q.vertex 1 = P.vertex (k-3) := by
  let j : Fin (n/2) := ⟨k/2-1,by omega⟩
  have hj : 2*j.val+2=k := by dsimp [j]; omega
  obtain ⟨x,hx,hxk,only⟩ := saturated_witness P c h4 (by omega) hd sat j
  rw [hj] at hxk only
  let Q := rotateAt P k hk hkn hx hxk only
  exact ⟨Q,by simp [Q,rotateAt,hkn], by simp [Q,rotateAt,show ¬k≤0 by omega,show 1≠k by omega],
    by simp [Q,rotateAt,show ¬k≤1 by omega,show 2≠k by omega,show k-2-1=k-3 by omega]⟩

/-- At a high endpoint of an even path, two clean neighbors either extend
twice or supply two detours that retain its far endpoint. -/
private theorem extendTwice (P : Chain G (2*n)) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    (hn : 4 ≤ n) (hmin : ∀ x, n ≤ G.degree x) (hd : n+2 ≤ G.degree (P.vertex 0)) :
    ∃ Q : Chain G (2*n+2), Q.vertex (2*n+2) = P.vertex (2*n) := by
  obtain ⟨x,y,hx,hy,hxy⟩ := two_good P c h4 (by omega) (by omega)
  have go {w z : V} (hw : Good P w) (hz : Good (grow P w hw) z) :
      ∃ Q : Chain G (2*n+2), Q.vertex (2*n+2) = P.vertex (2*n) :=
    ⟨grow (grow P w hw) z hz,rfl⟩
  by_cases sx : ∃ z, Good (grow P x hx) z
  · obtain ⟨z,hz⟩ := sx; exact go hx hz
  by_cases sy : ∃ z, Good (grow P y hy) z
  · obtain ⟨z,hz⟩ := sy; exact go hy hz
  obtain ⟨F,hF⟩ := doubleStallsWithEnd P c h4 (by omega) hx hy hxy
    (by have := hmin x; omega) (by have := hmin y; omega)
    (fun z hz => sx ⟨z,hz⟩) (fun z hz => sy ⟨z,hz⟩)
  exact ⟨tailChain F,hF⟩

/-- A four-edge seed with a high endpoint gives a rooted chain on 2d+2
edges in an asymmetric degree core, preserving the other end of the seed. -/
theorem rooted_chain_from_four (T : Chain G 4) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    {d : ℕ} (hd : 4 ≤ d) (hmin : ∀ x, d ≤ G.degree x) (col : Fin 2)
    (hside : ∀ x, c x = col → d+1 ≤ G.degree x) (hw : d+2 ≤ G.degree (T.vertex 0)) :
    ∃ Q : Chain G (2*d+2), Q.vertex (2*d+2) = T.vertex 4 := by
  obtain ⟨Q,hv',hw'⟩ := seedFour T c h4 hmin (2*d-4) (by omega)
  have el : 2*d-4+4=2*d := by omega
  let P : Chain G (2*d) := el ▸ Q
  have hv : P.vertex (2*d) = T.vertex 4 := by simpa [P,castVertex,el] using hv'
  have w : P.vertex (2*d-4) = T.vertex 0 := by simpa [P,castVertex,el] using hw'
  by_cases colRoot : c (T.vertex 4) = col
  · have hpcol : c (P.vertex 0) = col := by
      apply Fin.ext
      have he := P.color_val c (2*d) le_rfl
      rw [hv,colRoot] at he
      have := (c (P.vertex 0)).isLt
      omega
    -- One extension is forced; retain the original seed for the next rotation.
    classical
    let A := (G.neighborFinset (P.vertex 0)).filter (Good P)
    have hcount := good_card P c h4 (by omega)
    change G.degree (P.vertex 0) ≤ A.card+(2*d)/2 at hcount
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < A.card by have := hside _ hpcol; omega)
    let R := grow P x (Finset.mem_filter.mp hx).2
    by_cases ext : ∃ z, Good R z
    · obtain ⟨z,hz⟩ := ext
      exact ⟨grow R z hz,hv⟩
    obtain ⟨U,hU,_,hU1⟩ := rotate_saturated R c h4 (k := 2*d) (by omega) (by omega)
      (by omega) (by have := hmin (R.vertex 0); omega) (fun z hz => ext ⟨z,hz⟩)
    let F := tailChain U
    have hF : F.vertex 0 = T.vertex 0 := by
      change U.vertex 1 = _
      rw [hU1, show 2*d-3 = (2*d-4)+1 by omega]
      exact w
    obtain ⟨D,hD⟩ := extendTwice F c h4 hd hmin (by rw [hF]; exact hw)
    exact ⟨D,hD.trans (hU.trans hv)⟩
  · have make {R : Chain G (2*d+1)} (hR : R.vertex (2*d+1) = T.vertex 4) :
        ∃ Q : Chain G (2*d+2), Q.vertex (2*d+2) = T.vertex 4 := by
      have hcol : c (R.vertex 0) = col := by
        apply Fin.ext
        have he := R.color_val c (2*d+1) le_rfl
        rw [hR] at he
        have := Fin.val_ne_of_ne colRoot
        have := (c (R.vertex 0)).isLt
        have := (c (T.vertex 4)).isLt; have := col.isLt
        omega
      have hdeg := hside _ hcol
      obtain ⟨D,hD⟩ := R.extend c h4 (by omega) (by omega)
      exact ⟨D,hD.trans hR⟩
    by_cases ext : ∃ z, Good P z
    · obtain ⟨z,hz⟩ := ext
      exact make (R := grow P z hz) hv
    obtain ⟨U,hU,hu,_⟩ := rotate_saturated P c h4 (k := 2*d-2) (by omega) (by omega)
      (by omega) (by have := hmin (P.vertex 0); omega) (fun z hz => ext ⟨z,hz⟩)
    have hdU : d+2 ≤ G.degree (U.vertex 0) := by
      rw [hu,show 2*d-2-2=2*d-4 by omega,w]
      exact hw
    obtain ⟨D,hD⟩ := extendTwice U c h4 hd hmin hdU
    exact ⟨D,hD.trans (hU.trans hv)⟩

end Wall133
