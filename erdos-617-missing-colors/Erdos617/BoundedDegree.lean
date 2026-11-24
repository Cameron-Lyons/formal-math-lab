import Erdos617.ColorGraph
import Erdos617.CliqueBoundary

namespace Erdos617

open SimpleGraph

/-- No outside vertex has two neighbors in an r-clique. -/
private def ExteriorUnique {V : Type*} (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ C : Finset V, G.IsNClique r C →
    ∀ x ∉ C, ∀ y ∈ C, ∀ z ∈ C, G.Adj x y → G.Adj x z → y = z

private theorem exteriorUnique_induce {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (h : ExteriorUnique G r) (U : Set V) : ExteriorUnique (G.induce U) r := by
  intro C hC x hx y hy z hz hxy hxz
  let incl := Function.Embedding.subtype (· ∈ U)
  have hC' := (G.isNClique_induce_iff U C r).mp hC
  apply Subtype.ext
  apply h (C.map incl) hC' x.val _ y.val (Finset.mem_map_of_mem incl hy)
    z.val (Finset.mem_map_of_mem incl hz) hxy hxz
  rintro hmem
  obtain ⟨a, ha, he⟩ := Finset.mem_map.mp hmem
  exact hx ((Subtype.ext he : a = x) ▸ ha)

/-- At each step remove an r-clique, find an independent set in the remaining
graph, and try to extend it through the clique. At the last step both sets
have size r and counting edges rules out the case in which every independent set
of that size blocks the entire clique. -/
private theorem independent_on_blocks (r : ℕ) (hr : 3 ≤ r) (t : ℕ) (ht : t ≤ r)
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = t * r + 1)
    (hT : (∑ x, (G.degree x - r)) < r)
    (hTop : (∑ x, (G.degree x - r)) < (r-1)*(r-2))
    (hout : ExteriorUnique G r) : ∃ S, G.IsNIndepSet (t + 1) S := by
  classical
  induction t generalizing V with
  | zero =>
    obtain ⟨x⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card V by simp [hV])
    exact ⟨{x}, by simp [isNIndepSet_iff, IsIndepSet]⟩
  | succ t ih =>
    by_contra! hi
    obtain ⟨C, hC⟩ := clique_of_total_excess_lt r (t+1) hr G hV hT hi
    let U : Set V := ↑(Cᶜ : Finset V)
    let H := G.induce U
    have hU : Fintype.card U = t * r + 1 := by
      change Fintype.card (Cᶜ : Finset V) = _
      rw [Fintype.card_coe, Finset.card_compl, hV, hC.card_eq, Nat.succ_mul]
      omega
    have hdH (v : U) : H.degree v ≤ G.degree v.val := by
      rw [← H.card_neighborFinset_eq_degree, ← G.card_neighborFinset_eq_degree]
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro w hw
        exact (G.mem_neighborFinset _ _).mpr ((H.mem_neighborFinset v w).mp hw)
      · exact fun _ _ _ _ h => Subtype.ext h
    have hsub : (∑ v : U, (H.degree v - r)) ≤ ∑ v : V, (G.degree v - r) := calc
      _ ≤ ∑ v : U, (G.degree v.val - r) :=
        Finset.sum_le_sum fun v _ => Nat.sub_le_sub_right (hdH v) r
      _ = ∑ v ∈ Cᶜ, (G.degree v - r) := 
        (Finset.sum_subtype (p := fun x => x ∈ U) Cᶜ (fun _ => Iff.rfl) (fun v => G.degree v - r)).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    obtain ⟨J₀, hJ₀⟩ := ih (by omega) H hU (hsub.trans_lt hT) (hsub.trans_lt hTop)
      (exteriorUnique_induce hout U)
    let incl := Function.Embedding.subtype (· ∈ U)
    let J := J₀.map incl
    have hJ : G.IsNIndepSet (t + 1) J := by
      refine ⟨?_, (Finset.card_map _).trans hJ₀.card_eq⟩
      intro a ha b hb hab
      obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp hb
      exact hJ₀.isIndepSet ha' hb' (fun e => hab (congrArg incl e))
    have disj : Disjoint C J := by
      apply Finset.disjoint_left.mpr
      intro z hz hJz
      obtain ⟨z', _, rfl⟩ := Finset.mem_map.mp hJz
      exact Finset.mem_compl.mp z'.property hz
    rcases lt_or_eq_of_le ht with hlt | heq
    · obtain ⟨S, hS⟩ := extend_across_clique G C J hC hJ disj hlt (hout C hC)
      exact hi S hS
    · rw [heq] at hJ hV hi
      exact hTop.not_ge (full_clique_independent_excess_bound G hr hV C hC (hout C hC)
        J hJ disj.symm hi)

/-- The induction uses the total degree above r in the chosen color. -/
private theorem missing_of_excess_bounds {V : Type*} [Fintype V] [DecidableEq V]
    (r : ℕ) (hr : 3 ≤ r) (hV : Fintype.card V = r^2 + 1)
    (c : Sym2 V → Fin r) (k : Fin r) (hT : (∑ v, ((colorGraph c k).degree v - r)) < r)
    (hTop : (∑ v, ((colorGraph c k).degree v - r)) < (r-1)*(r-2)) :
    ∃ (S : Finset V) (l : Fin r), S.card = r + 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u,v) ≠ l := by
  by_contra h
  have hb := balanced_of_no_witness c h
  have hout : ExteriorUnique (colorGraph c k) r := fun C hC x hx _ hy _ hz =>
    exterior_clique_neighbor_unique c hb k C hC x hx hy hz
  obtain ⟨S, hS⟩ := independent_on_blocks r hr r le_rfl (colorGraph c k)
    (by simpa [pow_two] using hV) hT hTop hout
  exact h ⟨S, k, hS.card_eq, fun _ hu _ hv huv he => hS.isIndepSet hu hv huv ⟨huv, he⟩⟩

/-- On r²+1 vertices, allowing a total of fewer than r incidences above degree r
in a fixed color still forces an (r+1)-set missing a color, for r ≥ 4. -/
theorem missing_of_total_excess_lt {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} (hr : 4 ≤ r) (hV : Fintype.card V = r^2 + 1)
    (c : Sym2 V → Fin r) (k : Fin r) (hT : (∑ v, ((colorGraph c k).degree v - r)) < r) :
    ∃ (S : Finset V) (l : Fin r), S.card = r + 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u,v) ≠ l := by
  apply missing_of_excess_bounds r (by omega) hV c k hT
  apply hT.trans_le
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [show 4+m-1 = 3+m by omega, show 4+m-2 = 2+m by omega]
  nlinarith

/-- Erdős 617 holds whenever some color occurs on at most r edges at every vertex. -/
theorem missing_of_bounded_color_degree {V : Type*} [Fintype V] [DecidableEq V]
    (r : ℕ) (hr : 3 ≤ r) (hV : Fintype.card V = r^2 + 1)
    (c : Sym2 V → Fin r) (k : Fin r) (hd : ∀ v, (colorGraph c k).degree v ≤ r) :
    ∃ (S : Finset V) (l : Fin r), S.card = r + 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u,v) ≠ l := by
  have zero : (∑ v, ((colorGraph c k).degree v - r)) = 0 := by
    simp [fun v => Nat.sub_eq_zero_of_le (hd v)]
  apply missing_of_excess_bounds r hr hV c k
  · omega
  · rw [zero]
    exact Nat.mul_pos (by omega) (by omega)

/-- In particular, the conclusion holds for arbitrary r if every color class is
a regular graph. Its degree may differ from those of the other colors. -/
theorem missing_of_regular_colors {V : Type*} [Fintype V] [DecidableEq V]
    (r : ℕ) (hr : 3 ≤ r) (hV : Fintype.card V = r^2 + 1)
    (c : Sym2 V → Fin r) (regular : ∀ k, ∃ d, (colorGraph c k).IsRegularOfDegree d) :
    ∃ (S : Finset V) (l : Fin r), S.card = r + 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u,v) ≠ l := by
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card V by omega)
  have small : ∃ k, (colorGraph c k).degree x ≤ r := by
    by_contra! hall
    have lower := Finset.sum_le_sum (s := Finset.univ) (fun k _ => Nat.succ_le_of_lt (hall k))
    rw [sum_colorGraph_degree c x, hV] at lower
    simp [pow_two, Nat.mul_add] at lower
    omega
  obtain ⟨k, hk⟩ := small
  obtain ⟨d, hd⟩ := regular k
  exact missing_of_bounded_color_degree r hr hV c k (fun v => (hd v).trans_le ((hd x) ▸ hk))

/-- It suffices to find r independent vertices in each prescribed color on
(r−1)r+1 vertices of a hypothetical balanced coloring. A vertex of low degree
in that color can then be added as the final vertex. -/
theorem missing_of_last_local_step {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (hr : 3 ≤ r) (hV : Fintype.card V = r^2+1) (c : Sym2 V → Fin r)
    (localStep : Balanced c → ∀ (k : Fin r) (S : Finset V), S.card = (r-1)*r+1 →
      ∃ I ⊆ S, (colorGraph c k).IsNIndepSet r I) :
    ∃ (S : Finset V) (k : Fin r), S.card = r+1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u,v) ≠ k := by
  classical
  by_contra hn
  have hb := balanced_of_no_witness c hn
  let i : Fin r := ⟨0, by omega⟩
  have high : ∃ x, r < (colorGraph c i).degree x := by
    by_contra! h
    exact hn (missing_of_bounded_color_degree r hr hV c i h)
  obtain ⟨x, hx⟩ := high
  have low : ∃ k, (colorGraph c k).degree x < r := by
    by_contra! h
    have hs := Finset.sum_lt_sum (s := Finset.univ) (fun j _ => h j) ⟨i, Finset.mem_univ _, hx⟩
    rw [sum_colorGraph_degree, hV] at hs
    simp [pow_two] at hs
  obtain ⟨k, hk⟩ := low
  let G := colorGraph c k
  have many : (r-1)*r+1 ≤ (Gᶜ.neighborFinset x).card := by
    rw [card_neighborFinset_eq_degree, degree_compl, hV, pow_two, Nat.sub_mul, Nat.one_mul]
    change G.degree x < r at hk
    have hrr : r ≤ r*r := by
      simpa using Nat.mul_le_mul_right r (show 1 ≤ r by omega)
    omega
  obtain ⟨S, hS, hs⟩ := Finset.exists_subset_card_eq many
  obtain ⟨I, hI, hInd⟩ := localStep hb k S hs
  have hnon (v : V) (hv : v ∈ I) : Gᶜ.Adj x v :=
    (Gᶜ.mem_neighborFinset x v).mp (hS (hI hv))
  have hxI : x ∉ I := fun h => (hnon x h).ne rfl
  have finalSet := independent_insert_of_nonadjacent G hInd.isIndepSet x
    (fun v hv => (hnon v hv).2)
  apply hn
  exact ⟨insert x I, k, by rw [Finset.card_insert_of_notMem hxI, hInd.card_eq],
    fun _ hu _ hv huv he => finalSet hu hv huv ⟨huv, he⟩⟩

end Erdos617
