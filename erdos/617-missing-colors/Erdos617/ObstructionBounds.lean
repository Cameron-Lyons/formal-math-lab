module

public import Erdos617.BlockEdgeBound
public import Erdos617.ColorCounts
public import Erdos617.MinimalObstruction

@[expose] public section

namespace Erdos617

open SimpleGraph Finset

private theorem obstruction_edge_arithmetic (r t x y : ℕ) (hr : 3 ≤ r) (ht : 2 ≤ t)
    (hx : (t*r+1)*r + (2*r-2) ≤ 2*x)
    (hy : (r-1)*(r*t.choose 2 + 2*t - 1) ≤ y)
    (htotal : y+x = (t*r+1).choose 2) :
    r*(4*t+1) ≤ r*t^2 + 4*t := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m+1 := ⟨r-1, by omega⟩
  let L := (m+1)*t.choose 2 + 2*t-1
  have hL : L+1 = (m+1)*t.choose 2 + 2*t := by dsimp [L]; omega
  have hC := congrArg (fun z => m*(m+1)*z) (twice_choose_two t)
  have hM := congrArg (fun z => m*z) hL
  have hdiff : 2*(m+1)-2 = 2*m := by omega
  rw [hdiff] at hx
  change (m+1-1)*L ≤ y at hy
  rw [Nat.add_sub_cancel] at hy
  nlinarith only [hx, hy, htotal, hC, hM, twice_choose_two (t*(m+1)+1)]

variable {V : Type*} {r t : ℕ} {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V}

theorem MinimalObstruction.two_le_parameter [DecidableEq V] (h : MinimalObstruction c k t S)
    (hr : 3 ≤ r) (hb : Balanced c) (ht : t < r) : 2 ≤ t := by
  classical
  let cp : Sym2 S → Fin r := fun e => c (Sym2.map Subtype.val e)
  have hn : Fintype.card S = t*r+1 := (Fintype.card_coe S).trans h.card_eq
  by_contra! hsmall
  have ht1 : t = 1 := by have := h.pos; omega
  have hzero (v : S) : (colorGraph cp k).degree v - r = 0 := by
    have hlt := (colorGraph cp k).degree_lt_card_verts v
    rw [hn, ht1, Nat.one_mul] at hlt
    omega
  have he := h.excess_ge hr hb ht
  change 2*r-2 ≤ ∑ v : S, ((colorGraph cp k).degree v - r) at he
  simp_rw [hzero, sum_const_zero] at he
  omega

/-- All colors other than the obstruction color meet the graph edge floor
on the same vertex set. -/
theorem MinimalObstruction.foreign_edge_sum [DecidableEq V] (h : MinimalObstruction c k t S)
    (hb : Balanced c) (htwo : 2 ≤ t) :
    (r-1)*(r*t.choose 2+2*t-1) ≤ ∑ j ∈ Finset.univ.erase k,
      (colorGraph (fun e : Sym2 S => c (Sym2.map Subtype.val e)) j).edgeFinset.card := by
  classical
  let cp : Sym2 S → Fin r := fun e => c (Sym2.map Subtype.val e)
  let E (j : Fin r) := (colorGraph cp j).edgeFinset.card
  have hn : Fintype.card S = t*r+1 := (Fintype.card_coe S).trans h.card_eq
  have hbalanced : Balanced cp := balanced_pullback c hb (Function.Embedding.subtype (· ∈ S))
  have foreign (j : Fin r) (hjk : j ≠ k) :
      r*t.choose 2 + 2*t - 1 ≤ E j := by
    apply edge_bound_of_clique_and_indep_caps (colorGraph cp j) htwo hn
    · intro I hI
      obtain ⟨u, hu, v, hv, huv, he⟩ := hbalanced I hI.card_eq j
      exact hI.isIndepSet hu hv huv ⟨huv, he⟩
    · intro T hT
      have hI : (colorGraph cp k).IsNIndepSet (t+1) T := by
        refine ⟨?_, hT.card_eq⟩
        intro u hu v hv huv he
        exact hjk ((hT.isClique hu hv huv).2.symm.trans he.2)
      obtain ⟨I, hIS, hI⟩ := lift_independent_subset c k S ⟨T, hI⟩
      exact h.free I hIS hI
  have hs := Finset.sum_le_sum (s := Finset.univ.erase k)
    (fun j hj => foreign j (Finset.mem_erase.mp hj).1)
  simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ k),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  exact hs

/-- A minimal obstruction forces a numerical restriction on its independent-set
parameter `t`, by counting all colors on its `t*r+1` vertices. -/
theorem MinimalObstruction.parameter_bound [DecidableEq V] (h : MinimalObstruction c k t S)
    (hr : 3 ≤ r) (hb : Balanced c) (ht : t < r) :
    r*(4*t+1) ≤ r*t^2 + 4*t := by
  classical
  let cp : Sym2 S → Fin r := fun e => c (Sym2.map Subtype.val e)
  let E (j : Fin r) := (colorGraph cp j).edgeFinset.card
  have hn : Fintype.card S = t*r+1 := (Fintype.card_coe S).trans h.card_eq
  have htwo := h.two_le_parameter hr hb ht
  have hs := h.foreign_edge_sum hb htwo
  have htotal := sum_color_edges cp
  change ∑ j, E j = (Fintype.card S).choose 2 at htotal
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k), hn] at htotal
  have hc := h.twice_edges_ge hr hb ht
  rw [h.card_eq] at hc
  exact obstruction_edge_arithmetic r t _ _ hr htwo hc hs htotal

/-- For at least 17 colors, the first failure cannot occur with `t ≤ 4`. -/
theorem MinimalObstruction.five_le_parameter [DecidableEq V] (h : MinimalObstruction c k t S)
    (hr : 17 ≤ r) (hb : Balanced c) (ht : t < r) : 5 ≤ t := by
  by_contra! hsmall
  have hbound := h.parameter_bound (by omega) hb ht
  have hsq : r*t^2 ≤ r*(4*t) := by
    rw [pow_two]
    exact Nat.mul_le_mul_left r (Nat.mul_le_mul_right t (by omega))
  rw [Nat.mul_add, Nat.mul_one] at hbound
  omega

/-- Every counterexample to the unrestricted conjecture contains a minimal
obstruction whose parameter satisfies the edge-count inequality. -/
theorem exists_minimalObstruction_parameter_bound [Fintype V] [DecidableEq V]
    (hr : 3 ≤ r) (hV : Fintype.card V = r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c) :
    ∃ (k : Fin r) (t : ℕ) (S : Finset V), 1 ≤ t ∧ t < r ∧
      MinimalObstruction c k t S ∧ r*(4*t+1) ≤ r*t^2 + 4*t := by
  obtain ⟨k, t, S, hpos, ht, h⟩ := exists_minimalObstruction hr hV c hb
  exact ⟨k, t, S, hpos, ht, h, h.parameter_bound hr hb ht⟩

/-- Any counterexample with at least 17 colors contains an obstruction of
order `t*r+1` for some `5 ≤ t < r`. -/
theorem exists_minimalObstruction_five_le [Fintype V] [DecidableEq V]
    (hr : 17 ≤ r) (hV : Fintype.card V = r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c) :
    ∃ (k : Fin r) (t : ℕ) (S : Finset V), 5 ≤ t ∧ t < r ∧ MinimalObstruction c k t S := by
  obtain ⟨k, t, S, _, ht, h⟩ := exists_minimalObstruction (by omega) hV c hb
  exact ⟨k, t, S, h.five_le_parameter hr hb ht, ht, h⟩

/-- In a balanced coloring, every set of 4r+1 vertices contains five
vertices missing any prescribed color, for r ≥ 17. -/
theorem independent_five_in_subset (hr : 17 ≤ r) (c : Sym2 V → Fin r) (hb : Balanced c)
    (k : Fin r) (S : Finset V) (hS : S.card = 4*r+1) :
    ∃ I ⊆ S, (colorGraph c k).IsNIndepSet 5 I := by
  classical
  by_contra! hn
  obtain ⟨t, W, ht, _, hm⟩ := minimalObstruction_of_failure hS hn
  have := hm.five_le_parameter hr hb (by omega)
  omega

end Erdos617
