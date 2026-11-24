import Erdos617.ClusterAmbiguity
import Erdos617.ClusterAssignment
import Erdos617.ClusterMultiplicity
import Erdos617.ClusterSingles
import Erdos617.PrivateBlocks
import Erdos617.StrictHalfRange

/-!
# A quadratic parameter bound for a balanced coloring

Inside a minimal obstruction of order `t*r+1`, a maximum independent set
with small total degree gives t disjoint monochromatic cliques covering all
but at most `3*t²` vertices. At most `5*r*t²` edges of the obstruction color
run between these cliques. If `r > 1000*t²`, an independent transversal shows
that the vertices close to just one clique themselves form a clique for each
index. Each remaining vertex can be assigned to two of the resulting cliques.
Balance requires at least `r-1` additional foreign-color incidences per extra
assignment. Counting the nonneighbors of those vertices gives fewer.
-/

namespace Erdos617

open Finset SimpleGraph

private theorem row_size_lower {V ι : Type*} [DecidableEq V] [Fintype ι] {r t : ℕ}
    (S : Finset V) (B : ι → Finset V) (ht : Fintype.card ι = t) (hS : S.card = t*r+1)
    (hd : Pairwise (fun i j => Disjoint (B i) (B j))) (hsub : ∀ i, B i ⊆ S)
    (hsize : ∀ i, (B i).card ≤ r) (i : ι) :
    r ≤ (B i).card + (S \ univ.biUnion B).card := by
  classical
  have cover := card_sdiff_add_card_eq_card (biUnion_subset.mpr (fun j _ => hsub j) :
    univ.biUnion B ⊆ S)
  rw [card_biUnion (fun a _ b _ hne => hd (i := a) (j := b) hne), hS] at cover
  have rest := sum_le_sum (s := univ.erase i) (fun j _ => hsize j)
  have split := sum_erase_add univ (fun j => (B j).card) (mem_univ i)
  have hpos : 0 < t := ht ▸ Fintype.card_pos_iff.mpr ⟨i⟩
  have hmul : (t-1)*r+r=t*r := by rw [← Nat.succ_mul, show (t-1).succ=t by omega]
  simp only [sum_const, card_erase_of_mem (mem_univ _), card_univ, ht, nsmul_eq_mul,
    Nat.cast_id] at rest
  omega

variable {V ι : Type*} [DecidableEq V] [Fintype ι] {r t : ℕ}
    {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V}

/-- If the palette is large compared with t², unique close rows form cliques.
Each remaining vertex can be counted in two such rows with low total cost. -/
private theorem incompatible_cluster_cover (h : MinimalObstruction c k t S)
    (hb : Balanced c) (hlarge : 1000*t^2 < r) (B : ι → Finset V) (ht : Fintype.card ι = t)
    (hd : Pairwise (fun i j => Disjoint (B i) (B j))) (hsub : ∀i, B i ⊆ S)
    (hc : ∀i, (colorGraph c k).IsClique (B i : Set V)) (hsize : ∀i, (B i).card ≤ r)
    (hfew : (S \ univ.biUnion B).card ≤ 3*t^2) (F : Finset (Sym2 V))
    (he : F.card ≤ 5*r*t^2)
    (hcross : ∀ i j, i ≠ j → ∀ x ∈ B i, ∀ y ∈ B j, (colorGraph c k).Adj x y → s(x,y) ∈ F) :
    False := by
  classical
  let G := colorGraph c k
  let v := r/10
  let q := 6*v
  let X := S \ univ.biUnion B
  let U := singleBlock G B q S
  let H := S \ univ.biUnion U
  let A := H \ X
  have tpos := h.pos
  have apos : 0 < t^2 := Nat.pow_pos tpos
  have hv : 100*t^2 ≤ v := by dsimp [v]; omega
  have vr : 10*v ≤ r := by dsimp [v]; omega
  have rv : r ≤ 11*v := by dsimp [v] at *; omega
  have hscale0 : r+3 ≤ 11*v := by dsimp [v] at *; omega
  have hsparse : F.card ≤ 55*v*t^2 :=
    he.trans (by nlinarith only [Nat.mul_le_mul_right (t^2) rv])
  have hsqrt : Nat.sqrt F.card ≤ v := by
    have hs : F.card ≤ v*v := by nlinarith only [hsparse, Nat.mul_le_mul_left v hv]
    simpa using Nat.sqrt_le_sqrt hs
  have hq : 1 ≤ q := by dsimp [q]; omega
  have hnear (x : V) (hx : x ∈ S) : ∃ i, ((B i).filter fun y => ¬ G.Adj x y).card ≤ v := by
    by_cases hxB : x ∈ univ.biUnion B
    · obtain ⟨i, _, hi⟩ := mem_biUnion.mp hxB
      exact ⟨i, (clique_misses_at_most_one G (hc i) hi).trans (by omega)⟩
    · obtain ⟨i, hmiss⟩ := h.exists_close_block B ht hd hsub F hcross (mem_sdiff.mpr ⟨hx, hxB⟩)
      exact ⟨i, hmiss.trans hsqrt⟩
  have hclique (i : ι) : G.IsClique (U i : Set V) :=
    h.singleBlock_isClique B ht hd hsub hsize F hcross (by dsimp [q]; omega) i
  have hrow (j : ι) : 3*v+q ≤ (B j).card := by
    have hl := row_size_lower S B ht h.card_eq hd hsub hsize j
    dsimp [q]
    omega
  -- Charge each ambiguous vertex in an original row to its neighbors in a second row.
  have amb := ambiguous_incidence_bound G B A F hrow hcross (by
    intro x hx
    obtain ⟨hxH, hxX⟩ := mem_sdiff.mp hx
    have hxS := (mem_sdiff.mp hxH).1
    have hxB : x ∈ univ.biUnion B := by
      by_contra hn
      exact hxX (mem_sdiff.mpr ⟨hxS,hn⟩)
    obtain ⟨i, _, hxi⟩ := mem_biUnion.mp hxB
    obtain ⟨j, hji, hj⟩ := ambiguous_in_row_has_other G B S hc hq i x hxH hxi
    exact ⟨i, j, hji.symm, hxi, hj⟩)
  have hA : A.card ≤ 37*t^2 := by
    have hm : (3*v)*A.card ≤ (3*v)*(37*t^2) := by nlinarith only [amb, hsparse]
    exact Nat.le_of_mul_le_mul_left hm (by omega)
  have hX : X.card ≤ 3*t^2 := hfew
  have hH : H.card ≤ 40*t^2 := by
    have hcut : H.card ≤ A.card + X.card := card_le_card_sdiff_add_card
    omega
  let cost (x : V) (i : ι) := ((U i).filter fun y => ¬G.Adj x y).card
  obtain ⟨Y, hY, hcount, hcost⟩ := double_cluster_assignment H cost (v+X.card) (q+X.card)
    (ambiguous_has_two_close_singles G B S hc hq (by dsimp [q]; omega) hnear)
  have hdis (i : ι) : Disjoint (U i) (Y i) := disjoint_left.mpr fun x hxi hxy =>
    (mem_sdiff.mp (hY i hxy)).2 (mem_biUnion.mpr ⟨i, mem_univ _, hxi⟩)
  have hcover : t*r+1 ≤ (∑ i, (U i).card) + H.card := by
    have hl := card_biUnion_le (s := (univ : Finset ι)) (t := U)
    have hu : S.card ≤ H.card + (univ.biUnion U).card := card_le_card_sdiff_add_card
    rw [h.card_eq] at hu
    omega
  -- Each ambiguous vertex contributes two memberships to the foreign-color count.
  have demand := cluster_multiplicity_capacity c hb k U H Y ht hclique hdis hcover hY
    (le_refl H.card) (by omega : H.card+H.card ≤ _) hcount.le
  change (r-1)*(1+H.card) ≤ (∑ i, ∑ x ∈ Y i, cost x i)+2*H.card^2 at demand
  have unit : v+X.card+(q+X.card)+2*H.card ≤ r-1 := by
    dsimp [q]
    omega
  have total := Nat.mul_le_mul_left H.card unit
  have hr : 1 < r := by omega
  nlinarith only [demand, hcost, total, Nat.sub_add_cancel (show 1 ≤ r by omega), hr]

/-- Every minimal obstruction below the palette size satisfies r ≤ 1000*t². -/
theorem MinimalObstruction.quadratic_bound (h : MinimalObstruction c k t S)
    (hr : 3 ≤ r) (hb : Balanced c) (htr : t < r) : r ≤ 1000*t^2 := by
  classical
  by_contra! hlarge
  obtain ⟨I, B, hIt, hd, hsub, hcl, hsize, hfew, F, he, hcross⟩ :=
    h.exists_sparse_clique_cover hr hb htr (by omega)
  exact incompatible_cluster_cover h hb hlarge B hIt hd hsub hcl hsize hfew F he hcross

/-- Any prescribed color can be avoided on p+1 vertices of any set of p*r+1
vertices in a balanced coloring as soon as r exceeds 1000*p². -/
theorem independent_in_subset_of_quadratic_palette {p : ℕ} (hr : 3 ≤ r)
    (hb : Balanced c) (hlarge : 1000*p^2 < r) (hS : S.card = p*r+1) (k : Fin r) :
    ∃ I ⊆ S, (colorGraph c k).IsNIndepSet (p+1) I := by
  by_contra! hfree
  obtain ⟨t, W, htp, _, h⟩ := minimalObstruction_of_failure hS hfree
  have hpos : 0 < p := lt_of_lt_of_le h.pos htp
  have hp : p ≤ p^2 := by simpa [pow_two] using Nat.mul_le_mul_left p hpos
  have ht2 := Nat.pow_le_pow_left htp 2
  have hbound := h.quadratic_bound hr hb (by omega)
  omega

/-- Both parameter bounds hold for the same color and vertex set in a counterexample. -/
theorem exists_minimalObstruction_quadratic_range [Fintype V] (hr : 3 ≤ r)
    (hV : Fintype.card V = r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c) :
    ∃ (k : Fin r) (t : ℕ) (S : Finset V),
      r ≤ 1000*t^2 ∧ t ≤ (r+1)/2 ∧ MinimalObstruction c k t S := by
  obtain ⟨k, t, S, _, ht, h⟩ := exists_minimalObstruction_ceil_half hr hV c hb
  exact ⟨k, t, S, h.quadratic_bound hr hb (by omega), ht, h⟩

/-- A sufficient local statement for the original conclusion, restricted to the
range of parameters that survives the quadratic and rank estimates. -/
theorem missing_of_local_window [Fintype V] (hr : 3 ≤ r) (hV : Fintype.card V = r^2+1)
    (c : Sym2 V → Fin r)
    (hlocal : ∀ (k : Fin r) (t : ℕ), r ≤ 1000*t^2 → t ≤ (r+1)/2 →
      5*r*t+4 ≤ r*t^2+2*r+6*t → ∀ W : Finset V, W.card = t*r+1 →
      ∃ I ⊆ W, (colorGraph c k).IsNIndepSet (t+1) I) :
    ∃ (S : Finset V) (k : Fin r), S.card = r+1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u,v) ≠ k := by
  by_contra hn
  have hb := balanced_of_no_witness c hn
  obtain ⟨k, t, W, hlo, hhi, h⟩ := exists_minimalObstruction_quadratic_range hr hV c hb
  obtain ⟨I, hIW, hi⟩ := hlocal k t hlo hhi (h.rank_parameter_bound hr hb (by omega)) W h.card_eq
  exact h.free I hIW hi

end Erdos617
