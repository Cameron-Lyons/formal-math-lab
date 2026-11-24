import Erdos617.ClusterCapacity
import Erdos617.ClusterProximity
import Erdos617.PrivateBlocks
import Erdos617.StrictHalfRange

namespace Erdos617

open Finset SimpleGraph

private theorem capacity_polynomial {r t M : ℕ} (hr : 0 < r) (ht : 0 < t)
    (hM : M^2 ≤ 5*r*t^2) (hcap : r-1 ≤ (3*t^2)*M+(3*t^2)^2) : r ≤ 180*t^6 := by
  by_contra! hlarge
  have h46 : t^4 ≤ t^6 := Nat.pow_le_pow_right ht (by decide)
  have hp : 0 < t^6 := Nat.pow_pos ht
  have hsmall : 2*((3*t^2)^2+1) ≤ r := by nlinarith only [hlarge, h46, hp]
  have hrM : r ≤ 6*t^2*M := by nlinarith only [hsmall, hcap, Nat.sub_add_cancel hr]
  have hs := Nat.mul_le_mul hrM hrM
  have he := Nat.mul_le_mul_left (36*t^4) hM
  have hfinal : r*r ≤ r*(180*t^6) := by nlinarith only [hs, he]
  exact hlarge.not_ge (Nat.le_of_mul_le_mul_left hfinal hr)

variable {V : Type*} [DecidableEq V] {r t : ℕ} {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V}

/-- For a balanced coloring, the parameter of every minimal obstruction
strictly below the palette size grows at least as the sixth root of r/180. -/
theorem MinimalObstruction.polynomial_bound (h : MinimalObstruction c k t S)
    (hr : 3 ≤ r) (hb : Balanced c) (htr : t < r) : r ≤ 180*t^6 := by
  classical
  have ht := h.pos
  by_cases hscale : 2*t^2 ≤ r
  · obtain ⟨I, B, hIt, hd, hsub, hcl, _, hfew, F, he, hcross⟩ :=
      h.exists_sparse_clique_cover hr hb htr hscale
    let X := S \ univ.biUnion B
    have hcover : S ⊆ univ.biUnion B ∪ X := by
      intro x hx
      by_cases hmem : x ∈ univ.biUnion B
      · exact mem_union_left _ hmem
      · exact mem_union_right _ (mem_sdiff.mpr ⟨hx,hmem⟩)
    have hcap := cluster_capacity c hb k S X B hIt h.card_eq hcl hcover hfew
      (fun _ hx => h.exists_close_block B hIt hd hsub F hcross hx)
    exact capacity_polynomial (by omega) ht ((Nat.sqrt_le' _).trans he) hcap
  · have h26 : t^2 ≤ t^6 := Nat.pow_le_pow_right ht (by decide)
    omega

/-- In any balanced coloring, every set of p*r+1 vertices contains p+1 vertices
omitting any specified color whenever r exceeds 180*p^6. -/
theorem independent_in_subset_of_large_palette {p : ℕ} (hr : 3 ≤ r)
    (hb : Balanced c) (hlarge : 180*p^6 < r) (hS : S.card = p*r+1) (k : Fin r) :
    ∃ I ⊆ S, (colorGraph c k).IsNIndepSet (p+1) I := by
  by_contra! hfree
  obtain ⟨t, W, htp, _, h⟩ := minimalObstruction_of_failure hS hfree
  have hp : 0 < p := lt_of_lt_of_le h.pos htp
  have hp6 : p ≤ p^6 := by simpa only [pow_one] using
    (Nat.pow_le_pow_right hp (by decide : 1 ≤ 6))
  have ht6 : t^6 ≤ p^6 := Nat.pow_le_pow_left htp 6
  have hbound := h.polynomial_bound hr hb (by omega)
  omega

/-- A counterexample forces one obstruction in the intersection of the
polynomial lower bound and the half-range upper bound. -/
theorem exists_minimalObstruction_polynomial_range [Fintype V] (hr : 3 ≤ r)
    (hV : Fintype.card V = r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c) :
    ∃ (k : Fin r) (t : ℕ) (S : Finset V),
      r ≤ 180*t^6 ∧ t ≤ (r+1)/2 ∧ MinimalObstruction c k t S := by
  obtain ⟨k, t, S, _, ht, h⟩ := exists_minimalObstruction_ceil_half hr hV c hb
  exact ⟨k, t, S, h.polynomial_bound hr hb (by omega), ht, h⟩

end Erdos617
