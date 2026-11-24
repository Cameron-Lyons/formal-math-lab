import Erdos617.ColorCounts
import Erdos617.TriangleFreeRegular
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Linarith

namespace Erdos617

open SimpleGraph Finset

/-- Selecting one endpoint per color edge leaves an independent complement. -/
private theorem color_edges_at_least_r_on_two_blocks {V : Type*} [Fintype V] [DecidableEq V]
    (r : ℕ) (hV : Fintype.card V = 2 * r) (c : Sym2 V → Fin r) (hb : Balanced c) (j : Fin r) :
    r ≤ (colorGraph c j).edgeFinset.card := by
  let E := (colorGraph c j).edgeFinset
  let C := E.image (fun e : Sym2 V ↦ e.out.1)
  have hC : C.card ≤ E.card := card_image_le
  by_contra! hfew
  change E.card < r at hfew
  have hcomp : r + 1 ≤ Cᶜ.card := by rw [card_compl, hV]; omega
  obtain ⟨S, hS, hs⟩ := exists_subset_card_eq hcomp
  obtain ⟨u, hu, v, hv, huv, he⟩ := hb S hs j
  let e : Sym2 V := s(u,v)
  have heE : e ∈ E := mem_edgeFinset.mpr (show (colorGraph c j).Adj u v from ⟨huv, he⟩)
  have hcovered : e.out.1 ∈ C := mem_image_of_mem _ heE
  have hmem : e.out.1 = u ∨ e.out.1 = v := Sym2.mem_iff.mp e.out_fst_mem
  rcases hmem with eqa | eqb
  · exact mem_compl.mp (hS hu) (eqa ▸ hcovered)
  · exact mem_compl.mp (hS hv) (eqb ▸ hcovered)

/-- If the complement of a color on `2*r` vertices is triangle-free, the color
contains an `r`-clique. -/
theorem clique_on_two_blocks_of_triangle_free (r : ℕ) (hr : 6 ≤ r)
    {V : Type*} [Fintype V] [DecidableEq V] (hV : Fintype.card V = 2 * r)
    (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r)
    (ht : (colorGraph c k)ᶜ.CliqueFree 3) :
    ∃ C, (colorGraph c k).IsNClique r C := by
  classical
  let H := (colorGraph c k)ᶜ
  by_contra hnone
  have hi : H.IndepSetFree r := by
    intro C hC
    exact hnone ⟨C, (isNIndepSet_compl _).mp hC⟩
  have hupper (v : V) : H.degree v ≤ r - 1 := by
    by_contra! hlarge
    have hcard : r ≤ (H.neighborFinset v).card := by
      rw [card_neighborFinset_eq_degree]
      omega
    obtain ⟨C, hC, hs⟩ := exists_subset_card_eq hcard
    apply hi C
    refine ⟨?_, hs⟩
    have hn := H.isIndepSet_neighborSet_of_triangleFree ht v
    exact hn.mono (fun w hw ↦ (H.mem_neighborFinset v w).mp (hC hw))
  have hothers := sum_le_sum (s := univ.erase k)
    (fun j _ ↦ color_edges_at_least_r_on_two_blocks r hV c hb j)
  rw [sum_other_color_edges c k] at hothers
  simp only [sum_const, card_erase_of_mem (mem_univ k), card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hothers
  have hsumH : ∑ x, H.degree x = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
  have hreg (v : V) : H.degree v = r-1 := by
    by_contra hne
    have hstrict := sum_lt_sum (s := univ) (fun x _ ↦ hupper x)
      ⟨v, mem_univ _, lt_of_le_of_ne (hupper v) hne⟩
    rw [hsumH] at hstrict
    simp only [sum_const, card_univ, nsmul_eq_mul, hV] at hstrict
    change (r - 1) * r ≤ H.edgeFinset.card at hothers
    nlinarith only [hstrict, hothers]
  exact triangle_free_regular_impossible r hr H hV hreg ht hi

end Erdos617
