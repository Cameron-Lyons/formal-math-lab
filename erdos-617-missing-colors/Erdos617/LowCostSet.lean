import Erdos617.RankObstruction

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] {r t : ℕ} {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V}

private theorem upper_count (r t x y : ℕ) (hr : 0 < r)
    (hl : (r-1)*(r*t.choose 2) ≤ y) (hs : y+x = (t*r+1).choose 2) :
    2*x ≤ (t*r+1)*r + r*t^2 := by
  obtain ⟨m,rfl⟩ : ∃ m, r=m+1 := ⟨r-1,by omega⟩
  rw [Nat.add_sub_cancel] at hl
  have h := congrArg (fun z => m*(m+1)*z) (twice_choose_two t)
  nlinarith only [hl, hs, h, twice_choose_two (t*(m+1)+1), Nat.zero_le m]

/-- The other colors' Turán bounds limit the number of edge incidences in the obstruction color. -/
theorem MinimalObstruction.twice_edges_le (h : MinimalObstruction c k t S)
    (hr : 0 < r) (hb : Balanced c) :
    2*blockEdges (colorGraph c k) S ≤ r*S.card+r*t^2 := by
  classical
  let cp : Sym2 S → Fin r := fun e => c (Sym2.map Subtype.val e)
  let E (j : Fin r) := (colorGraph cp j).edgeFinset.card
  have lower (j : Fin r) : r*t.choose 2 ≤ E j :=
    (Nat.le_add_right _ t).trans (induced_color_edge_count_of_balanced hr c hb S h.card_eq j)
  have hl := sum_le_sum (s := univ.erase k) fun j _ => lower j
  simp only [sum_const, card_erase_of_mem (mem_univ k), card_univ, Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_id] at hl
  have hs := sum_color_edges cp
  change (∑ j, E j) = (Fintype.card S).choose 2 at hs
  rw [← sum_erase_add _ _ (mem_univ k),Fintype.card_coe,h.card_eq] at hs
  have hu := upper_count r t (E k) _ hr hl hs
  have he : E k = blockEdges (colorGraph c k) S := (color_blockEdges_eq S c k).symm
  simpa only [he, ← h.card_eq, Nat.mul_comm S.card r] using hu

/-- The total degree excess over r is at most r*t². -/
theorem MinimalObstruction.excess_le (h : MinimalObstruction c k t S)
    (hr : 0 < r) (hb : Balanced c) :
    (∑ x ∈ S, ((S.filter ((colorGraph c k).Adj x)).card-r)) ≤ r*t^2 := by
  have hu := h.twice_edges_le hr hb
  rw [← block_degree_sum, Nat.mul_comm r S.card] at hu
  have heq : (∑ x ∈ S, ((S.filter ((colorGraph c k).Adj x)).card-r)) + S.card*r =
      ∑ x ∈ S, (S.filter ((colorGraph c k).Adj x)).card := by
    rw [show S.card*r = ∑ _ ∈ S,r by simp, ← sum_add_distrib]
    exact sum_congr rfl fun x hx => Nat.sub_add_cancel (h.degree_ge x hx)
  omega

/-- A maximum independent set can be chosen entirely among vertices of degree
at most r+t² inside the obstruction. -/
theorem MinimalObstruction.exists_independent_degree_le (h : MinimalObstruction c k t S)
    (hr : 0 < r) (hb : Balanced c) :
    ∃ I ⊆ S, (colorGraph c k).IsNIndepSet t I ∧
      ∀ x ∈ I, (S.filter ((colorGraph c k).Adj x)).card ≤ r+t^2 := by
  classical
  let e (x : V) := (S.filter ((colorGraph c k).Adj x)).card-r
  let H := S.filter fun x => t^2 < e x
  have hHS : H ⊆ S := filter_subset ..
  have hi : H.card*(t^2+1) ≤ r*t^2 := calc
    _ = ∑ _ ∈ H, (t^2+1) := by simp
    _ ≤ ∑ x ∈ H, e x := sum_le_sum fun x hx => (mem_filter.mp hx).2
    _ ≤ ∑ x ∈ S, e x := sum_le_sum_of_subset hHS
    _ ≤ r*t^2 := h.excess_le hr hb
  have hfew : H.card < r := by
    by_contra! hmany
    have hx := Nat.mul_le_mul_right (t^2+1) hmany
    rw [Nat.mul_add, Nat.mul_one] at hx
    omega
  have ht := h.pos
  have hprod : (t-1)*r+r=t*r := by rw [← Nat.succ_mul, show (t-1).succ=t by omega]
  have hsize : (t-1)*r+1 ≤ (S \ H).card := by
    rw [card_sdiff_of_subset hHS,h.card_eq]
    omega
  obtain ⟨W,hW,hWcard⟩ := exists_subset_card_eq hsize
  obtain ⟨I,hI,hind⟩ := h.smaller (t-1) (by omega) W (hW.trans sdiff_subset) hWcard
  rw [Nat.sub_add_cancel ht] at hind
  refine ⟨I,hI.trans (hW.trans sdiff_subset),hind,?_⟩
  intro x hx
  obtain ⟨hS, hn⟩ := mem_sdiff.mp (hW (hI hx))
  have bound : e x ≤ t^2 := le_of_not_gt fun hl => hn (mem_filter.mpr ⟨hS,hl⟩)
  dsimp [e] at bound
  omega

/-- A version with the weaker degree cap 2t² above r. -/
theorem MinimalObstruction.exists_low_degree_independent (h : MinimalObstruction c k t S)
    (hr : 0 < r) (hb : Balanced c) :
    ∃ I ⊆ S, (colorGraph c k).IsNIndepSet t I ∧
      ∀ x ∈ I, (S.filter ((colorGraph c k).Adj x)).card ≤ r+2*t^2 := by
  obtain ⟨I,hI,hi,hd⟩ := h.exists_independent_degree_le hr hb
  exact ⟨I,hI,hi,fun x hx => by have := hd x hx; omega⟩

end Erdos617
