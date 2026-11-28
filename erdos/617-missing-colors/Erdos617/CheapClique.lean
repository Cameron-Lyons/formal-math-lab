module

public import Erdos617.ManyCliqueBlocks
public import Erdos617.LowCostSet

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

private theorem least_foreign_bound (r t x y : ℕ) (hr : 3 ≤ r)
    (hx : (t*r+1)*r ≤ 2*x) (hy : (r-1)*y+x ≤ (t*r+1).choose 2) :
    y ≤ r*t.choose 2+t^2 := by
  obtain ⟨m,rfl⟩ : ∃ m, r=m+3 := ⟨r-3,by omega⟩
  rw [show m+3-1=m+2 by omega] at hy
  by_contra! hlarge
  have hm := Nat.mul_le_mul_left (m+2) hlarge.le
  have hchoose := congrArg (fun z => (m+2)*(m+3)*z) (twice_choose_two t)
  nlinarith only [hx,hy,hm,hchoose,twice_choose_two (t*(m+3)+1),Nat.zero_le (m*t^2),
    Nat.zero_le (t^2),Nat.zero_le m]

variable {V : Type*} [DecidableEq V] {r t : ℕ} {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V}

/-- A sparse foreign color supplies disjoint t-cliques. Averaging the obstruction
color's degree excess over them yields an independent set with small degree sum. -/
theorem MinimalObstruction.exists_independent_degree_sum_le (h : MinimalObstruction c k t S)
    (hr : 3 ≤ r) (ht : 2 ≤ t) (htr : t < r) (hscale : 2*t^2 ≤ r) (hb : Balanced c) :
    ∃ I ⊆ S, (colorGraph c k).IsNIndepSet t I ∧
      (∑ x ∈ I, (S.filter ((colorGraph c k).Adj x)).card) ≤ t*r+2*t^2 := by
  classical
  let cp : Sym2 S → Fin r := fun e => c (Sym2.map Subtype.val e)
  let E (j : Fin r) := (colorGraph cp j).edgeFinset.card
  have hn : Fintype.card S = t*r+1 := (Fintype.card_coe S).trans h.card_eq
  have hbp := balanced_pullback c hb (Function.Embedding.subtype (· ∈ S))
  let F := univ.erase k
  have hcF : F.card = r-1 := by simp [F]
  have hF : F.Nonempty := card_pos.mp (by rw [hcF]; omega)
  obtain ⟨j,hj,hmin⟩ := F.exists_min_image E hF
  have hjk := (mem_erase.mp hj).1
  have hjlow : F.card*E j ≤ ∑ l ∈ F, E l := by simpa using sum_le_sum hmin
  have htotal := sum_color_edges cp
  change (∑ l, E l) = (Fintype.card S).choose 2 at htotal
  rw [← sum_erase_add _ _ (mem_univ k),hn] at htotal
  have hkt := h.twice_edges_ge hr hb htr
  change S.card*r + (2*r-2) ≤ 2*E k at hkt
  rw [h.card_eq] at hkt
  have hu : E j ≤ r*t.choose 2+t^2 := by
    apply least_foreign_bound r t (E k) (E j) hr (by omega)
    rw [← hcF,← htotal]
    exact Nat.add_le_add_right hjlow _
  have hα : (colorGraph cp j).IndepSetFree (r+1) := by
    intro I hI
    obtain ⟨x,hx,y,hy,hxy,he⟩ := hbp I hI.card_eq j
    exact hI.isIndepSet hx hy hxy ⟨hxy,he⟩
  have hω : (colorGraph cp j).CliqueFree (t+1) := by
    intro I hI
    have hind : (colorGraph cp k).IsNIndepSet (t+1) I := by
      refine ⟨?_,hI.card_eq⟩
      intro x hx y hy hxy he
      exact hjk ((hI.isClique hx hy hxy).2.symm.trans he.2)
    obtain ⟨J,hJS,hJ⟩ := lift_independent_subset c k S ⟨I,hind⟩
    exact h.free J hJS hJ
  obtain ⟨P,hd,hi,hpack⟩ := many_clique_blocks (colorGraph cp j) ht hn hα hω hu
  let excess (x : V) := (S.filter ((colorGraph c k).Adj x)).card - r
  have htotalEx : (∑ x : S, excess x) ≤ r*t^2 := by
    rw [← sum_subtype S (fun _ => Iff.rfl) excess]
    exact h.excess_le (by omega) hb
  have hex : (∑ A ∈ P, ∑ x ∈ A, excess x.val) ≤ r*t^2 := by
    have hsum := sum_biUnion (f := fun x : S => excess x.val) hd
    exact hsum.symm.trans_le ((sum_le_sum_of_subset (subset_univ _)).trans htotalEx)
  obtain ⟨A,hA,hcost⟩ : ∃ A ∈ P, (∑ x ∈ A, excess x.val) ≤ 2*t^2 := by
    by_contra! hbad
    have hnP := sum_le_sum (f := fun _ : Finset S => 2*t^2+1)
      (g := fun A => ∑ x ∈ A, excess x.val) (fun A hA => hbad A hA)
    change (∑ _ ∈ P, (2*t^2+1)) ≤ _ at hnP
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_add,Nat.mul_one] at hnP
    have hm := Nat.mul_le_mul_right (t^2) (show r ≤ 2*P.card by omega)
    rw [Nat.mul_assoc, Nat.mul_left_comm] at hm
    have hP : 0 < P.card := by omega
    omega
  let incl := Function.Embedding.subtype (· ∈ S)
  let I := A.map incl
  have hIS : I ⊆ S := fun _ hx => A.property_of_mem_map_subtype hx
  have hcard : I.card = t := (card_map _).trans (hi A hA).card_eq
  refine ⟨I,hIS,⟨?_,hcard⟩,?_⟩
  · intro x hx y hy hxy he
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
    obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
    have hc := (hi A hA).isClique ha hb (fun e => hxy (congrArg incl e))
    exact hjk (hc.2.symm.trans he.2)
  · have hdg (x : V) (hx : x ∈ I) : (S.filter ((colorGraph c k).Adj x)).card = r+excess x :=
      (Nat.add_sub_of_le (h.degree_ge x (hIS hx))).symm
    have heI : (∑ x ∈ I,excess x) ≤ 2*t^2 := by simpa [I,incl] using hcost
    rw [sum_congr rfl hdg, sum_add_distrib, sum_const,hcard,nsmul_eq_mul,Nat.cast_id]
    omega

end Erdos617
