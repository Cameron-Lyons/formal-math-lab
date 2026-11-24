import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic.Linarith

namespace Erdos617

open Finset

variable {X Y : Type*}

/-- Rows with twice their incidence degree at least q. -/
def heavyIncidences (A : Finset X) (B : Finset Y) (R : X → Y → Prop) [DecidableRel R]
    (q : ℕ) : Finset X := A.filter fun x => q≤2*(B.filter (R x)).card

theorem incidence_heavy_bound (A : Finset X) (B : Finset Y) (R : X → Y → Prop)
    [DecidableRel R] (q k : ℕ) (cap : ∀ y∈B,(A.filter fun x => R x y).card≤k) :
    q*(heavyIncidences A B R q).card≤2*k*B.card := by
  classical
  let H := heavyIncidences A B R q
  have lo := sum_le_sum (s:=H) (f:=fun _ => q)
    (g:=fun x => 2*(B.filter (R x)).card) (fun _ hx => (mem_filter.mp hx).2)
  have inc : (∑ x∈H,(B.filter (R x)).card)=∑ y∈B,(H.filter fun x => R x y).card :=
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow R
  have up := sum_le_sum (s:=B) (f:=fun y => (H.filter fun x => R x y).card)
    (g:=fun _ => k) (fun y hy => (card_le_card (filter_subset_filter _ (filter_subset ..))).trans (cap y hy))
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,←mul_sum,inc] at lo up
  change q*H.card≤2*k*B.card
  nlinarith only [lo,up]

theorem incidence_half_le_four (A : Finset X) (B : Finset Y) (R : X → Y → Prop)
    [DecidableRel R] (nonempty : B.Nonempty) (cap : ∀ y∈B,(A.filter fun x => R x y).card≤2) :
    (heavyIncidences A B R B.card).card≤4 := by
  have le := incidence_heavy_bound A B R B.card 2 cap
  have pos := card_pos.mpr nonempty
  exact Nat.le_of_mul_le_mul_left (by simpa [Nat.mul_comm] using le) pos

/-- For 2r−1 columns of degree at most two, fewer than eight rows can
have degree at least r/2. -/
theorem incidence_half_rank_lt_eight (A : Finset X) (B : Finset Y) (R : X → Y → Prop)
    [DecidableRel R] {r : ℕ} (hr : 0<r) (size : B.card=2*r-1)
    (cap : ∀ y∈B,(A.filter fun x => R x y).card≤2) :
    (heavyIncidences A B R r).card<8 := by
  have le := incidence_heavy_bound A B R r 2 cap
  rw [size] at le
  by_contra! big
  have lower := Nat.mul_le_mul_left r big
  omega

private theorem covering_image_bound {Z : Type*} [DecidableEq Z] (A H : Finset X) (W : X → Finset Y)
    (R : X → Y → Prop) [DecidableRel R] (encode : X → X → Z) (C : Finset Z)
    (a k : ℕ) (cap : ∀ x∈H,∀ y∈W x,(A.filter fun z => R z y).card≤k)
    (width : ∀ x∈H,(W x).card≤a)
    (orient : ∀ e∈C,∃ x∈H,∃ z∈A,e=encode x z ∧ ∃ y∈W x,R z y) :
    C.card≤H.card*(a*k) := by
  classical
  let mates (x : X) := (W x).biUnion fun y => A.filter fun z => R z y
  let covers (x : X) := (mates x).image (encode x)
  have sub : C⊆H.biUnion covers := by
    intro e he
    obtain ⟨x,hx,z,hz,rfl,y,hy,hit⟩ := orient e he
    exact mem_biUnion.mpr ⟨x,hx,mem_image.mpr ⟨z,mem_biUnion.mpr ⟨y,hy,mem_filter.mpr ⟨hz,hit⟩⟩,rfl⟩⟩
  apply (card_le_card sub).trans (card_biUnion_le_card_mul _ _ _ ?_)
  intro x hx
  exact card_image_le.trans ((card_biUnion_le_card_mul _ _ k (cap x hx)).trans (Nat.mul_le_mul_right k (width x hx)))

/-- Count unordered covering pairs by choosing a heavy endpoint and a
witness hit by the other endpoint. -/
theorem covering_pairs_bound [DecidableEq X] (A H : Finset X) (W : X → Finset Y)
    (R : X → Y → Prop) [DecidableRel R] (C : Finset (Sym2 X))
    (k a : ℕ) (cap : ∀ x∈H,∀ y∈W x,(A.filter fun z => R z y).card≤k)
    (width : ∀ x∈H,(W x).card≤a)
    (orient : ∀ e∈C,∃ x∈H,∃ z∈A,e=s(x,z) ∧ ∃ y∈W x,R z y) :
    C.card≤H.card*(a*k) :=
  covering_image_bound A H W R (fun x z => s(x,z)) C a k cap width orient

/-- Count ordered pairs when either endpoint can be heavy. A heavy endpoint
has a fixed witness of width a, each member of which has at most k mates. -/
theorem covering_ordered_pairs_bound [DecidableEq X] (A H : Finset X) (W : X → Finset Y)
    (R : X → Y → Prop) [DecidableRel R] (K : X → X → Prop) [DecidableRel K]
    (k a : ℕ) (cap : ∀ x∈H,∀ y∈W x,(A.filter fun z => R z y).card≤k)
    (width : ∀ x∈H,(W x).card≤a)
    (heavy : ∀ x∈A,∀ z∈A,K x z → x∈H ∨ z∈H)
    (hit : ∀ x∈H,∀ z∈A,K x z ∨ K z x → ∃ y∈W x,R z y) :
    (A.offDiag.filter fun p => K p.1 p.2).card≤2*(H.card*(a*k)) := by
  classical
  let C := A.offDiag.filter fun p => K p.1 p.2
  let L := C.filter fun p => p.1∈H
  let U := C.filter fun p => p.1∉H
  have boundL := covering_image_bound A H W R Prod.mk L a k cap width (by
    rintro ⟨x,z⟩ he
    obtain ⟨he,hH⟩ := mem_filter.mp he
    obtain ⟨hA,hK⟩ := mem_filter.mp he
    obtain ⟨_,hz,_⟩ := mem_offDiag.mp hA
    exact ⟨x,hH,z,hz,rfl,hit x hH z hz (Or.inl hK)⟩)
  have boundU := covering_image_bound A H W R (fun z x => (x,z)) U a k cap width (by
    rintro ⟨x,z⟩ he
    obtain ⟨he,hn⟩ := mem_filter.mp he
    obtain ⟨hA,hK⟩ := mem_filter.mp he
    obtain ⟨hx,hz,_⟩ := mem_offDiag.mp hA
    have hH := (heavy x hx z hz hK).resolve_left hn
    exact ⟨z,hH,x,hx,rfl,hit z hH x hx (Or.inr hK)⟩)
  have sizes : L.card+U.card=C.card := card_filter_add_card_filter_not _
  change C.card≤2*(H.card*(a*k))
  omega

end Erdos617
