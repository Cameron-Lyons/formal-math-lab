import Erdos617.DoubleCover
import Erdos617.DoubleCoverParity
import Erdos617.DoubleCoverStarSum
import Erdos617.DoubleCoverTriangles

namespace Erdos617

open Finset SimpleGraph

variable {V ι : Type*} [DecidableEq V] [Fintype ι] [DecidableEq ι]
    {r t : ℕ} {S : Finset V} {c : Sym2 V → Fin r} {k : Fin r}

/-- A first obstruction has no exact twofold cover by 2t+1 cliques. -/
theorem MinimalObstruction.no_odd_double_clique_cover (h : MinimalObstruction c k t S)
    (hb : Balanced c) (ht : 2 ≤ t) (htr : t < r) (B : ι → Finset V)
    (hn : Fintype.card ι = 2*t+1) (hsub : ∀ i, B i ⊆ S)
    (hcl : ∀ i, (colorGraph c k).IsClique (B i : Set V)) :
    ¬ ∀ x ∈ S, (univ.filter fun i => x ∈ B i).card = 2 := by
  intro htwo
  let b (i : ι) := (B i).card
  let δ (i : ι) := r-b i
  let w (i j : ι) := (B i ∩ B j).card
  let g (i j : ι) := (B i ∪ B j).card-r
  obtain ⟨hs, hcap, hrow, hpair⟩ := h.double_cover_data hb ht htr B hn hsub hcl htwo
  have hdpos (i : ι) : 1 ≤ δ i := by dsimp [δ,b]; have := hcap i; omega
  have hbr (i : ι) : b i+δ i = r := by dsimp [δ,b]; have := hcap i; omega
  have hdsum : (∑ i, δ i)+2=r := by
    have total := sum_congr (s₁ := univ) rfl (fun i _ => hbr i)
    simp only [sum_add_distrib, sum_const, card_univ, hn, nsmul_eq_mul, Nat.cast_id] at total
    change (∑ i, b i) = 2*(t*r+1) at hs
    nlinarith only [total, hs]
  have hpos (i : ι) : 0 < b i := by
    have low := sum_le_sum (s := univ.erase i) fun j _ => hcap j
    have split := sum_erase_add univ (fun j => (B j).card) (mem_univ i)
    rw [hs] at split
    simp only [sum_const, card_erase_of_mem (mem_univ i), card_univ, hn,
      Nat.add_sub_cancel, nsmul_eq_mul, Nat.cast_id] at low
    dsimp [b]
    nlinarith only [low, split, congrArg (2*t*·) (Nat.sub_add_cancel (show 1≤r by omega))]
  have hw (i j : ι) : w i j = w j i := by simp [w,inter_comm]
  have hg (i j : ι) : g i j = g j i := by simp [g,union_comm]
  have heq (i j : ι) (hij : i ≠ j) : g i j+w i j+δ j = b i := by
    have hu := (hpair i j hij).1
    have hc := card_union_add_card_inter (B i) (B j)
    dsimp [g,w,δ,b]
    have := hcap j
    omega
  have hp (i j : ι) (hij : i≠j) : w i j*g i j+
      (∑ z ∈ (univ.erase i).erase j, w i z*w j z) ≤ δ i*δ j+g i j := by
    let l := (B i \ B j).card
    let d := (B j \ B i).card
    have he := double_cover_triangle_budget c hb k S B hsub hcl htwo i j hij
    change (r-1)*g i j+(∑ z ∈ (univ.erase i).erase j,w i z*w j z) ≤ l*d at he
    have h1 : l+w i j=b i := card_sdiff_add_card_inter .. 
    have h2 : d+w i j=b j := by simpa only [w,b,d,inter_comm] using card_sdiff_add_card_inter (B j) (B i)
    have hr := heq i j hij
    have hrr := heq j i hij.symm
    rw [hg j i,hw j i] at hrr
    have hl : l=δ j+g i j := by omega
    have hd : d=δ i+g i j := by omega
    have heq' : δ i+δ j+g i j+w i j=r := by have := hbr i; omega
    rw [hl,hd] at he
    nlinarith only [he,congrArg (·*g i j) heq',congrArg (·*g i j) (Nat.sub_add_cancel (show 1≤r by omega))]
  have hmean := double_cover_star_mean ht hn b δ w g hdpos hbr hdsum hw hg hrow heq hp
  exact no_odd_partner_table ht hn b δ w g hpos hdpos hbr hdsum hw hg hrow heq hmean

/-- Any family of obstruction-color cliques covering every vertex at least twice
uses at least 2t+2 cliques. -/
theorem MinimalObstruction.twofold_clique_cover_card (h : MinimalObstruction c k t S)
    (hb : Balanced c) (ht : 2 ≤ t) (htr : t < r) (B : ι → Finset V)
    (hsub : ∀ i, B i ⊆ S) (hcl : ∀ i, (colorGraph c k).IsClique (B i : Set V))
    (hcover : ∀ x ∈ S, 2 ≤ (univ.filter fun i => x ∈ B i).card) :
    2*t+2 ≤ Fintype.card ι := by
  classical
  have chooseTwo (x : S) : ∃ T ⊆ univ.filter (fun i => x.val ∈ B i), T.card=2 :=
    exists_subset_card_eq (hcover x.val x.prop)
  choose f hf hfc using chooseTwo
  let U (i : ι) := S.filter (fun x => ∃ hx : x ∈ S, i ∈ f ⟨x,hx⟩)
  have hUB (i : ι) : U i ⊆ B i := by
    intro x hx
    obtain ⟨_,hxS,hi⟩ := mem_filter.mp hx
    exact (mem_filter.mp (hf ⟨x,hxS⟩ hi)).2
  have hUS (i : ι) : U i ⊆ S := (hUB i).trans (hsub i)
  have hUC (i : ι) : (colorGraph c k).IsClique (U i : Set V) := (hcl i).subset (hUB i)
  have htwo (x : V) (hx : x ∈ S) : (univ.filter fun i => x ∈ U i).card=2 := by
    have heq : univ.filter (fun i => x ∈ U i) = f ⟨x,hx⟩ := by ext i; simp [U,hx]
    rw [heq,hfc]
  have total := (double_cover_counts S U hUS htwo).1
  have size (i : ι) (_ : i ∈ univ) : (U i).card ≤ r := by
    by_contra! hlarge
    obtain ⟨C,hCU,hn⟩ := exists_subset_card_eq (s := U i) hlarge.le
    exact h.no_clique hb htr C (hCU.trans (hUS i)) ⟨(hUC i).subset hCU,hn⟩
  have upper := sum_le_sum (s := univ) size
  simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,total,h.card_eq] at upper
  have hgt : 2*t < Fintype.card ι := by
    by_contra! hsmall
    nlinarith only [upper,Nat.mul_le_mul_right r hsmall]
  by_contra! hshort
  exact h.no_odd_double_clique_cover hb ht htr U (by omega) hUS hUC htwo

end Erdos617
