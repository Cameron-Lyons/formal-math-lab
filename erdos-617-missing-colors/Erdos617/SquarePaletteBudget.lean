module

public import Erdos617.BlockEdgeBound
public import Erdos617.ColorCounts
public import Erdos617.PaletteMatching

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

theorem square_budget_identity (s : ℕ) (hs : 1≤s) :
    (s-1)*(s*s.choose 2+2*s-1)+2*((s+1)*(s-1).choose 2+2*(s-1))+1=(s^2+1).choose 2 := by
  obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  rw [Nat.succ_eq_add_one,Nat.add_sub_cancel]
  have g : (q+1)*(q+1).choose 2+2*(q+1)-1=(q+1)*(q+1).choose 2+2*q+1 := by omega
  rw [g]
  nlinarith only [twice_choose_two ((q+1)^2+1),
    congrArg (fun v => q*(q+1)*v) (twice_choose_two (q+1)),
    congrArg (fun v => 2*(q+2)*v) (twice_choose_two q)]

/-- On s²+1 vertices, if every color of an (s+1)-coloring has the stated
strict edge floor and no (s+1)-clique, at least three colors admit
independent sets of order s+1. -/
theorem square_palette_three_large_indep {V : Type*} [Fintype V] [DecidableEq V] {s : ℕ}
    (hs : 5≤s) (hn : Fintype.card V=s^2+1) (c : Sym2 V → Fin (s+1))
    (hcl : ∀ k,(colorGraph c k).CliqueFree (s+1))
    (he : ∀ k,(s+1)*(s-1).choose 2+2*(s-1)<(colorGraph c k).edgeFinset.card) :
    3≤(univ.filter fun k => s<(colorGraph c k).indepNum).card := by
  classical
  let bad := univ.filter fun k => s<(colorGraph c k).indepNum
  let E (k : Fin (s+1)) := (colorGraph c k).edgeFinset.card
  let G := s*s.choose 2+2*s-1
  let B := (s+1)*(s-1).choose 2+2*(s-1)
  by_contra! few
  change bad.card<3 at few
  have all : bad.card+badᶜ.card=s+1 := by simp
  obtain ⟨P,sub,count⟩ := exists_subset_card_eq (s:=badᶜ) (show s-1≤badᶜ.card by omega)
  have two : Pᶜ.card=2 := by
    have size : P.card+Pᶜ.card=s+1 := by simp
    omega
  have high (k : Fin (s+1)) (hk : k∈P) : G≤E k := by
    have rank : (colorGraph c k).indepNum≤s := by
      by_contra! wrong
      exact (mem_compl.mp (sub hk)) (mem_filter.mpr ⟨mem_univ _,wrong⟩)
    exact edge_bound_of_clique_and_indep_caps _ (by omega : 2≤s)
      (by simpa [pow_two] using hn : Fintype.card V=s*s+1)
      (fun I hi => by have lim := hi.isIndepSet.card_le_indepNum; rw [hi.card_eq] at lim; omega)
      (hcl k)
  have good := sum_le_sum high
  have rest := sum_le_sum (s:=Pᶜ) (f:=fun _ => B+1) (g:=E) (fun k _ => he k)
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,count] at good
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,two] at rest
  have sum := sum_add_sum_compl P E
  change (∑ k∈P,E k)+(∑ k∈Pᶜ,E k)=∑ k,(colorGraph c k).edgeFinset.card at sum
  rw [sum_color_edges,hn] at sum
  have iden : (s-1)*G+2*B+1=(s^2+1).choose 2 := square_budget_identity s (by omega)
  omega

/-- A singleton is present on every (s+1)-set exactly when its color graph
has independence number at most s. -/
theorem hitsPalette_singleton_iff_indepNum {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} (c : Sym2 V → Fin r) (s : ℕ) (k : Fin r) :
    HitsPalette c s {k} ↔ (colorGraph c k).indepNum≤s := by
  classical
  let G := colorGraph c k
  constructor
  · intro hit
    by_contra! large
    obtain ⟨I,ind⟩ := G.exists_isNIndepSet_indepNum
    obtain ⟨T,sub,sz⟩ := exists_subset_card_eq (s:=I) (show s+1≤I.card by rw [ind.card_eq]; exact large)
    obtain ⟨x,hx,y,hy,ne,eq⟩ := hit T sz
    exact ind.isIndepSet (sub hx) (sub hy) ne ⟨ne,mem_singleton.mp eq⟩
  · intro cap T sz
    by_contra! miss
    have ind : G.IsIndepSet (T : Set V) := fun x hx y hy ne e => miss x hx y hy ne (mem_singleton.mpr e.2)
    have low := ind.card_le_indepNum.trans cap
    omega

open scoped Classical in
/-- The three large independence numbers give three separate failed
singleton groups in the one-pair descent test. -/
theorem square_palette_three_avoidable {V : Type*} [Fintype V] [DecidableEq V] {s : ℕ}
    (hs : 5≤s) (hn : Fintype.card V=s^2+1) (c : Sym2 V → Fin (s+1))
    (hcl : ∀ k,(colorGraph c k).CliqueFree (s+1))
    (he : ∀ k,(s+1)*(s-1).choose 2+2*(s-1)<(colorGraph c k).edgeFinset.card) :
    3≤(univ.filter fun k => ¬HitsPalette c s {k}).card := by
  simpa only [hitsPalette_singleton_iff_indepNum,not_le] using square_palette_three_large_indep hs hn c hcl he

end Erdos617
