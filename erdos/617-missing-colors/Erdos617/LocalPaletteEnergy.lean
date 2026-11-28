module

public import Erdos617.LocalCliqueEnergy
public import Erdos617.NestedObstruction

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

/-- Rounding the uniform clique bound at an order one above a multiple
of the independence bound. -/
theorem clique_energy_floor {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {a q : ℕ} (hrank : G.indepNum ≤ a) (hn : Fintype.card V=q*a+1) :
    2*q*Fintype.card V+2*q+1 ≤ (∑ x,G.degree x)+Fintype.card V+∑ x,pointClique G x := by
  have h := (card_square_le_local_clique_energy G _ (card_le_pointClique G)).trans
    (Nat.mul_le_mul_right _ hrank)
  apply Nat.succ_le_of_lt
  by_contra! hle
  have bad := h.trans (Nat.mul_le_mul_left a hle)
  rw [hn] at bad
  nlinarith only [bad]

theorem balanced_indepNum_le {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r) : (colorGraph c k).indepNum ≤ r := by
  obtain ⟨I,hi⟩ := (colorGraph c k).exists_isNIndepSet_indepNum
  by_contra! high
  obtain ⟨T,hT,ht⟩ := exists_subset_card_eq (s:=I) (show r+1≤I.card by rw [hi.card_eq]; omega)
  obtain ⟨x,hx,y,hy,hxy,he⟩ := hb T ht k
  exact hi.isIndepSet (hT hx) (hT hy) hxy ⟨hxy,he⟩

/-- Upper bounds for the independence and local clique numbers on the obstruction. -/
theorem MinimalObstruction.point_clique_caps {V : Type*} [DecidableEq V] {r t : ℕ}
    {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V} (h : MinimalObstruction c k t S)
    (hb : Balanced c) (htr : t < r) :
    let G := colorGraph (fun e : Sym2 S => c (Sym2.map Subtype.val e))
    (G k).indepNum ≤ t ∧ (∀ x, pointClique (G k) x ≤ r-1) ∧
      ∀ j ≠ k, ∀ x, pointClique (G j) x ≤ t := by
  classical
  intro G
  have ha : (G k).indepNum ≤ t := by
    obtain ⟨T,hT⟩ := (G k).exists_isNIndepSet_indepNum
    obtain ⟨A,hAS,hi⟩ := lift_independent_subset c k S ⟨T,hT⟩
    have bound := card_le_rankOn _ hAS hi.isIndepSet
    rwa [hi.card_eq,h.rank_eq (by omega)] at bound
  refine ⟨ha,?_,?_⟩
  · intro x
    obtain ⟨C,_,hC⟩ := exists_pointClique (G k) x
    by_contra! high
    obtain ⟨D,hD,hn⟩ := exists_subset_card_eq (s:=C) (show r≤C.card by rw [hC.card_eq]; omega)
    let incl := Function.Embedding.subtype (·∈S)
    apply h.no_clique hb htr (D.map incl) (fun _ hy => D.property_of_mem_map_subtype hy)
    refine ⟨?_,(card_map ..).trans hn⟩
    intro u hu v hv huv
    obtain ⟨a,ha,ea⟩ := mem_map.mp hu
    obtain ⟨b,hb',eb⟩ := mem_map.mp hv
    subst u v
    exact ⟨huv,(hC.isClique (hD ha) (hD hb') (fun e => huv (congrArg incl e))).2⟩
  · intro j hj x
    obtain ⟨C,_,hC⟩ := exists_pointClique (G j) x
    have hind : (G k).IsIndepSet (C : Set S) := fun _ hy _ hz hne he =>
      hj ((hC.isClique hy hz hne).2.symm.trans he.2)
    exact hC.card_eq ▸ hind.card_le_indepNum.trans ha

theorem sum_palette_degrees {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (c : Sym2 V → Fin r) :
    (∑ j, ∑ x,(colorGraph c j).degree x) = Fintype.card V*(Fintype.card V-1) := by
  rw [sum_comm]
  simp [sum_colorGraph_degree]

/-- The total shortfall in local clique sizes across all vertices and colors
is less than (t−3)|S|. The displayed form retains the integer rounding gain. -/
theorem MinimalObstruction.total_local_clique_deficit {V : Type*} [DecidableEq V] {r t : ℕ}
    {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V} (h : MinimalObstruction c k t S)
    (hb : Balanced c) (htr : t < r) :
    let G := colorGraph (fun e : Sym2 S => c (Sym2.map Subtype.val e))
    (∑ x : S, ((r-1-pointClique (G k) x) + ∑ j∈univ.erase k,(t-pointClique (G j) x))) +
      3*S.card+3*r ≤ t*S.card+2*t+2 := by
  classical
  intro G
  let d (j : Fin r) := ∑ x,(G j).degree x
  let w (j : Fin r) := ∑ x,pointClique (G j) x
  let F := univ.erase k
  let n := Fintype.card S
  have nc : n=S.card := Fintype.card_coe _
  have hn : n=t*r+1 := nc.trans h.card_eq
  have fsize : F.card=r-1 := by simp [F]
  have ⟨ha,ck,cj⟩ := h.point_clique_caps hb htr
  have first := clique_energy_floor (G k) ha (by simpa [Nat.mul_comm r t] using hn : n=r*t+1)
  change 2*r*n+2*r+1 ≤ d k+n+w k at first
  have per (j : Fin r) (_ : j∈F) : 2*t*n+2*t+1 ≤ d j+n+w j :=
    clique_energy_floor (G j) (balanced_indepNum_le _ (balanced_pullback c hb
      (Function.Embedding.subtype (·∈S))) j) hn
  have rest := sum_le_sum per
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id,fsize] at rest
  have degrees := sum_erase_add univ d (mem_univ k)
  change (∑ j∈F,d j)+d k=∑ j,∑ x,(G j).degree x at degrees
  rw [sum_palette_degrees] at degrees
  change (∑ j∈F,d j)+d k=n*(n-1) at degrees
  have ckSum := sum_congr (s₁:=univ) rfl (fun (x:S) _ =>
    Nat.sub_add_cancel (ck x))
  change (∑ x:S,((r-1-pointClique (G k) x)+pointClique (G k) x))=∑ _ : S,(r-1) at ckSum
  rw [sum_add_distrib,sum_const,nsmul_eq_mul] at ckSum
  change (∑ x:S,(r-1-pointClique (G k) x))+w k=n*(r-1) at ckSum
  have cjSum (j : Fin r) (hj : j∈F) :
      (∑ x:S,(t-pointClique (G j) x))+w j=n*t := by
    change (∑ x:S,(t-pointClique (G j) x))+(∑ x:S,pointClique (G j) x)=n*t
    rw [←sum_add_distrib]
    calc
      _ = ∑ _ : S,t := sum_congr rfl (fun x _ => Nat.sub_add_cancel (cj j (mem_erase.mp hj).1 x))
      _ = n*t := by simp [n]
  have foreign := sum_congr rfl cjSum
  rw [sum_add_distrib,sum_const,nsmul_eq_mul,fsize] at foreign
  rw [sum_add_distrib,Finset.sum_comm (s:=univ) (t:=F),←nc]
  have hr' : r-1+1=r := by omega
  have nn : n-1=t*r := by omega
  rw [nn] at degrees
  have mult : (r-1)*t+t=t*r := by rw [←Nat.succ_mul,Nat.succ_eq_add_one,hr',Nat.mul_comm]
  have hcoeff : (r-1)*n+n=r*n := by rw [←Nat.succ_mul,Nat.succ_eq_add_one,hr']
  nlinarith only [first,rest,foreign,ckSum,degrees,mult,hcoeff,hn,hr',
    congrArg (·*n) mult,congrArg (n*·) hr']

theorem MinimalObstruction.exists_local_clique_deficit {V : Type*} [DecidableEq V] {r t : ℕ}
    {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V} (h : MinimalObstruction c k t S)
    (hr : 3 ≤ r) (hb : Balanced c) (htr : t < r) :
    let G := colorGraph (fun e : Sym2 S => c (Sym2.map Subtype.val e))
    ∃ x : S, (r-1-pointClique (G k) x) + (∑ j∈univ.erase k, (t-pointClique (G j) x)) ≤ t-4 := by
  classical
  intro G
  by_contra! high
  have hn := h.total_local_clique_deficit hb htr
  have low := sum_le_sum (s:=univ) (f:=fun _ : S => t-4+1) fun x _ => high x
  simp only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_coe,Nat.cast_id] at low
  have ⟨j,_,W,_,_,_,half,_,two,_⟩ := h.exists_nested_product_obstruction hr hb htr
  have ht : t-4+1+3=t := by omega
  have step := congrArg (S.card*·) ht
  rw [Nat.mul_add,Nat.mul_comm S.card t] at step
  change _+3*S.card+3*r ≤ t*S.card+2*t+2 at hn
  dsimp only [G] at low
  nlinarith only [step,low,hn,htr,hr]

end Erdos617
