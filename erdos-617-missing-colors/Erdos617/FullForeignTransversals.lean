import Erdos617.ForeignTotalBudget
import Erdos617.LineVariance

namespace Erdos617

open Finset SimpleGraph
open scoped Classical

private theorem full_part_account {t x a e D : ℕ} (ht : 2≤t) (ha : 1≤a)
    (size : x≤t ∨ 2≤a) (energy : 2*x^2≤a*(2*e+(t+1)*x))
    (price : D+t*x=e+(t.choose 2+1)*a+(t-1)) :
    (t-1)*(x+a+4) ≤ (t-1)*((t+4)*a+(if a=1 ∧ x=t then 1 else 0))+4*D := by
  by_cases one : a=1
  · subst a
    have le : x≤t := size.resolve_right (by decide)
    by_cases eq : x=t
    · rw [eq]; simp
    · simp [eq]
      have mult := Nat.mul_le_mul_left (t-1) (show x+1+4≤t+4 by omega)
      omega
  · have en : 2*(x:ℤ)^2≤a*(2*e+(t+1)*x) := by exact_mod_cast energy
    have scal : (a:ℤ)*(3*t*x)≤a*(2*e+2*a*t^2+x) := by
      nlinarith only [en,sq_nonneg ((x:ℤ)-a*t)]
    have tang : 3*t*x≤2*e+2*a*t^2+x := by
      exact_mod_cast le_of_mul_le_mul_left scal (show (0:ℤ)<a by omega)
    have pred : t-1+1=t := by omega
    have linear : (t-1)*(x+2)≤(t-1)*(t+2)*a+2*D := by
      nlinarith only [tang,price,congrArg (a*·) (twice_choose_two t),
        congrArg (·*(t*a)) pred,congrArg (·*x) pred,congrArg (·*a) pred]
    simp only [one,false_and,ite_false,Nat.add_zero]
    have two := Nat.mul_le_mul_left (t-1) (show 2≤a by omega)
    nlinarith only [linear,two,Nat.zero_le D]

private theorem full_foreign_count {V : Type*} [DecidableEq V] {r t : ℕ} {c : Sym2 V → Fin r}
    {k : Fin r} {S : Finset V} (h : MinimalObstruction c k t S) (ht : 2≤t)
    {j : Fin r} (jk : j≠k) (P : Finset (Finset V)) (cover : P.biUnion id=S)
    (dis : (↑P : Set (Finset V)).PairwiseDisjoint id) (parts : ∀ A∈P,RankInseparable (colorGraph c j) A)
    (ranks : (∑ A∈P,rankOn (colorGraph c j) A)≤r) :
    let G := colorGraph c j
    let F := P.filter fun A => rankOn G A=1 ∧ A.card=t
    4*(r*t.choose 2+t)+(t-1)*(r+1) ≤ 4*blockEdges G S+(t-1)*F.card := by
  classical
  let G := colorGraph c j
  let F := P.filter fun A => rankOn G A=1 ∧ A.card=t
  let D (A : Finset V) := blockEdges G A+(t.choose 2+1)*rankOn G A+(t-1)-t*A.card
  have price (A) (ha : A∈P) : D A+t*A.card=blockEdges G A+(t.choose 2+1)*rankOn G A+(t-1) :=
    Nat.sub_add_cancel (rank_density G A (parts A ha) t)
  have block (A : Finset V) (ha : A∈P) := biUnion_subset.mp cover.le A ha
  have free (A : Finset V) (ha : A∈P) (B : Finset V) (sub : B⊆A) : ¬G.IsNClique (t+1) B := by
    intro cl
    exact h.free B (sub.trans (block A ha)) ⟨fun _ hx _ hy ne e => jk ((cl.isClique hx hy ne).2.symm.trans e.2),cl.card_eq⟩
  have law (A : Finset V) (ha : A∈P) :=
    full_part_account ht (parts A ha).rank_pos
      (show A.card≤t ∨ 2≤rankOn G A from by
        by_cases one : rankOn G A=1
        · exact Or.inl (h.foreign_rank_one_cap jk (block A ha) one)
        · exact Or.inr (by have pos := (parts A ha).rank_pos; change 0<rankOn G A at pos; omega))
      (no_full_part_energy (show 0<t+1 by omega) (free A ha)) (price A ha)
  have l := sum_le_sum law
  have p := sum_congr (s₁:=P) rfl price
  have cnt := card_biUnion dis
  simp only [id_eq,cover,h.card_eq] at cnt
  have ifs : (∑ A∈P,if rankOn G A=1 ∧ A.card=t then 1 else 0)=F.card := by rw [←sum_filter]; simp [F]
  change (∑ A∈P,if rankOn (colorGraph c j) A=1 ∧ A.card=t then 1 else 0)=F.card at ifs
  simp only [←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id,ifs,←cnt] at l p
  have cov := boundary_edge_count G S P cover.le dis
  have lower : (∑ A∈P,blockEdges G A)≤blockEdges G S := by omega
  change (∑ A∈P,rankOn G A)≤r at ranks
  change 4*(r*t.choose 2+t)+(t-1)*(r+1)≤4*blockEdges G S+(t-1)*F.card
  have coef := Nat.mul_le_mul_left ((t-1)*(t+3)+4*(t.choose 2+1)) ranks
  have pred : t-1+1=t := by omega
  have ch := congrArg (r*·) (twice_choose_two t)
  have tr := congrArg (·*(t*r)) pred
  have rr := congrArg (·*r) pred
  have natural := congrArg (·*(∑ A∈P,rankOn G A)) pred
  nlinarith only [l,p,lower,coef,pred,ch,tr,rr,natural]

/-- The foreign colors of an obstruction have many disjoint cliques of
order exactly t. Every such clique is a maximum independent set of the
obstruction color. The displayed bound is positive throughout the half range. -/
theorem MinimalObstruction.full_foreign_transversals {V : Type*} [DecidableEq V] {r t : ℕ}
    {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V} (h : MinimalObstruction c k t S)
    (ht : 2≤t) (htr : t<r) (hb : Balanced c) :
    ∃ C : Fin r → Finset (Finset V),
      (∀ j≠k,(↑(C j) : Set (Finset V)).PairwiseDisjoint id ∧
        ∀ A∈C j,A⊆S ∧ (colorGraph c j).IsNClique t A) ∧
      (r-1)*(r+1) < (∑ j∈univ.erase k,(C j).card)+2*(r-1)*(t-1) := by
  classical
  obtain ⟨P,hP,_,_⟩ := h.exists_foreign_total_rank_budget_strict ht htr hb
  let C (j : Fin r) := (P j).filter fun A => rankOn (colorGraph c j) A=1 ∧ A.card=t
  let F := univ.erase k
  let E (j : Fin r) := blockEdges (colorGraph c j) S
  let B := r*t.choose 2+t
  refine ⟨C,?_,?_⟩
  · intro j _
    obtain ⟨hu,hd,_⟩ := hP j
    refine ⟨fun _ ha _ hb ne => hd (mem_filter.mp ha).1 (mem_filter.mp hb).1 ne,?_⟩
    intro A ha
    obtain ⟨hp,one,sz⟩ := mem_filter.mp ha
    exact ⟨biUnion_subset.mp hu.le A hp,rank_one_clique _ one,sz⟩
  have per (j : Fin r) (hj : j∈F) : 4*B+(t-1)*(r+1)≤4*E j+(t-1)*(C j).card := by
    obtain ⟨cover,dis,parts,rk,cap⟩ := hP j
    exact full_foreign_count h ht (mem_erase.mp hj).1 (P j) cover dis parts (rk.le.trans cap)
  have all := sum_le_sum per
  have fc : F.card=r-1 := by simp [F]
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,fc,sum_add_distrib,←mul_sum] at all
  have sum := sum_color_edges (fun e : Sym2 S => c (e.map Subtype.val))
  simp_rw [←color_blockEdges_eq] at sum
  change (∑ j,E j)=(Fintype.card S).choose 2 at sum
  rw [←sum_erase_add _ _ (mem_univ k),Fintype.card_coe,h.card_eq,Nat.add_comm] at sum
  let W := (∑ j∈F,E j)-(r-1)*B
  have floors := sum_le_sum (s:=F) (fun j _ => induced_color_edge_count_of_balanced (by omega) c hb S h.card_eq j)
  simp_rw [←color_blockEdges_eq] at floors
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,fc] at floors
  change (r-1)*B≤∑ j∈F,E j at floors
  have id : (r-1)*B+W=∑ j∈F,E j := by dsimp [W]; omega
  have money := foreign_total_budget_arithmetic ht htr (h.rank_edge_bound (by omega)) id.le sum
  change 2*W<(r-1)*(t-1)*(t-1) at money
  change (r-1)*(r+1)<(∑ j∈F,(C j).card)+2*(r-1)*(t-1)
  apply Nat.lt_of_mul_lt_mul_left (a:=t-1)
  nlinarith only [money,all,congrArg (4*·) id]

/-- A single foreign color has at least r−2t+4 disjoint maximum
independent sets of the obstruction color. In the half range, this
always supplies at least three. -/
theorem MinimalObstruction.packed_full_foreign_color {V : Type*} [DecidableEq V] {r t : ℕ}
    {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V} (h : MinimalObstruction c k t S)
    (ht : 2≤t) (htr : t<r) (hb : Balanced c) :
    ∃ j≠k,∃ P : Finset (Finset V), (↑P : Set (Finset V)).PairwiseDisjoint id ∧
      (∀ A∈P,A⊆S ∧ (colorGraph c j).IsNClique t A ∧ (colorGraph c k).IsNIndepSet t A) ∧
      r+4≤2*t+P.card := by
  classical
  obtain ⟨C,hC,many⟩ := h.full_foreign_transversals ht htr hb
  let F := univ.erase k
  have fc : F.card=r-1 := by simp [F]
  have openF : F.Nonempty := card_pos.mp (by rw [fc]; omega)
  obtain ⟨j,hj,largest⟩ := F.exists_max_image (fun l => (C l).card) openF
  have jk := (mem_erase.mp hj).1
  refine ⟨j,jk,C j,(hC j jk).1,?_,?_⟩
  · intro A hA
    obtain ⟨sub,cl⟩ := (hC j jk).2 A hA
    exact ⟨sub,cl,⟨fun _ hx _ hy ne e => jk ((cl.isClique hx hy ne).2.symm.trans e.2),cl.card_eq⟩⟩
  · have bound := sum_le_sum largest
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id,fc] at bound
    change (r-1)*(r+1)<(∑ l∈F,(C l).card)+2*(r-1)*(t-1) at many
    have result : r+1<(C j).card+2*(t-1) := by
      apply Nat.lt_of_mul_lt_mul_left (a:=r-1)
      nlinarith only [many,bound]
    omega

end Erdos617
