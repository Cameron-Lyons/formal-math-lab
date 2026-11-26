module

public import Erdos617.GoodSquareBlocks
public import Erdos617.QuadraticObstruction
public import Erdos617.LineVariance

@[expose] public section

namespace Erdos617

open Finset SimpleGraph
open scoped Classical

private theorem soft_part_size {x a r s D e : ℕ} (positive : 0<a) (hr : 2≤r) (sr : s+1=r)
    (energy : 2*x^2≤a*(2*e+r*x))
    (cost : D+s*x=e+(s.choose 2+1)*a+(s-1)) :
    (r+2)*x≤(r+2)*(r+1)*a+2*D := by
  have en : 2*(x:ℤ)^2≤a*(2*e+r*x) := by exact_mod_cast energy
  have scaled : (a:ℤ)*(3*r*x)≤a*(2*e+2*a*r^2) := by
    nlinarith only [en,sq_nonneg ((x:ℤ)-a*r)]
  have tangent : 3*r*x≤2*e+2*a*r^2 := by
    exact_mod_cast le_of_mul_le_mul_left scaled (show (0:ℤ)<a by omega)
  have ch := congrArg (a*·) (twice_choose_two s)
  have pred : s-1+1=s := by omega
  rw [←sr] at tangent ⊢
  nlinarith only [tangent,cost,ch,pred,show 0≤a by omega,show 0≤s-1 by omega]

/-- A color with small excess on a one-step square has almost all its rank
in clique components. The total size deficit of these cliques is also small. -/
theorem square_rank_soft_profile {V : Type*} [DecidableEq V] {r : ℕ}
    (c : Sym2 V → Fin r) (k : Fin r) (hr : 6≤r) (_hb : Balanced c)
    (U : Finset V) (sz : U.card=(r-1)^2+1) (cap : rankOn (colorGraph c k) U≤r-1)
    (no : ∀ A⊆U, ¬(colorGraph c k).IsNClique r A) {b : ℕ}
    (large : 6*(b+1)<r)
    (budget : blockEdges (colorGraph c k) U≤(r-1)*(r-1).choose 2+2*(r-1)-1+b*(r-2)) :
    let G := colorGraph c k
    ∃ Q : Finset (Finset V), Q.biUnion id=U ∧
      (↑Q : Set (Finset V)).PairwiseDisjoint id ∧ (∀ A∈Q,RankInseparable G A) ∧
      (∑ A∈Q,rankOn G A)=r-1 ∧ rankOn G U=r-1 ∧
      (let L:=Q.filter fun A => rankOn G A=1
       let H:=Q \ L
       L.card+(∑ A∈H,rankOn G A)=r-1 ∧ (∑ A∈H,rankOn G A)≤2*(b+1) ∧
       (∀ A∈L,A.card≤r-1) ∧ (∑ A∈L,(r-1-A.card))≤6*(b+1)) ∧
      (inducedEdgeSet G U \ Q.biUnion (inducedEdgeSet G)).card≤b*(r-2) := by
  classical
  let g := b*(r-2)
  let G := colorGraph c k
  let s := r-1
  have sr : s+1=r := by dsimp [s]; omega
  have sU : U.card=s*s+1 := by simpa [s,pow_two] using sz
  change rankOn G U≤s at cap
  change blockEdges G U≤s*s.choose 2+2*s-1+g at budget
  obtain ⟨Q,hu,hd,hi,hs⟩ := exists_rank_partition G U
  let F := inducedEdgeSet G U \ Q.biUnion (inducedEdgeSet G)
  let D (A : Finset V) := blockEdges G A+(s.choose 2+1)*rankOn G A+(s-1)-s*A.card
  have ident (A : Finset V) (ha : A∈Q) :
      D A+s*A.card=blockEdges G A+(s.choose 2+1)*rankOn G A+(s-1) :=
    Nat.sub_add_cancel (rank_density G A (hi A ha) s)
  have total := sum_congr (s₁:=Q) rfl ident
  have cut := boundary_edge_count G U Q hu.le hd
  change F.card+(∑ A∈Q,blockEdges G A)=blockEdges G U at cut
  have count := card_biUnion hd
  simp only [id_eq,hu] at count
  simp only [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,Nat.cast_id,←count,hs] at total
  have lower (A : Finset V) (ha : A∈Q) : 1≤rankOn G A := (hi A ha).rank_pos
  have ones := sum_le_sum lower
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,hs] at ones
  have pc := ones.trans cap
  have ac := Nat.mul_le_mul_left (s.choose 2+1) cap
  have eqQ := congrArg ((s-1)*·) (Nat.sub_add_cancel pc)
  rw [Nat.mul_add,Nat.mul_comm (s-1) Q.card] at eqQ
  have numeric : s*U.card+s*s.choose 2+s=(s.choose 2+1)*s+(s-1)*s+2*(s*s.choose 2+s) := by
    have mulch := congrArg (s*·) (twice_choose_two s)
    have mp := congrArg (·*s) (show s-1+1=s by omega)
    rw [sU]
    nlinarith only [mulch,mp]
  have spos : 0<s := by omega
  have money : F.card+(∑ A∈Q,D A)+(s-1)*(s-Q.card)≤s-1+g := by omega
  let L := Q.filter fun A => rankOn G A=1
  let H := Q \ L
  let T := ∑ A∈H,rankOn G A
  have sl : L⊆Q := filter_subset ..
  have sh : H⊆Q := sdiff_subset
  have hsize : L.card+H.card=Q.card := by rw [Nat.add_comm]; exact card_sdiff_add_card_eq_card sl
  have split (f : Finset V → ℕ) : (∑ A∈L,f A)+(∑ A∈H,f A)=∑ A∈Q,f A := by
    rw [Nat.add_comm]
    exact sum_sdiff sl
  have ranks : L.card+T=rankOn G U := by
    have sum := split (rankOn G)
    have ones : (∑ A∈L,rankOn G A)=L.card := by
      rw [sum_congr rfl (fun A hA => (mem_filter.mp hA).2)]
      simp [L]
    simpa only [ones,hs] using sum
  have lb (A : Finset V) (ha : A∈H) : 2≤rankOn G A := by
    have pos := lower A (sh ha)
    have ne : rankOn G A≠1 := fun eq => (mem_sdiff.mp ha).2 (mem_filter.mpr ⟨sh ha,eq⟩)
    omega
  have two := sum_le_sum lb
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at two
  change H.card*2≤T at two
  have loss : s-Q.card≤b+1 := by
    apply Nat.le_of_mul_le_mul_left (c:=s-1) _ (by omega)
    have pred : s-1=r-2 := by omega
    change F.card+(∑ A∈Q,D A)+(s-1)*(s-Q.card)≤s-1+b*(r-2) at money
    rw [pred] at money ⊢
    rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm (r-2) b]
    omega
  have mass : T≤2*(b+1) := by omega
  have inside (A : Finset V) (ha : A∈Q) : A⊆U := biUnion_subset.mp hu.le _ ha
  have short (A : Finset V) (ha : A∈L) : A.card≤s := by
    by_contra! big
    obtain ⟨B,sub,card⟩ := exists_subset_card_eq (show r≤A.card by omega)
    have cl := rank_one_clique G (mem_filter.mp ha).2
    exact no B (sub.trans (inside A (sl ha))) ⟨cl.subset sub,card⟩
  have soft (A : Finset V) (ha : A∈H) : (r+2)*A.card≤(r+2)*(r+1)*rankOn G A+2*D A :=
    soft_part_size (hi A (sh ha)).rank_pos (by omega) sr (no_full_part_energy (by omega : 0<r)
      (fun C hC => no C (hC.trans (inside A (sh ha))))) (ident A (sh ha))
  have allSoft := sum_le_sum soft
  simp only [sum_add_distrib,←mul_sum] at allSoft
  change (r+2)*(∑ A∈H,A.card)≤(r+2)*(r+1)*T+2*(∑ A∈H,D A) at allSoft
  have osc : (∑ A∈H,D A)≤(b+1)*(r+2) := by
    have subD := sum_le_sum_of_subset_of_nonneg sh (f:=D) (fun _ _ _ => Nat.zero_le _)
    have step := Nat.mul_le_mul_left (b+1) (show r-2≤r+2 by omega)
    have eq : (b+1)*(r-2)=g+(s-1) := by dsimp [g]; rw [Nat.add_mul,Nat.one_mul,show s-1=r-2 by omega]
    omega
  have limits : (∑ A∈H,A.card)≤(r+1)*T+2*(b+1) := by
    apply Nat.le_of_mul_le_mul_left (c:=r+2) _ (by omega)
    nlinarith only [allSoft,osc]
  have deficits (A : Finset V) (ha : A∈L) : s-A.card+A.card=s := Nat.sub_add_cancel (short A ha)
  have total := sum_congr (s₁:=L) rfl deficits
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id] at total
  have sum := split card
  rw [←count] at sum
  have rk : rankOn G U=s := by
    by_contra ne
    have less : (L.card+T)*s≤(s-1)*s := Nat.mul_le_mul_right s (by omega)
    have ps := congrArg (·*s) (show s-1+1=s by omega)
    have tr := congrArg (T*·) sr
    nlinarith only [less,ps,tr,limits,total,sum,large,sU,sr,mass,Nat.zero_le (∑ A∈L,(s-A.card))]
  have rankSum : (∑ A∈Q,rankOn G A)=s := hs.trans rk
  have defcap : (∑ A∈L,(s-A.card))+1≤2*T+2*(b+1) := by
    have used := congrArg (·*s) (ranks.trans rk)
    have core := congrArg (T*·) sr
    nlinarith only [sum,total,limits,used,sU,core]
  have needed : 1≤s-Q.card := by
    by_contra! enough
    have zero : T=0 := by omega
    have empty : H=∅ := card_eq_zero.mp (by omega)
    have allRows : Q=L := by
      apply Subset.antisymm _ sl
      exact sdiff_eq_empty_iff_subset.mp empty
    have uc := sum_le_sum short
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at uc
    rw [←allRows,←count,sU] at uc
    have max := Nat.mul_le_mul_right s pc
    omega
  have cross : F.card≤g := by
    have d := Nat.mul_le_mul_left (s-1) needed
    rw [Nat.mul_one] at d
    omega
  have final : (∑ A∈L,(s-A.card))≤6*(b+1) := by omega
  exact ⟨Q,hu,hd,hi,rankSum,rk,⟨ranks.trans rk,mass,short,final⟩,cross⟩

/-- In the quadratic local-rank range, none of the remaining components
has more than r vertices per unit of rank, improving the total row deficit. -/
theorem square_rank_profile {V : Type*} [DecidableEq V] {r : ℕ}
    (c : Sym2 V → Fin r) (k : Fin r) (hr : 6≤r) (hb : Balanced c)
    (U : Finset V) (sz : U.card=(r-1)^2+1) (cap : rankOn (colorGraph c k) U≤r-1)
    (no : ∀ A⊆U, ¬(colorGraph c k).IsNClique r A) {b : ℕ}
    (large : 1000*(2*(b+1))^2<r)
    (budget : blockEdges (colorGraph c k) U≤(r-1)*(r-1).choose 2+2*(r-1)-1+b*(r-2)) :
    let G := colorGraph c k
    ∃ Q : Finset (Finset V), Q.biUnion id=U ∧
      (↑Q : Set (Finset V)).PairwiseDisjoint id ∧ (∀ A∈Q,RankInseparable G A) ∧
      (∑ A∈Q,rankOn G A)=r-1 ∧ rankOn G U=r-1 ∧
      (let L:=Q.filter fun A => rankOn G A=1
       let H:=Q \ L
       L.card+(∑ A∈H,rankOn G A)=r-1 ∧ (∑ A∈H,rankOn G A)≤2*(b+1) ∧
       (∀ A∈L,A.card≤r-1) ∧ (∑ A∈L,(r-1-A.card))≤2*(b+1) ∧
       (∀ A∈H,A.card≤rankOn G A*r)) ∧
      (inducedEdgeSet G U \ Q.biUnion (inducedEdgeSet G)).card≤b*(r-2) := by
  classical
  let G := colorGraph c k
  let s := r-1
  obtain ⟨Q,hu,hd,hi,sumrk,rk,data,cross⟩ := square_rank_soft_profile c k hr hb U sz cap no
    (b:=b) (by nlinarith only [large,Nat.zero_le (b*b),Nat.zero_le b]) budget
  let L := Q.filter fun A => rankOn G A=1
  let H := Q \ L
  let T := ∑ A∈H,rankOn G A
  obtain ⟨ranks,mass,short,_⟩ := data
  change L.card+T=s at ranks
  change T≤2*(b+1) at mass
  have room (A : Finset V) (ha : A∈H) : A.card≤rankOn G A*r := by
    have lim : rankOn G A≤T := single_le_sum (f:=rankOn G) (fun _ _ => Nat.zero_le _) ha
    have sq := Nat.pow_le_pow_left (lim.trans mass) 2
    by_contra! big
    obtain ⟨B,sub,sizeB⟩ := exists_subset_card_eq (show rankOn G A*r+1≤A.card by omega)
    obtain ⟨I,inB,ind⟩ := independent_in_subset_of_quadratic_palette (by omega : 3≤r) hb
      (show 1000*(rankOn G A)^2<r by omega) sizeB k
    have absurd := card_le_rankOn (colorGraph c k) (inB.trans sub) ind.isIndepSet
    rw [ind.card_eq] at absurd
    exact Nat.not_succ_le_self _ absurd
  have lim := sum_le_sum room
  rw [←sum_mul] at lim
  change (∑ A∈H,A.card)≤T*r at lim
  have count := card_biUnion hd
  simp only [id_eq,hu] at count
  have split := sum_sdiff (s₂:=Q) (s₁:=L) (filter_subset ..) (f:=card)
  change (∑ A∈H,A.card)+(∑ A∈L,A.card)=∑ A∈Q,A.card at split
  rw [←count] at split
  have total := sum_congr (s₁:=L) rfl (fun A ha => Nat.sub_add_cancel (short A ha))
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id] at total
  change (∑ A∈L,(s-A.card))+(∑ A∈L,A.card)=L.card*s at total
  change U.card=s^2+1 at sz
  have dp : (∑ A∈L,(s-A.card))+1≤T := by
    nlinarith only [lim,split,total,sz,congrArg (·*s) ranks,congrArg (T*·) (show s+1=r by dsimp [s]; omega)]
  exact ⟨Q,hu,hd,hi,sumrk,rk,⟨ranks,mass,short,(Nat.le_add_right _ 1).trans (dp.trans mass),room⟩,cross⟩

end Erdos617
