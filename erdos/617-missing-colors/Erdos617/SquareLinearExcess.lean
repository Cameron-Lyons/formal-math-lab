module

public import Erdos617.PartitionCrossing
public import Erdos617.SquareTuran
public import Erdos617.RankDensity
public import Erdos617.GlobalCliqueEnergy
public import Mathlib.Data.Nat.Sqrt

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] [Fintype V] {r : ℕ} {c : Sym2 V → Fin r} {k : Fin r}
local notation "G" => colorGraph c k

/-- When an r-clique partition is almost edge-minimal, the shortfall of each
part from r−2 is controlled by its contribution to the edge excess. -/
private theorem deficit_sqrt {r p n e v g : ℕ} (rp : p+2=r) (pos : 0<p)
    (slack : v+p*n=e+(p.choose 2+1)+(p-1)) (clique : 2*e+n=n*n) (small : v≤g) :
    r-n≤2*g.sqrt+3 := by
  by_cases h : p≤n
  · omega
  obtain ⟨a,pa⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt (Nat.lt_of_not_ge h))
  have identity : a*a+a=2*v := by
    rw [pa] at slack
    have ch := twice_choose_two p
    rw [pa] at ch
    have pred : n+a-1+1=n+a := by omega
    nlinarith only [slack,clique,ch,pred]
  have sq := Nat.lt_succ_sqrt g
  by_contra! large
  have bound : 2*(g.sqrt+1)≤a := by omega
  have both := Nat.mul_le_mul bound bound
  nlinarith only [both,sq,identity,small,Nat.zero_le a,Nat.zero_le (g.sqrt*g.sqrt)]

private theorem few_spokes_from_excess {r d g : ℕ} (hr : 15*g+7<r) (hd : d≤2*g.sqrt+3) :
    (d+1)*g.sqrt+(d+1).choose 2<r-1 := by
  have q := Nat.sqrt_le g
  have small := Nat.sqrt_le_self g
  have mult := Nat.mul_le_mul (show d+1≤2*g.sqrt+4 by omega) (show 2*g.sqrt+d≤4*g.sqrt+3 by omega)
  have ch := twice_choose_two (d+1)
  nlinarith only [q,small,mult,ch,hr,Nat.sub_add_cancel (show 1≤r by omega)]

/-- Every induced color graph on a square of side r−1 exceeds its ordinary
Turán edge floor by a term linear in r. -/
theorem square_linear_edge_excess (hr : 5≤r) (hn : Fintype.card V=r^2+1) (hb : Balanced c)
    (U : Finset V) (sz : U.card=(r-1)^2+1) {g : ℕ}
    (upper : blockEdges G U≤r*(r-2).choose 2+2*(r-2)+g) : r≤15*g+7 := by
  classical
  by_contra! large
  let p := r-2
  have rp : p+2=r := by dsimp [p]; omega
  have pos : 0<p := by omega
  have size : U.card=p*r+2 := by rw [sz,←rp,show p+2-1=p+1 by omega]; ring
  let E := blockEdges G U
  let base := r*p.choose 2+2*p
  change E≤base+g at upper
  obtain ⟨P,hu,hd,hi,hs⟩ := exists_rank_partition G U
  let F := inducedEdgeSet G U \ P.biUnion (inducedEdgeSet G)
  let D (A : Finset V) := blockEdges G A+(p.choose 2+1)*rankOn G A+(p-1)-p*A.card
  have ident (A : Finset V) (ha : A∈P) :
      D A+p*A.card=blockEdges G A+(p.choose 2+1)*rankOn G A+(p-1) :=
    Nat.sub_add_cancel (rank_density G A (hi A ha) p)
  have total := sum_congr (s₁:=P) rfl ident
  have cut := boundary_edge_count G U P hu.le hd
  change F.card+(∑ A∈P,blockEdges G A)=E at cut
  have count := card_biUnion hd
  simp only [id_eq,hu] at count
  simp only [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,Nat.cast_id,←count,hs] at total
  have alpha : rankOn G U≤r := by
    obtain ⟨I,hiI,ind,n⟩ := exists_max_indep G U
    rw [←n]; exact ind.card_le_indepNum.trans (balanced_indepNum_le _ hb _)
  have ones := sum_le_sum (s:=P) (f:=fun _ => 1) (fun A hA => (hi A hA).rank_pos)
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,hs] at ones
  have pc := ones.trans alpha
  have ac := Nat.mul_le_mul_left (p.choose 2+1) alpha
  have eqP := congrArg ((p-1)*·) (Nat.sub_add_cancel pc)
  rw [Nat.mul_add,Nat.mul_comm (p-1) P.card] at eqP
  have numeric : p*(p*r+2)+base=(p.choose 2+1)*r+(p-1)*r+2*base := by
    dsimp [base]
    have pred : p-1+1=p := by omega
    have m := congrArg (r*·) pred
    have ch := congrArg (r*·) (twice_choose_two p)
    nlinarith only [m,ch]
  rw [size] at total
  have money : F.card+(∑ A∈P,D A)+(p-1)*(r-P.card)≤g := by omega
  have full : P.card=r := by
    by_contra! ne
    have fact := Nat.mul_le_mul_left (p-1) (show 1≤r-P.card by omega)
    rw [Nat.mul_one] at fact
    omega
  have one (A : Finset V) (ha : A∈P) : rankOn G A=1 := by
    apply Eq.symm
    have lower (X : Finset V) (hX : X∈P) : 1≤rankOn G X := (hi X hX).rank_pos
    apply (sum_eq_sum_iff_of_le lower).mp _ A ha
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,hs,full]
    omega
  have cl (A : Finset V) (ha : A∈P) := rank_one_clique G (one A ha)
  have cap (A : Finset V) (ha : A∈P) : A.card≤r := by
    obtain ⟨x,hx⟩ := (hi A ha).nonempty
    exact (card_le_pointClique G A (cl A ha) x hx).trans (balanced_pointClique_le (by omega) c hb k x)
  have short (A : Finset V) (ha : A∈P) : r-A.card≤2*g.sqrt+3 := by
    have row := ident A ha
    rw [one A ha,Nat.mul_one] at row
    have eq : 2*blockEdges G A+A.card=A.card*A.card := by
      rw [←block_degree_sum]
      have loc (x : V) (hx : x∈A) : (A.filter ((colorGraph c k).Adj x)).card=A.card-1 := by
        have same : A.filter ((colorGraph c k).Adj x)=A.erase x := by
          ext y
          simp only [mem_filter,mem_erase]
          exact ⟨fun h => ⟨h.2.ne.symm,h.1⟩,fun h => ⟨h.2,cl A ha hx h.2 h.1.symm⟩⟩
        rw [same,card_erase_of_mem hx]
      rw [sum_congr rfl loc,sum_const,nsmul_eq_mul]
      have step := congrArg (A.card*·) (Nat.sub_add_cancel (card_pos.mpr (hi A ha).nonempty : 1≤A.card))
      simpa [Nat.mul_add] using step
    have bound := single_le_sum (f:=D) (fun _ _ => Nat.zero_le _) ha
    apply deficit_sqrt rp pos row eq
    omega
  let B (i : P) := i.val
  have covered : univ.biUnion B=U := by ext z; simpa [B] using Finset.ext_iff.mp hu z
  have crossing {i j : P} (ne : i≠j) {x y : V} (hx : x∈B i) (hy : y∈B j) (e : (colorGraph c k).Adj x y) : s(x,y)∈F := by
    have inside (A : Finset V) (ha : A∈P) : A⊆U := (biUnion_subset.mp hu.le) A ha
    refine mem_sdiff.mpr ⟨(mem_inducedEdgeSet G).mpr ⟨inside _ i.prop hx,inside _ j.prop hy,e⟩,?_⟩
    intro internal
    obtain ⟨A,hA,edge⟩ := mem_biUnion.mp internal
    obtain ⟨xa,ya,_⟩ := (mem_inducedEdgeSet G).mp edge
    have eq {Y Z : Finset V} (yP : Y∈P) (zP : Z∈P) {v : V} (vy : v∈Y) (vz : v∈Z) : Y=Z :=
      by_contra (fun h => Finset.disjoint_left.mp (hd yP zP h) vy vz)
    exact ne (Subtype.ext ((eq i.prop hA hx xa).trans (eq hA j.prop ya hy)))
  have bound := clique_partition_cross_floor (ι:=P) ((Fintype.card_coe _).trans full) hn hb B covered
    (fun _ _ ne => hd (Subtype.prop _) (Subtype.prop _) (fun eq => ne (Subtype.ext eq)))
    (fun i => cl _ i.prop) (fun i => cap _ i.prop) (Nat.succ_pos g.sqrt)
    (fun i => by simpa only [B,Nat.succ_eq_add_one,Nat.add_sub_cancel] using few_spokes_from_excess large (short _ i.prop)) F
    (fun _ _ h _ hx _ hy e => crossing h hx hy e)
  have low := Nat.lt_succ_sqrt' g
  omega

/-- Rounded additive form of the linear excess on each codimension-one square. -/
theorem square_linear_edge_floor (hr : 5≤r) (hn : Fintype.card V=r^2+1) (hb : Balanced c)
    (U : Finset V) (sz : U.card=(r-1)^2+1) :
    r*(r-2).choose 2+2*(r-2)+(r+7)/15≤blockEdges G U := by
  let d := fun e : Sym2 U => c (e.map Subtype.val)
  have floor := square_turan_floor (colorGraph d k) (by omega : 3≤r) ((Fintype.card_coe U).trans sz)
    (balanced_indepNum_le _ (balanced_pullback c hb (Function.Embedding.subtype (·∈U))) k)
  rw [←color_blockEdges_eq] at floor
  let base := r*(r-2).choose 2+2*(r-2)
  let e := blockEdges G U
  change base≤e at floor
  have excess := square_linear_edge_excess (k:=k) hr hn hb U sz (g:=e-base) (by change e≤base+(e-base); omega)
  change base+(r+7)/15≤e
  omega

end Erdos617
