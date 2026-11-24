import Erdos617.OddPrivateRows
import Erdos617.OddBags
import Erdos617.ClusterMultiplicity
import Mathlib.Data.Nat.Sqrt

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] {r t : ℕ} {c : Sym2 V → Fin r}
variable {k : Fin r} {S I : Finset V}

/-- Edges between two disjoint monochromatic cliques are scarce in the same
color. In particular, a complete monochromatic rectangle across the two rows
is bounded in terms of their size deficits. -/
private theorem rectangle_cap (hb : Balanced c) (A B U W : Finset V)
    (hA : (colorGraph c k).IsClique (A : Set V)) (hB : (colorGraph c k).IsClique (B : Set V))
    (hab : Disjoint A B) (hu : U⊆A) (hw : W⊆B)
    (hadj : ∀ u∈U, ∀ w∈W,(colorGraph c k).Adj u w)
    (ha : A.card≤r) (hb' : B.card≤r) :
    U.card*W.card ≤ r + (r-A.card)*(r-B.card) := by
  classical
  let R := A×ˢB \ U×ˢW
  have cap := foreign_pair_budget c hb k (A∪B) R (by
    intro x hx y hy hne hc
    have noA : ¬(x∈A ∧ y∈A) := fun h => hc (hA h.1 h.2 hne).2
    have noB : ¬(x∈B ∧ y∈B) := fun h => hc (hB h.1 h.2 hne).2
    have noU : ¬(x∈U ∧ y∈W) := fun h => hc (hadj x h.1 y h.2).2
    have noW : ¬(x∈W ∧ y∈U) := fun h => hc (hadj y h.2 x h.1).symm.2
    simp only [R,mem_sdiff,mem_product,mem_union] at *
    tauto)
  have sub : U×ˢW ⊆ A×ˢB := product_subset_product hu hw
  have count := card_sdiff_add_card_eq_card sub
  change R.card + (U×ˢW).card = (A×ˢB).card at count
  rw [card_product,card_product] at count
  rw [card_union_of_disjoint hab] at cap
  have p : 0<r := lt_of_le_of_lt (Nat.zero_le k.val) k.isLt
  have h₁ := Nat.sub_add_cancel ha
  have h₂ := Nat.sub_add_cancel hb'
  have h₃ : r-1+1=r := by omega
  nlinarith only [cap,count,congrArg ((A.card+B.card)*·) h₃,congrArg (r*·) h₃,
    congrArg (·*(r-B.card)) h₁, congrArg (A.card*·) h₂,congrArg (r*·) h₂,h₁,h₂]

/-- If all vertices of T have their closed anchor-neighborhood contained in J,
then the independence number on T is at most |J|. -/
theorem MinimalObstruction.anchor_rank_bound (h : MinimalObstruction c k t S)
    (hIS : I⊆S) (ind : (colorGraph c k).IsNIndepSet t I) (J T : Finset V) (hJI : J⊆I)
    (hTS : T⊆S) (hits : ∀ x∈T, I.filter (fun u => x=u ∨ (colorGraph c k).Adj x u) ⊆ J) :
    rankOn (colorGraph c k) T ≤ J.card := by
  classical
  let G := colorGraph c k
  obtain ⟨H,hH,hi,hc⟩ := exists_max_indep G T
  have apart : Disjoint H (I\J) := disjoint_left.mpr (by
    intro x hx hxJ
    exact (mem_sdiff.mp hxJ).2 (hits x (hH hx) (mem_filter.mpr ⟨(mem_sdiff.mp hxJ).1, Or.inl rfl⟩)))
  have merged : G.IsIndepSet (↑(H∪(I\J)) : Set V) := by
    intro x hx y hy hxy edge
    rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
    · exact hi hx hy hxy edge
    · exact (mem_sdiff.mp hy).2 (hits x (hH hx) (mem_filter.mpr ⟨(mem_sdiff.mp hy).1,Or.inr edge⟩))
    · exact (mem_sdiff.mp hx).2 (hits y (hH hy) (mem_filter.mpr ⟨(mem_sdiff.mp hx).1,Or.inr edge.symm⟩))
    · exact ind.isIndepSet (mem_sdiff.mp hx).1 (mem_sdiff.mp hy).1 hxy edge
  have total := card_le_rankOn G (union_subset (hH.trans hTS) (sdiff_subset.trans hIS)) merged
  have hr : 0 < r := lt_of_le_of_lt (Nat.zero_le k.val) k.isLt
  change _ ≤ rankOn (colorGraph c k) S at total
  rw [h.rank_eq hr,card_union_of_disjoint apart,hc] at total
  have count := card_sdiff_add_card_eq_card hJI
  rw [ind.card_eq] at count
  change rankOn G T ≤ J.card
  omega

/-- A vertex with precisely two anchor hits must be close to one of the two
private cliques, uniformly in the number of anchors. -/
private theorem close_of_binary_hits (h : MinimalObstruction c k t S) (hb : Balanced c)
    (hIS : I⊆S) (ind : (colorGraph c k).IsNIndepSet t I) (B : I → Finset V)
    (hc : ∀ i, B i ⊆ S ∧ (colorGraph c k).IsClique (B i : Set V) ∧ (B i).card<r)
    (hd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hrow : ∀ i, B i=S.filter (fun x => I.filter (fun y => x=y ∨ (colorGraph c k).Adj x y)={i.val}))
    {d : ℕ} (hδ : ∀ i, r-(B i).card ≤ d) (x : V) (hx : x∈S\univ.biUnion B)
    (h2 : (I.filter ((colorGraph c k).Adj x)).card=2) :
    ∃ i, ((B i).filter fun y => ¬(colorGraph c k).Adj x y).card ≤ Nat.sqrt (r+d^2) := by
  classical
  let G := colorGraph c k
  let N (v : V) := I.filter fun u => v=u ∨ G.Adj v u
  obtain ⟨a,b,hab,hpair⟩ := card_eq_two.mp h2
  have hi : {a,b} ⊆ I := hpair ▸ filter_subset .. 
  let i : I := ⟨a,hi (by simp)⟩
  let j : I := ⟨b,hi (by simp)⟩
  have hij : i≠j := fun eq => hab (congrArg Subtype.val eq)
  have hxI : x∉I := by
    intro hm
    have ha : G.Adj x a := (mem_filter.mp (show a∈I.filter (G.Adj x) from hpair ▸ mem_insert_self ..)).2
    exact ind.isIndepSet hm i.prop ha.ne ha
  have nx : N x={a,b} := by
    rw [←hpair]
    ext y
    by_cases hy : y∈I
    · simp [N,hy,show x≠y from fun eq => hxI (eq ▸ hy),G]
    · simp [N,hy]
  have own (l : I) {y : V} (hy : y∈B l) : N y={l.val} := by
    rw [hrow l] at hy
    exact (mem_filter.mp hy).2
  let U := (B i).filter fun y => ¬G.Adj x y
  let W := (B j).filter fun y => ¬G.Adj x y
  have rect (y : V) (hy : y∈U) (z : V) (hz : z∈W) : G.Adj y z := by
    obtain ⟨hyi,xy⟩ := mem_filter.mp hy
    obtain ⟨hzj,xz⟩ := mem_filter.mp hz
    have xx {u : V} {l : I} (hu : u∈B l) : x≠u := by
      rintro rfl
      exact (mem_sdiff.mp hx).2 (mem_biUnion.mpr ⟨l,mem_univ _,hu⟩)
    have yz : y≠z := fun eq => disjoint_left.mp (hd hij) hyi (eq ▸ hzj)
    by_contra no
    let T : Finset V := {x,y,z}
    have hT : T⊆S := insert_subset (mem_sdiff.mp hx).1 (insert_subset ((hc i).1 hyi) (singleton_subset_iff.mpr ((hc j).1 hzj)))
    have rk := h.anchor_rank_bound hIS ind {a,b} T hi hT (by
      intro u hu
      rcases mem_insert.mp hu with rfl | hu
      · exact nx.le
      rcases mem_insert.mp hu with rfl | hu
      · exact (own i hyi).le.trans (singleton_subset_iff.mpr (mem_insert_self ..))
      · obtain rfl := mem_singleton.mp hu
        exact (own j hzj).le.trans (singleton_subset_iff.mpr (by simp [j])))
    have hind : G.IsIndepSet (T : Set V) := by
      have cl : Gᶜ.IsNClique 3 T := SimpleGraph.is3Clique_triple_iff.mpr
        ⟨⟨xx hyi,xy⟩,⟨xx hzj,xz⟩,⟨yz,no⟩⟩
      exact (G.isNClique_compl.mp cl).isIndepSet
    have count := card_le_rankOn G (Subset.rfl : T⊆T) hind
    have valT : T.card=3 := by simp [T,xx hyi,xx hzj,yz]
    rw [valT] at count
    simp only [card_pair hab] at rk
    change rankOn G T ≤ 2 at rk
    omega
  have bound := rectangle_cap hb (B i) (B j) U W (hc i).2.1 (hc j).2.1 (hd hij)
    (filter_subset ..) (filter_subset ..) rect (hc i).2.2.le (hc j).2.2.le
  have limit := Nat.mul_le_mul (hδ i) (hδ j)
  simp only [←pow_two] at limit
  by_contra! big
  have l := Nat.mul_le_mul (Nat.succ_le_of_lt (big i)) (Nat.succ_le_of_lt (big j))
  change _ ≤ U.card*W.card at l
  have := Nat.lt_succ_sqrt' (r+d^2)
  nlinarith only [this,l,bound,limit]

/-- Whenever every exception has two anchor neighbors, a bound on the largest
private-row deficit bounds the entire palette, independently of the rank.
The adjacent private rows cannot absorb all the exceptional vertices. -/
theorem MinimalObstruction.binary_row_deficit_bound (h : MinimalObstruction c k t S) (hb : Balanced c)
    (hIS : I⊆S) (ind : (colorGraph c k).IsNIndepSet t I) (B : I → Finset V)
    (hc : ∀ i, B i ⊆ S ∧ (colorGraph c k).IsClique (B i : Set V) ∧ (B i).card<r)
    (hd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hrow : ∀ i, B i=S.filter (fun x => I.filter (fun y => x=y ∨ (colorGraph c k).Adj x y)={i.val}))
    (h2 : ∀ x∈S\univ.biUnion B, (I.filter ((colorGraph c k).Adj x)).card=2)
    (d : ℕ) (hδ : ∀ i, r-(B i).card ≤ d) : r ≤ 4*(d+1)^2+2 := by
  classical
  let G := colorGraph c k
  let X := S \ univ.biUnion B
  let q := Nat.sqrt (r+d^2)
  let miss (x : V) (i : I) := ((B i).filter fun y => ¬G.Adj x y).card
  let Y (i : I) := X.filter fun x => miss x i ≤ q
  have cover : S ⊆ univ.biUnion (fun i => B i ∪ Y i) := by
    intro x hx
    by_cases mem : x∈univ.biUnion B
    · obtain ⟨i,_,hi⟩ := mem_biUnion.mp mem
      exact mem_biUnion.mpr ⟨i,mem_univ _,mem_union_left _ hi⟩
    · have hxX := mem_sdiff.mpr ⟨hx,mem⟩
      obtain ⟨i,hi⟩ := close_of_binary_hits h hb hIS ind B hc hd hrow hδ x hxX (h2 x hxX)
      exact mem_biUnion.mpr ⟨i,mem_univ _,mem_union_right _ (mem_filter.mpr ⟨hxX,hi⟩)⟩
  obtain ⟨i,hi⟩ : ∃ i, r < (B i ∪ Y i).card := by
    by_contra! small
    have ub := (card_le_card cover).trans
      (card_biUnion_le_card_mul univ _ r (fun i _ => small i))
    rw [h.card_eq,card_univ,Fintype.card_coe,ind.card_eq] at ub
    omega
  have dis : Disjoint (B i) (Y i) := disjoint_left.mpr (by
    intro x hB hY
    exact (mem_sdiff.mp (mem_filter.mp hY).1).2 (mem_biUnion.mpr ⟨i,mem_univ _,hB⟩))
  rw [card_union_of_disjoint dis] at hi
  have rowSize := (hc i).2.2
  obtain ⟨A,hAY,hA⟩ := exists_subset_card_eq (s:=Y i) (n:=r-(B i).card+1) (by omega)
  have cap := enlarged_clique_budget c hb k (B i) A (hc i).2.1 (dis.mono_right hAY)
  have lim := sum_le_sum (s:=A) (f:=fun x => miss x i) (g:=fun _ => q)
    (fun x hx => (mem_filter.mp (hAY hx)).2)
  rw [sum_const,nsmul_eq_mul] at lim
  simp only [Nat.cast_id] at lim
  change (r-1)*((B i).card+A.card) ≤ (r-1)*r+(∑ x∈A,miss x i)+A.card^2 at cap
  have sz : (B i).card+A.card=r+1 := by omega
  rw [sz,Nat.mul_add,Nat.mul_one] at cap
  have dlim := hδ i
  have aa : A.card≤d+1 := by omega
  have prod := Nat.mul_le_mul_right q aa
  have sq := Nat.pow_le_pow_left aa 2
  have small : r-1 ≤ (d+1)*q+(d+1)^2 := by omega
  have sqrt := Nat.sqrt_le' (r+d^2)
  change q^2 ≤ r+d^2 at sqrt
  have hdd := Nat.pow_le_pow_left (Nat.le_succ d) 2
  rcases le_total (d+1) q with l | l
  · obtain ⟨u,hu⟩ := Nat.exists_eq_add_of_le l
    have gap := congrArg (·^2) hu
    have step := congrArg ((d+1)*·) hu
    nlinarith only [small,sqrt,hdd,gap,step,Nat.zero_le (u^2),Nat.sub_add_cancel (show 1≤r by have := k.isLt; omega)]
  · have step := Nat.mul_le_mul_left (d+1) l
    nlinarith only [small,step,Nat.sub_add_cancel (show 1≤r by have := k.isLt; omega),Nat.zero_le ((d+1)^2)]

/-- At the odd endpoint a sparse core has a binary-anchor decomposition with
mean private-row deficit less than three and an individual deficit d with
4(d+1)²+2 ≥ r. Both conclusions describe the same disjoint cliques. -/
theorem odd_endpoint_row_deficit_range [Fintype V] {s : ℕ} (hs : 1 ≤ s) (hr : r=2*s+1)
    (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c)
    (hsmall : ∀ (k : Fin r) (a : ℕ), a ≤ s → ∀ W : Finset V, ¬MinimalObstruction c k a W) :
    ∃ (k : Fin r) (S I : Finset V) (B : I → Finset V),
      MinimalObstruction c k (s+1) S ∧ (colorGraph c k).IsNIndepSet (s+1) I ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      (∀ i, B i ⊆ S ∧ (colorGraph c k).IsClique (B i : Set V) ∧ (B i).card<r) ∧
      (∑ i, (r-(B i).card)) ≤ 3*s ∧
      (∃ i, r-2≤(B i).card) ∧ ∃ i, r ≤ 4*(r-(B i).card+1)^2+2 := by
  classical
  obtain ⟨k,j,hkj,hk,hj⟩ := odd_endpoint_two_sparse hs hr hn c hb hsmall
  obtain ⟨S,P,h,hp,hpu,hpd,hpc⟩ := odd_endpoint_of_sparse_color hs hr hn c hb k hk (hsmall k)
  obtain ⟨_,Q,_,hq,_,hqd,hqc⟩ := odd_endpoint_of_sparse_color hs hr hn c hb j hj (hsmall j)
  obtain ⟨C,_,B,X,hi,hd,hcl,hrow,hX,h2,sumX,limit,lg⟩ :=
    odd_endpoint_private_rows hs hr hb hkj hk h P Q hp hpu hpd hpc hq hqd hqc
  let I:=C∩S
  have pos : (univ : Finset I).Nonempty := card_pos.mp (by rw [card_univ,Fintype.card_coe,hi.card_eq]; omega)
  obtain ⟨i,_,mx⟩ := univ.exists_max_image (fun a : I => r-(B a).card) pos
  subst X
  exact ⟨k,S,I,B,h,hi,hd,hcl,Nat.le_of_succ_le_succ (sumX.le.trans limit),lg,i,h.binary_row_deficit_bound hb inter_subset_right hi B hcl hd
    hrow h2 _ (fun a => mx a (mem_univ _))⟩

end Erdos617
