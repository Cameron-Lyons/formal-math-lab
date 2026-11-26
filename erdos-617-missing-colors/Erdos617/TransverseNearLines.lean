module

public import Erdos617.FullCliquePropagation
public import Erdos617.GlobalCliqueEnergy

@[expose] public section

namespace Erdos617

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ} {c : Sym2 V → Fin r}

/-- Many almost-full foreign cliques cross any two prescribed transverse full
lines. Distinct cliques in the family meet in at most one vertex. -/
theorem many_near_full_transversals (hr : 5≤r) (hn : Fintype.card V=r^2+1) (hb : Balanced c)
    {i j : Fin r} (ij : i≠j) (C D : Finset V) (hC : (colorGraph c i).IsNClique r C)
    (hD : (colorGraph c j).IsNClique r D) (meet : (C∩D).card=1) :
    ∃ T : Finset (Finset V), 2*((r-1)*(r-3))≤2*T.card+(r-1)^2+1 ∧
      (∀ A∈T, (A∩C).card=1 ∧ (A∩D).card=1 ∧ r-1≤A.card ∧ A.card≤r ∧
        ∃ k, k≠i ∧ k≠j ∧ (colorGraph c k).IsClique (A:Set V)) ∧
      ∀ A∈T,∀ B∈T,A≠B → (A∩B).card≤1 := by
  classical
  let F := univ.erase i
  let Z := F ×ˢ C
  let Y := D \ C
  let Z' := (F.erase j) ×ˢ C
  let N (k : Fin r) (x : V) := C.filter ((colorGraph c k).Adj x)
  let B (a : Fin r × V) := Cᶜ.filter fun x => N a.1 x={a.2}
  let A (a : Fin r × V) := insert a.2 (B a)
  have cpos (a : Fin r × V) (ha : a∈Z) : a.2∈C := (mem_product.mp ha).2
  have ki (a : Fin r × V) (ha : a∈Z) : a.1≠i := (mem_erase.mp (mem_product.mp ha).1).1
  have nz (a : Fin r × V) (ha : a∈Z) : a.2∉B a := fun h => (mem_compl.mp (mem_filter.mp h).1) (cpos a ha)
  have ord (a : Fin r × V) (ha : a∈Z) : (A a).card=(B a).card+1 := card_insert_of_notMem (nz a ha)
  have clique (a : Fin r × V) (ha : a∈Z) : (colorGraph c a.1).IsClique (A a:Set V) :=
    private_clique _ C (full_clique_maximum_in_other_color c hb (ki a ha) hC) _ (cpos a ha)
  have acap (a : Fin r × V) (ha : a∈Z) : (A a).card≤r := by
    exact (card_le_pointClique _ _ (clique a ha) a.2 (mem_insert_self ..)).trans (balanced_pointClique_le (by omega) c hb _ _)
  have atC (a : Fin r × V) (ha : a∈Z) : A a∩C={a.2} := by
    ext x
    have := cpos a ha
    simp only [A,B,mem_inter,mem_insert,mem_filter,mem_compl,mem_singleton]
    grind
  have fcount (K : Finset (Fin r)) (x : V) (out : x∈Cᶜ) :
      ((K ×ˢ C).filter fun a => x∈B a).card =
        ∑ k∈K,(C.filter fun v => N k x={v}).card := by
    calc
      _ = ∑ a∈K ×ˢ C, if x∈B a then 1 else 0 := by simp only [sum_boole,Nat.cast_id]
      _ = _ := ?_
    rw [Finset.sum_product]
    apply sum_congr rfl
    intro k _
    simp [B,out,sum_boole]
  have fsize : F.card=r-1 := by simp [F]
  have zsize : Z.card=(r-1)*r := by rw [card_product,fsize,hC.card_eq]
  have csize := C.card_add_card_compl
  rw [hC.card_eq,hn] at csize
  have ysize : Y.card=r-1 := by
    have sp := card_sdiff_add_card_inter D C
    rw [inter_comm D C,meet,hD.card_eq] at sp
    change (D\C).card=r-1
    omega
  have spokes (x : V) (out : x∈Cᶜ) : r-2≤(Z.filter fun a => x∈B a).card := by
    rw [fcount _ x out]
    have := full_line_unique_spoke_count (by omega : 2≤r) c hb i hC (mem_compl.mp out)
    dsimp [N,F]
    omega
  have all := sum_le_sum spokes
  have flip : (∑ x∈Cᶜ,(Z.filter fun a => x∈B a).card) = ∑ a∈Z,(Cᶜ.filter (·∈B a)).card :=
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun x a => x∈B a)
  rw [flip] at all
  have atB (a : Fin r × V) : Cᶜ.filter (·∈B a)=B a := by ext x; simp [B]
  simp only [atB,sum_const,nsmul_eq_mul,Nat.cast_id] at all
  have absent : (∑ a∈Z,(r-(A a).card))≤(r-1)^2+1 := by
    have sum := sum_congr (s₁:=Z) rfl (fun a ha => show r-(A a).card+((B a).card+1)=r by
      rw [←ord a ha,Nat.sub_add_cancel (acap a ha)])
    simp only [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,zsize] at sum
    have rs : r-1+1=r := by omega
    have cs : Cᶜ.card=(r-1)*r+1 := by nlinarith only [csize,congrArg (·*r) rs]
    rw [cs] at all
    nlinarith only [all,sum,congrArg ((r-1)*r*·) (show r-2+2=r by omega),
      congrArg ((r-1)*·) rs,rs]
  have subsetZ : Z'⊆Z := product_subset_product (erase_subset ..) (Subset.rfl)
  have kj (a : Fin r × V) (ha : a∈Z') : a.1≠j := (mem_erase.mp (mem_product.mp ha).1).1
  have oneD (a : Fin r × V) (ha : a∈Z') : (A a∩D).card≤1 := by
    apply card_le_one.mpr
    intro x hx y hy
    by_contra ne
    exact (kj a ha) (((clique a (subsetZ ha)) (mem_inter.mp hx).1 (mem_inter.mp hy).1 ne).2.symm.trans
      (hD.isClique (mem_inter.mp hx).2 (mem_inter.mp hy).2 ne).2)
  have enough (y : V) (hy : y∈Y) : r-3≤(Z'.filter fun a => y∈B a).card := by
    have out := mem_compl.mpr (mem_sdiff.mp hy).2
    have prev := spokes y out
    rw [fcount _ y out] at prev ⊢
    have jF : j∈F := mem_erase.mpr ⟨ij.symm,mem_univ _⟩
    have sp := sum_erase_add F (fun k => (C.filter fun v => N k y={v}).card) jF
    have lim : (C.filter fun v => N j y={v}).card≤1 := by
      apply card_le_one.mpr
      intro x hx z hz
      exact singleton_inj.mp ((mem_filter.mp hx).2.symm.trans (mem_filter.mp hz).2)
    omega
  let ZT := Z'.filter fun a => (A a∩D).Nonempty
  have zt : ZT⊆Z := (filter_subset ..).trans subsetZ
  have breadth : (r-1)*(r-3)≤ZT.card := by
    have sum := sum_le_sum enough
    have flipY : (∑ x∈Y,(Z'.filter fun a => x∈B a).card) = ∑ a∈Z',(Y.filter (·∈B a)).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun x a => x∈B a)
    rw [flipY] at sum
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id,ysize] at sum
    have point (a : Fin r × V) (ha : a∈Z') : (Y.filter (·∈B a)).card≤(if (A a∩D).Nonempty then 1 else 0) := by
      have sub : Y.filter (·∈B a)⊆A a∩D := by
        intro x hx
        exact mem_inter.mpr ⟨mem_insert_of_mem (mem_filter.mp hx).2,(mem_sdiff.mp (mem_filter.mp hx).1).1⟩
      split
      · exact (card_le_card sub).trans (oneD a ha)
      · rename_i empty
        rw [not_nonempty_iff_eq_empty.mp empty] at sub
        simpa using card_le_card sub
    exact sum.trans (by simpa only [sum_boole,Nat.cast_id,ZT] using sum_le_sum point)
  let T := ZT.filter fun a => r-1≤(A a).card
  have almost : 2*((r-1)*(r-3))≤2*T.card+(r-1)^2+1 := by
    have thin := sum_le_sum (s:=ZT\T) (f:=fun _ => 2) (g:=fun a => r-(A a).card) (fun a ha => by
      have ne := (mem_sdiff.mp ha).2
      have short : ¬r-1≤(A a).card := fun h => ne (mem_filter.mpr ⟨(mem_sdiff.mp ha).1,h⟩)
      omega)
    have sub : ZT\T⊆Z := sdiff_subset.trans zt
    have all := sum_le_sum_of_subset_of_nonneg sub (f:=fun a => r-(A a).card) (by simp)
    have seen := card_sdiff_add_card_eq_card (filter_subset (fun a => r-1≤(A a).card) ZT)
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at thin
    change (ZT\T).card+T.card=ZT.card at seen
    omega
  have tzt : T⊆ZT := filter_subset ..
  have tk {a : Fin r × V} (ha : a∈T) := (mem_filter.mp (tzt ha)).1
  have monoInj : Set.InjOn A (↑T : Set _) := by
    intro a ha b hb' eq
    have aZ := zt (tzt ha)
    have bZ := zt (tzt hb')
    have same := (atC a aZ).symm.trans ((congrArg (·∩C) eq).trans (atC b bZ))
    have np := (mem_filter.mp ha).2
    obtain ⟨x,hx,y,hy,ne⟩ := one_lt_card.mp (by omega : 1<(A a).card)
    exact Prod.ext (((clique a aZ) hx hy ne).2.symm.trans ((clique b bZ) (eq ▸ hx) (eq ▸ hy) ne).2)
      (singleton_inj.mp same)
  refine ⟨T.image A,by rwa [card_image_of_injOn monoInj],?_,?_⟩
  · intro K hK
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hK
    have d := card_pos.mpr (mem_filter.mp (tzt ha)).2
    have le := oneD a (tk ha)
    exact ⟨by rw [atC _ (zt (tzt ha)),card_singleton],by omega,(mem_filter.mp ha).2,acap a (zt (tzt ha)),
      a.1,ki a (zt (tzt ha)),kj a (tk ha),clique a (zt (tzt ha))⟩
  · intro K hK L hL different
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hK
    obtain ⟨b,hb',rfl⟩ := mem_image.mp hL
    apply card_le_one.mpr
    intro x hx y hy
    by_contra ne
    have color := ((clique a (zt (tzt ha))) (mem_inter.mp hx).1 (mem_inter.mp hy).1 ne).2.symm.trans
      ((clique b (zt (tzt hb'))) (mem_inter.mp hx).2 (mem_inter.mp hy).2 ne).2
    have anchor (z : V) (za : z∈A a) (zb : z∈A b) : a.2=b.2 := by
      by_cases zc : z∈C
      · have h := mem_inter.mpr ⟨za,zc⟩
        rw [atC _ (zt (tzt ha))] at h
        have h' := mem_inter.mpr ⟨zb,zc⟩
        rw [atC _ (zt (tzt hb'))] at h'
        exact (mem_singleton.mp h).symm.trans (mem_singleton.mp h')
      · have na := (mem_filter.mp ((mem_insert.mp za).resolve_left (fun eq => zc (eq ▸ cpos a (zt (tzt ha)))))).2
        have nb := (mem_filter.mp ((mem_insert.mp zb).resolve_left (fun eq => zc (eq ▸ cpos b (zt (tzt hb')))))).2
        rw [color] at na
        exact singleton_inj.mp (na.symm.trans nb)
    exact different (congrArg A (Prod.ext color (anchor _ (mem_inter.mp hx).1 (mem_inter.mp hx).2)))

end Erdos617
