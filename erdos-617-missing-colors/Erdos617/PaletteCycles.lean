import Erdos617.PaletteDescent
import Erdos617.RankTwoCycle

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] {r : ℕ} {c : Sym2 V → Fin r} {k j : Fin r}

/-- With foreign independence number two, the ends of a two-edge path in color
k are joined in the foreign color. -/
theorem path_chord_of_rank_two {W : Finset V} (hjk : j≠k)
    (h₂ : rankOn (colorGraph c j) W=2) {x y z : V} (hx : x∈W) (hy : y∈W) (hz : z∈W)
    (hxy : (colorGraph c k).Adj x y) (hxz : (colorGraph c k).Adj x z) (hyz : y≠z) :
    c s(y,z)=j := by
  by_contra no
  let H := colorGraph c j
  have pair : H.IsIndepSet (({y,z} : Finset V) : Set V) := by
    rw [←isClique_compl,coe_insert,coe_singleton,isClique_pair]
    exact fun _ => ⟨hyz,fun e => no e.2⟩
  have triple := independent_insert_of_nonadjacent H pair x (by
    intro u hu e
    rcases mem_insert.mp hu with rfl | hu
    · exact hjk (e.2.symm.trans hxy.2)
    · obtain rfl := mem_singleton.mp hu
      exact hjk (e.2.symm.trans hxz.2))
  have ub := card_le_rankOn H (insert_subset hx (insert_subset hy (singleton_subset_iff.mpr hz))) triple
  change rankOn H W=2 at h₂
  simp [hxy.ne,hxz.ne,hyz,h₂] at ub

private theorem rank_two_majority {ι : Type*} [DecidableEq ι] (F : Finset ι) (b : ι → ℕ)
    (hmin : ∀ j∈F, 2≤b j) (hcost : 2*(∑ j∈F,(b j-1))<3*F.card) :
    F.card < 2*(F.filter (fun j => b j=2)).card := by
  classical
  have per (j : ι) (hj : j∈F) : 2≤(b j-1)+(if b j=2 then 1 else 0) := by
    split <;> have := hmin j hj <;> omega
  have sum := sum_le_sum per
  simp only [sum_const,sum_add_distrib,sum_boole,nsmul_eq_mul,Nat.cast_id] at sum
  omega

/-- For an obstruction of rank four, strictly more than half of the other colors
occur on chords of distinct induced cycles of length five, seven or nine.
Each two-edge path around such a cycle determines its foreign color. -/
theorem MinimalObstruction.majority_odd_cycles {S : Finset V} (h : MinimalObstruction c k 4 S)
    (hr : 3 ≤ r) (hb : Balanced c) (htr : 4<r) :
    ∃ (J : Finset (Fin r)) (W : Fin r → Finset V), J ⊆ univ.erase k ∧ r-1<2*J.card ∧
      Set.InjOn W (J : Set (Fin r)) ∧
      ∀ j∈J, W j ⊆ S ∧ rankOn (colorGraph c j) (W j)=2 ∧
        ((W j).card=5 ∨ (W j).card=7 ∨ (W j).card=9) ∧
        Nonempty (cycleGraph (W j).card ≃g (colorGraph c k).induce ((W j) : Set V)) ∧
        ∀ x∈W j, ∀ y∈W j, ∀ z∈W j, (colorGraph c k).Adj x y →
          (colorGraph c k).Adj x z → y≠z → c s(y,z)=j := by
  classical
  obtain ⟨W,hloc,hcost⟩ := h.exists_palette_product_obstructions hr hb htr
  let F := univ.erase k
  let b (j : Fin r) := rankOn (colorGraph c j) (W j)
  let J := F.filter fun j => b j=2
  have fcard : F.card=r-1 := by simp [F]
  have bmin (j : Fin r) (hj : j∈F) : 2≤b j := (hloc j (mem_erase.mp hj).1).2.2.2.2
  have cost : 2*(∑ j∈F,(b j-1))<3*F.card := by
    rw [fcard,Nat.mul_comm 3]
    exact hcost
  have large := rank_two_majority F b bmin cost
  have col {j : Fin r} (hj : j ∈ J) : j≠k := (mem_erase.mp (mem_filter.mp hj).1).1
  have two {j : Fin r} (hj : j ∈ J) : rankOn (colorGraph c j) (W j)=2 := (mem_filter.mp hj).2
  refine ⟨J,W,filter_subset ..,fcard ▸ large,?_,?_⟩
  · intro i hi j hj eq
    obtain ⟨_,hw,_,_,_⟩ := hloc i (col hi)
    obtain ⟨x,hx⟩ := hw.inseparable.nonempty
    have deg := hw.degree_ge x hx
    rw [two hi] at deg
    obtain ⟨y,hy,z,hz,hyz⟩ := one_lt_card.mp (lt_of_lt_of_le (by decide : 1 < 2) deg)
    obtain ⟨hyW,hxy⟩ := mem_filter.mp hy
    obtain ⟨hzW,hxz⟩ := mem_filter.mp hz
    exact (path_chord_of_rank_two (col hi) (two hi) hx hyW hzW hxy hxz hyz).symm.trans
      (path_chord_of_rank_two (col hj) (two hj) (eq ▸ hx) (eq ▸ hyW) (eq ▸ hzW) hxy hxz hyz)
  · intro j hj
    obtain ⟨hsub,hw,ha,hlo,_⟩ := hloc j (col hj)
    have hcard := hw.card_eq
    rw [two hj] at hcard
    refine ⟨hsub,two hj,by omega,(hw.induced_odd_cycle_of_rank_two (two hj)).2,?_⟩
    intro x hx y hy z hz
    exact path_chord_of_rank_two (col hj) (two hj) hx hy hz

end Erdos617
