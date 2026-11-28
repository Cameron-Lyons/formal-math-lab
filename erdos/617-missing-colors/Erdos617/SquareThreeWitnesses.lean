module

public import Erdos617.ClusterExtension
public import Erdos617.SquareTuran
public import Erdos617.SquarePaletteBudget
public import Erdos617.GlobalCliqueEnergy
public import Erdos617.OnePairMerge

@[expose] public section

namespace Erdos617

open Finset SimpleGraph
open scoped Classical

/-- In an ambient counterexample every color strictly exceeds the Turán
minimum on every square one step smaller. -/
theorem strict_square_turan_floor {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (hr : 5≤r) (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c)
    (U : Finset V) (sz : U.card=(r-1)^2+1) (k : Fin r) :
    let d := fun e : Sym2 U => c (e.map Subtype.val)
    r*(r-2).choose 2+2*(r-2)<(colorGraph d k).edgeFinset.card := by
  intro d
  let G := colorGraph d k
  have cap := balanced_indepNum_le d (balanced_pullback c hb (Function.Embedding.subtype (·∈U))) k
  have n := (Fintype.card_coe U).trans sz
  have lower := square_turan_floor G (by omega : 3≤r) n cap
  apply lt_of_le_of_ne lower
  intro eq
  obtain ⟨P,cover,dis,cl,sep⟩ := square_turan_rigid G (by omega : 3≤r) n cap eq.symm
  exact no_square_turan_partition hr hn hb P cover dis cl sep

/-- Every smaller square in a counterexample has at least three individually
avoidable colors. This applies even when the square is chosen arbitrarily,
without deleting prescribed full rows or assuming a least counterexample. -/
theorem three_avoidable_on_every_square {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (hr : 6≤r) (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c)
    (U : Finset V) (sz : U.card=(r-1)^2+1) :
    let d := fun e : Sym2 U => c (e.map Subtype.val)
    3≤(univ.filter fun j => ¬HitsPalette d (r-1) {j}).card := by
  classical
  obtain ⟨s,rfl⟩ : ∃ s,r=s+1 := ⟨r-1,by omega⟩
  simp only [Nat.add_sub_cancel] at sz ⊢
  let d := fun e : Sym2 U => c (e.map Subtype.val)
  change 3≤(univ.filter fun j => ¬HitsPalette d s {j}).card
  have small (k : Fin (s+1)) := strict_square_turan_floor (by omega) hn c hb U (by simpa using sz) k
  change ∀ k,(s+1)*(s-1).choose 2+2*(s-1)<(colorGraph d k).edgeFinset.card at small
  by_cases cl : ∀ k,(colorGraph d k).CliqueFree (s+1)
  · exact square_palette_three_avoidable (by omega) ((Fintype.card_coe U).trans sz) d cl small
  · push Not at cl
    obtain ⟨k,fail⟩ := cl
    obtain ⟨T,full⟩ := not_forall.mp fail
    have hT : (colorGraph d k).IsNClique (s+1) T := of_not_not full
    have inc : univ.erase k ⊆ univ.filter fun j => ¬HitsPalette d s {j} := by
      intro j hj
      refine mem_filter.mpr ⟨mem_univ _,?_⟩
      intro hit
      obtain ⟨x,hx,y,hy,ne,e⟩ := hit T hT.card_eq
      exact (mem_erase.mp hj).1 ((mem_singleton.mp e).symm.trans (hT.isClique hx hy ne).2)
    have count := card_le_card inc
    simp only [card_erase_of_mem (mem_univ k),card_univ,Fintype.card_fin,Nat.add_sub_cancel] at count
    omega

/-- A vertex-independent relabeling of the original colors cannot give a
balanced (r−1)-coloring on any square of the required size. -/
theorem no_square_palette_merge {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (hr : 6≤r) (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c)
    (U : Finset V) (sz : U.card=(r-1)^2+1) :
    let d := fun e : Sym2 U => c (e.map Subtype.val)
    ∀ f : Fin r → Fin (r-1), ¬Balanced (f ∘ d) := by
  intro d f merged
  have many := three_avoidable_on_every_square hr hn c hb U sz
  have n : ∃ T : Finset U,T.card=r := by
    apply Exists.imp (fun W h => h.2) (exists_subset_card_eq (s:=(univ : Finset U)) ?_)
    rw [card_univ,Fintype.card_coe,sz,pow_two]
    have := Nat.mul_le_mul_left (r-1) (show 1≤r-1 by omega)
    omega
  have few := ((one_pair_merge_or_obstruction (by omega) d n).mp ⟨f,merged⟩).1
  exact (by omega : ¬3≤2) (many.trans few)

end Erdos617
