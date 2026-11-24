import Erdos617.MinimalObstruction
import Erdos617.ColorCounts

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] {r : ℕ}

/-- Every color other than k needs at least |S|−r distinct edges in S.
An oriented list of pairs covering all such edges therefore limits |S|. -/
theorem foreign_pair_budget (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r)
    (S : Finset V) (P : Finset (V × V))
    (hP : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → c s(x,y) ≠ k → (x,y) ∈ P ∨ (y,x) ∈ P) :
    (r-1)*S.card ≤ (r-1)*r + P.card := by
  classical
  let col (p : V × V) := c s(p.1,p.2)
  let F := univ.erase k
  have bound (j : Fin r) (hj : j ∈ F) :
      S.card ≤ r+(P.filter fun p => col p = j).card := by
    let E := P.filter fun p => col p = j
    let H := E.image Prod.fst
    have hsmall : (S \ H).card ≤ r := by
      by_contra! hlarge
      obtain ⟨T, hT, hc⟩ := exists_subset_card_eq (Nat.succ_le_of_lt hlarge)
      obtain ⟨x, hx, y, hy, hxy, he⟩ := hb T hc j
      obtain ⟨hxS, hxH⟩ := mem_sdiff.mp (hT hx)
      obtain ⟨hyS, hyH⟩ := mem_sdiff.mp (hT hy)
      rcases hP x hxS y hyS hxy (he ▸ (mem_erase.mp hj).1) with hf | hf
      · exact hxH (mem_image.mpr ⟨(x,y),mem_filter.mpr ⟨hf,he⟩,rfl⟩)
      · exact hyH (mem_image.mpr ⟨(y,x),mem_filter.mpr ⟨hf,by simpa [col, Sym2.eq_swap] using he⟩,rfl⟩)
    have hs := card_sdiff_add_card_inter S H
    have hi : (S ∩ H).card ≤ E.card := (card_le_card inter_subset_right).trans card_image_le
    change S.card ≤ r+E.card
    omega
  have hsum := sum_le_sum (s := F) bound
  rw [sum_add_distrib, sum_card_fiberwise_eq_card_filter] at hsum
  have hf : F.card = r-1 := by simp [F]
  simp only [sum_const, hf, nsmul_eq_mul, Nat.cast_id] at hsum
  exact hsum.trans (Nat.add_le_add_left (card_filter_le ..) _)

/-- With two overlapping monochromatic cliques, all foreign pairs on their union
cross between the two outside bags. -/
theorem three_clique_bag_budget (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r)
    (A B C : Finset V) (hd : Disjoint A B) (hd' : Disjoint (A ∪ B) C)
    (hAB : (colorGraph c k).IsClique ((A ∪ B : Finset V) : Set V))
    (hBC : (colorGraph c k).IsClique ((B ∪ C : Finset V) : Set V)) :
    (r-1)*(A.card+B.card+C.card) ≤ (r-1)*r + A.card*C.card := by
  have h := foreign_pair_budget c hb k ((A ∪ B) ∪ C) (A ×ˢ C) (by
    intro x hx y hy hxy hcol
    have hcAB : ¬ (x ∈ A ∪ B ∧ y ∈ A ∪ B) := fun h => hcol (hAB h.1 h.2 hxy).2
    have hcBC : ¬ (x ∈ B ∪ C ∧ y ∈ B ∪ C) := fun h => hcol (hBC h.1 h.2 hxy).2
    simp only [mem_union] at hx hy hcAB hcBC
    simp only [mem_product]
    grind)
  simpa only [card_union_of_disjoint hd', card_union_of_disjoint hd, card_product] using h

/-- The sum of consecutive products along a path is bounded by the total inner
weight times s when the endpoint weights together are at most s. -/
theorem path_product_bound {s t : ℕ} (ht : 2 ≤ t) (w : Fin (t+1) → ℕ)
    (hw : ∀ i, w i ≤ s) (hend : w 0+w (Fin.last t) ≤ s) :
    (∑ i : Fin t, w i.castSucc*w i.succ) +
      s*(w 0+w (Fin.last t)) ≤ s*∑ i, w i := by
  let a := w (Fin.last t)
  let b := s-a
  have hab : a+b=s := by dsimp [a,b]; have := hw (Fin.last t); omega
  have hz : w 0 ≤ b := by dsimp [a,b]; omega
  let inner (i : Fin (t+1)) := if i=0 ∨ i=Fin.last t then 0 else w i
  have h0 : inner 0=0 := by simp [inner]
  have ht' : inner (Fin.last t)=0 := by simp [inner]
  have interp (x y : ℕ) (hx : x ≤ s) (hy : y ≤ s) : x*y ≤ a*x+b*y := by
    rcases le_total x y with hxy | hyx
    · have h := Nat.mul_le_mul_left x hy
      nlinarith only [h, Nat.mul_le_mul_left b hxy, congrArg (·*x) hab]
    · have h := Nat.mul_le_mul_right y hx
      nlinarith only [h,Nat.mul_le_mul_left a hyx,congrArg (·*y) hab]
  have per (i : Fin t) : w i.castSucc*w i.succ ≤ a*inner i.castSucc + b*inner i.succ := by
    have hl := Fin.castSucc_ne_last i
    have hr := Fin.succ_ne_zero i
    by_cases hi : i.castSucc = 0
    · have hi' : i.succ ≠ Fin.last t := by
        intro he
        have h1 := congrArg Fin.val hi
        have h2 := congrArg Fin.val he
        simp only [Fin.val_castSucc, Fin.val_zero, Fin.val_succ, Fin.val_last] at h1 h2
        omega
      simp only [hi,h0,Nat.mul_zero,Nat.zero_add,inner,hr,hi',or_self,ite_false]
      exact Nat.mul_le_mul_right _ hz
    · by_cases he : i.succ = Fin.last t
      · simp only [he,ht',Nat.mul_zero,Nat.add_zero,inner,hi,hl,or_self,ite_false]
        exact Nat.le_of_eq (Nat.mul_comm ..)
      · simpa [inner,hi,hl,hr,he] using interp _ _ (hw i.castSucc) (hw i.succ)
  have edge := sum_le_sum (s := univ) fun i _ => per i
  have lc := Fin.sum_univ_castSucc inner
  have rc := Fin.sum_univ_succ inner
  rw [ht',add_zero] at lc
  rw [h0,zero_add] at rc
  simp only [sum_add_distrib, ← mul_sum, ← lc, ← rc, ← Nat.add_mul, hab] at edge
  have hne : (0 : Fin (t+1)) ≠ Fin.last t := by
    intro he
    have h := congrArg Fin.val he
    simp only [Fin.val_zero,Fin.val_last] at h
    omega
  have split (i : Fin (t+1)) :
      w i = inner i + (if i=0 then w 0 else 0) + (if i=Fin.last t then w (Fin.last t) else 0) := by
    by_cases hi : i=0
    · subst i
      simp [h0,hne]
    · by_cases h : i=Fin.last t
      · subst i
        simp [ht',hi]
      · simp [inner,hi,h]
  have hs := sum_congr (s₁ := univ) rfl fun i _ => split i
  simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true] at hs
  nlinarith only [edge, congrArg (s*·) hs]

/-- Consecutive bags of an odd cycle form cliques. The ordering starts with a
light bag, alternates with a center bag, and closes by joining the two end
light bags. Only bags in a common three-bag estimate need be disjoint. -/
structure OddCliqueBags (G : SimpleGraph V) (t : ℕ) where
  light : Fin (t+1) → Finset V
  center : Fin t → Finset V
  left_disjoint (i : Fin t) : Disjoint (light i.castSucc) (center i)
  right_disjoint (i : Fin t) : Disjoint (light i.castSucc ∪ center i) (light i.succ)
  ends_disjoint : Disjoint (light 0) (light (Fin.last t))
  left_clique (i : Fin t) : G.IsClique ((light i.castSucc ∪ center i : Finset V) : Set V)
  right_clique (i : Fin t) : G.IsClique ((center i ∪ light i.succ : Finset V) : Set V)
  ends_clique : G.IsClique ((light 0 ∪ light (Fin.last t) : Finset V) : Set V)

/-- An odd cycle of 2t+1 monochromatic clique bags can cover at most tr vertices
if each light bag and their closing pair have size at most r−1. -/
theorem odd_clique_bag_bound {t : ℕ} (hr : 2 ≤ r) (ht : 2 ≤ t)
    (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r) (B : OddCliqueBags (colorGraph c k) t)
    (hsize : ∀ i, (B.light i).card ≤ r-1)
    (hend : (B.light 0).card+(B.light (Fin.last t)).card ≤ r-1) :
    (∑ i, (B.light i).card) + (∑ i, (B.center i).card) ≤ t*r := by
  let w (i : Fin (t+1)) := (B.light i).card
  let v (i : Fin t) := (B.center i).card
  have per (i : Fin t) : (r-1)*(w i.castSucc + v i + w i.succ) ≤
      (r-1)*r + w i.castSucc*w i.succ :=
    three_clique_bag_budget c hb k _ _ _ (B.left_disjoint i) (B.right_disjoint i)
      (B.left_clique i) (B.right_clique i)
  have budget := sum_le_sum (s := univ) fun i _ => per i
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_id] at budget
  have path := path_product_bound ht w hsize hend
  have left := congrArg ((r-1)*·) (Fin.sum_univ_castSucc w)
  have right := congrArg ((r-1)*·) (Fin.sum_univ_succ w)
  change (∑ i, w i) + (∑ i, v i) ≤ t*r
  have hm : (r-1)*((∑ i, w i) + (∑ i, v i)) ≤ (r-1)*(t*r) := by
    nlinarith only [path,budget,left,right]
  exact Nat.le_of_mul_le_mul_left hm (by omega)

/-- A first obstruction on tr+1 vertices cannot consist of an odd cycle of
clique bags in its obstruction color, even if extra edges join other bags. -/
theorem MinimalObstruction.no_odd_clique_bag_cover {t : ℕ} {S : Finset V} {c : Sym2 V → Fin r}
    {k : Fin r} (h : MinimalObstruction c k t S) (hb : Balanced c) (ht : 2 ≤ t)
    (htr : t < r) (B : OddCliqueBags (colorGraph c k) t) (hsub : ∀ i, B.light i ⊆ S) :
    ¬ S ⊆ univ.biUnion B.light ∪ univ.biUnion B.center := by
  intro hcover
  have cap {A : Finset V} (hAS : A ⊆ S) (hc : (colorGraph c k).IsClique (A : Set V)) :
      A.card ≤ r-1 := by
    by_contra! hlarge
    obtain ⟨C,hCA,hn⟩ := exists_subset_card_eq (s := A) (show r ≤ A.card by omega)
    exact h.no_clique hb htr C (hCA.trans hAS) ⟨hc.subset hCA,hn⟩
  have hsize (i : Fin (t+1)) : (B.light i).card ≤ r-1 := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact cap (hsub _) (B.ends_clique.subset (subset_union_right (s₁ := B.light 0)))
    · exact cap (hsub _) ((B.left_clique j).subset (subset_union_left (s₂ := B.center j)))
  have ends := cap (union_subset (hsub 0) (hsub (Fin.last t))) B.ends_clique
  rw [card_union_of_disjoint B.ends_disjoint] at ends
  have bound := odd_clique_bag_bound (by omega) ht c hb k B hsize ends
  have total := (card_le_card hcover).trans ((card_union_le ..).trans
    (Nat.add_le_add (card_biUnion_le (s := univ) (t := B.light))
      (card_biUnion_le (s := univ) (t := B.center))))
  rw [h.card_eq] at total
  omega

end Erdos617
