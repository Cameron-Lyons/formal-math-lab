module

public import Erdos617.IndependentSets
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem weighted_independent_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → ℕ) (hcap : ∀ K : Finset V, G.IsClique (K : Set V) → ∀ v ∈ K, K.card ≤ c v)
    (w : V → ℝ) (hnn : ∀ v, 0 ≤ w v) :
    ∃ I : Finset V, G.IsMaximumIndepSet I ∧
      2*(∑ v, w v) ≤ ∑ i ∈ I, (((c i : ℝ)+1)*w i + ∑ x ∈ G.neighborFinset i, w x) := by
  classical
  let F := univ.filter (fun I : Finset V => G.IsMaximumIndepSet I)
  obtain ⟨I₀,h₀⟩ := G.maximumIndepSet_exists
  obtain ⟨I,hIF,hmax⟩ := F.exists_max_image (fun J => ∑ j ∈ J, w j)
    ⟨I₀,mem_filter.mpr ⟨mem_univ _,h₀⟩⟩
  have hI := (mem_filter.mp hIF).2
  let N (x : V) := I.filter (G.Adj x)
  let P (i : V) := Iᶜ.filter (fun x => N x={i})
  have pbound (i : V) (hi : i∈I) : (∑ x∈P i, w x) + w i ≤ (c i : ℝ)*w i := by
    have notin : i ∉ P i := fun h => (mem_compl.mp (mem_filter.mp h).1) hi
    have size := hcap _ (private_clique G I hI i hi) i (mem_insert_self ..)
    change (insert i (P i)).card ≤ c i at size
    rw [card_insert_of_notMem notin] at size
    have weight (x : V) (hx : x∈P i) : w x ≤ w i := by
      obtain ⟨hxout,hsingle⟩ := mem_filter.mp hx
      have hxi : x ∉ I.erase i := fun h => (mem_compl.mp hxout) (mem_of_mem_erase h)
      let J := insert x (I.erase i)
      have ind : G.IsIndepSet J := independent_insert_of_nonadjacent G
        (hI.isIndepSet.mono (erase_subset ..)) x (by
          intro y hy adj
          have memN : y ∈ N x := mem_filter.mpr ⟨mem_of_mem_erase hy,adj⟩
          exact (mem_erase.mp hy).1 (mem_singleton.mp (hsingle ▸ memN)))
      have same : J.card = I.card := by
        rw [show J = insert x (I.erase i) by rfl,card_insert_of_notMem hxi,card_erase_add_one hi]
      have best : G.IsMaximumIndepSet J := ⟨ind,fun A hA => same ▸ hI.maximum A hA⟩
      have cmp := hmax J (mem_filter.mpr ⟨mem_univ _,best⟩)
      change (∑ y∈insert x (I.erase i), w y) ≤ ∑ y∈I,w y at cmp
      rw [sum_insert hxi] at cmp
      linarith [sum_erase_add I w hi]
    have bound := sum_le_sum weight
    simp only [sum_const,nsmul_eq_mul] at bound
    have size' : ((P i).card : ℝ)+1 ≤ c i := by exact_mod_cast size
    linarith [mul_le_mul_of_nonneg_right size' (hnn i)]
  have seen (x : V) (hx : x ∈ Iᶜ) :
      2 ≤ (N x).card+(I.filter (fun i => N x={i})).card := by
    have pos : 0 < (N x).card := by
      by_contra! hn
      have hi := independent_insert_of_nonadjacent G hI.isIndepSet x (fun y hy hxy =>
        (not_lt_of_ge hn) (card_pos.mpr ⟨y,mem_filter.mpr ⟨hy,hxy⟩⟩))
      have := hI.maximum _ hi
      rw [card_insert_of_notMem (mem_compl.mp hx)] at this
      omega
    by_cases hn : (N x).card=1
    · obtain ⟨i,hi⟩ := card_eq_one.mp hn
      have hN : i∈N x := hi ▸ mem_singleton_self _
      have := card_pos.mpr (show (I.filter (fun i => N x={i})).Nonempty from
        ⟨i,mem_filter.mpr ⟨(mem_filter.mp hN).1,hi⟩⟩)
      omega
    · omega
  have cover := sum_le_sum (s:=Iᶜ) (fun x hx =>
    mul_le_mul_of_nonneg_right (show (2:ℝ) ≤ (N x).card+(I.filter (fun i => N x={i})).card by
      exact_mod_cast seen x hx) (hnn x))
  simp only [add_mul,sum_add_distrib,←mul_sum] at cover
  have inc : (∑ x∈Iᶜ, ((N x).card : ℝ)*w x) ≤ ∑ i∈I, ∑ x∈G.neighborFinset i,w x := by
    have eq := sum_sum_bipartiteAbove_eq_sum_sum_bipartiteBelow (s:=Iᶜ) (t:=I) G.Adj (fun x _ => w x)
    simp only [bipartiteAbove,bipartiteBelow,sum_const,nsmul_eq_mul] at eq
    change (∑ x∈Iᶜ, ((N x).card : ℝ)*w x) = _ at eq
    rw [eq]
    apply sum_le_sum
    intro i _
    exact sum_le_sum_of_subset_of_nonneg (fun x hx => (G.mem_neighborFinset i x).mpr
      (mem_filter.mp hx).2.symm) (fun x _ _ => hnn x)
  have priv := sum_sum_bipartiteAbove_eq_sum_sum_bipartiteBelow
    (s:=Iᶜ) (t:=I) (fun x i => N x={i}) (fun x _ => w x)
  simp only [bipartiteAbove,bipartiteBelow,sum_const,nsmul_eq_mul] at priv
  change _ = ∑ i∈I,∑ x∈P i,w x at priv
  rw [priv] at cover
  have ptotal := sum_le_sum pbound
  simp only [sum_add_distrib] at ptotal
  refine ⟨I,hI,?_⟩
  simp only [add_mul,one_mul,sum_add_distrib]
  linarith [sum_add_sum_compl I w]

/-- At an equilibrium of the local clique-weight quadratic form on the
probability simplex, the common weighted degree is at least 2/α.
This is the private-neighbor argument in Claim 2.2 of
[Liu et al.](https://arxiv.org/abs/2609.00210). -/
theorem equilibrium_local_clique_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → ℕ) (hcap : ∀ K : Finset V, G.IsClique (K : Set V) → ∀ v ∈ K, K.card ≤ c v)
    (w : V → ℝ) (hnn : ∀ v, 0 ≤ w v) (hunit : ∑ v, w v = 1)
    (q : ℝ) (heq : ∀ v, 0 < w v → ((c v : ℝ)+1)*w v + ∑ u ∈ G.neighborFinset v, w u = q) :
    2 ≤ (G.indepNum : ℝ)*q := by
  classical
  let D := univ.filter (fun v => 0 < w v)
  let incl := Function.Embedding.subtype (· ∈ D)
  let H := G.induce (D : Set V)
  have pos (v : D) : 0 < w v := (mem_filter.mp v.prop).2
  have support (v : V) (hv : v ∉ D) : w v=0 := by
    have := hnn v
    have h : ¬ 0 < w v := fun e => hv (mem_filter.mpr ⟨mem_univ _,e⟩)
    linarith
  have total : (∑ v : D, w v) = 1 := by
    rw [Finset.sum_coe_sort]
    exact (sum_subset (subset_univ D) (fun x _ hx => support x hx)).trans hunit
  have cap (K : Finset D) (hk : H.IsClique (K : Set D)) (v : D) (hv : v∈K) : K.card ≤ c v := by
    have mapped : G.IsClique (K.map incl : Finset V) := by
      intro x hx y hy hxy
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
      obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
      exact hk ha hb (fun eq => hxy (congrArg incl eq))
    simpa using hcap _ mapped v (mem_map_of_mem incl hv)
  have localEq (v : D) :
      ((c v : ℝ)+1)*w v + ∑ u∈H.neighborFinset v,w u = q := by
    rw [←heq v (pos v)]
    congr 1
    have mapN : (H.neighborFinset v).map incl = G.neighborFinset v ∩ D := by
      ext y
      constructor
      · intro hy
        obtain ⟨z,hz,rfl⟩ := mem_map.mp hy
        exact mem_inter.mpr ⟨(G.mem_neighborFinset ..).mpr ((H.mem_neighborFinset ..).mp hz),z.prop⟩
      · intro hy
        obtain ⟨ha,hd⟩ := mem_inter.mp hy
        exact mem_map.mpr ⟨⟨y,hd⟩,(H.mem_neighborFinset ..).mpr ((G.mem_neighborFinset ..).mp ha),rfl⟩
    change (∑ u∈H.neighborFinset v,w (incl u)) = _
    rw [← sum_map (H.neighborFinset v) incl w,mapN]
    exact sum_subset inter_subset_left (fun x hx h => support x (fun hd => h (mem_inter.mpr ⟨hx,hd⟩)))
  obtain ⟨I,hI,hsum⟩ := @weighted_independent_sum D (inferInstance : Fintype D) _ H _ (fun v => c v) cap (fun v => w v) (fun v => hnn v)
  simp only [total, mul_one] at hsum
  have hnum : (2:ℝ) ≤ I.card*q := by
    calc
      2 ≤ _ := hsum
      _ = ∑ _ ∈ I, q := sum_congr rfl (fun i _ => by
        convert localEq i using 2)
      _ = _ := by simp
  have mapI : G.IsIndepSet (I.map incl : Finset V) := by
    intro x hx y hy hxy he
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
    obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
    exact hI.isIndepSet ha hb (fun eq => hxy (congrArg incl eq)) he
  have rank : I.card ≤ G.indepNum := by simpa using mapI.card_le_indepNum
  have hq : 0 ≤ q := by
    by_contra! hn
    have := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg I.card) hn.le
    linarith
  have rankR : (I.card : ℝ) ≤ (G.indepNum : ℝ) := by exact_mod_cast rank
  exact hnum.trans (mul_le_mul_of_nonneg_right rankR hq)

end Erdos617
