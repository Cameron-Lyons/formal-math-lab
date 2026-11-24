import Erdos617.NestedObstruction
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} {G H : SimpleGraph V} {S : Finset V}

/-- A shortcut of a shortest odd closed walk cannot shorten both arcs between its endpoints. -/
private theorem no_shortcut {u : V} (p : G.Walk u u) (ho : Odd p.length)
    (hmin : ∀ v (q : G.Walk v v), q.length < p.length → Even q.length)
    {i j : ℕ} (hij : i ≤ j) (hjp : j ≤ p.length)
    (e : G.Walk (p.getVert i) (p.getVert j))
    (ha : j-i+e.length < p.length) (hb : i+e.length+(p.length-j) < p.length) : False := by
  have hv : ((p.drop i).take (j-i)).length = j-i := by
    rw [Walk.take_length, Walk.drop_length, Nat.min_eq_left (by omega)]
  let m : G.Walk (p.getVert i) (p.getVert j) :=
    ((p.drop i).take (j-i)).copy rfl (by rw [Walk.drop_getVert, Nat.add_sub_of_le hij])
  have h₁ := hmin _ (m.append e.reverse) (by simpa [m, hv] using ha)
  have h₂ := hmin _ (((p.take i).append e).append (p.drop j)) (by
    simpa [Walk.take_length, Walk.drop_length, Nat.min_eq_left (hij.trans hjp)] using hb)
  simp only [Walk.length_append, Walk.length_reverse, m, Walk.length_copy, hv,
    Walk.take_length, Walk.drop_length, Nat.min_eq_left (hij.trans hjp)] at h₁ h₂
  obtain ⟨k,hk⟩ := ho
  obtain ⟨a,ha'⟩ := h₁
  obtain ⟨b,hb'⟩ := h₂
  omega

/-- Natural-number description of consecutive indices, including the closing edge. -/
private def cycleNeighbors {n : ℕ} (i j : Fin n) : Prop :=
  j.val=i.val+1 ∨ (i.val=0 ∧ j.val+1=n)

private theorem cycleNeighbors_iff {n : ℕ} {i j : Fin n} (hij : i<j) :
    (cycleGraph n).Adj i j ↔ cycleNeighbors i j := by
  have hi := i.isLt
  have hj := j.isLt
  have h : i.val<j.val := hij
  rw [cycleGraph_adj', Fin.sub_val_of_le hij.le, Fin.val_sub, Nat.mod_eq_of_lt (by omega)]
  unfold cycleNeighbors
  omega

private theorem shortest_cycle {G : SimpleGraph V} (hb : ¬ G.Colorable 2) :
    ∃ n : ℕ, Odd n ∧ 3 ≤ n ∧ Nonempty (cycleGraph n ↪g G) := by
  classical
  have hloop : ∃ n : ℕ, ∃ (u : V) (p : G.Walk u u), p.length=n ∧ Odd n := by
    rw [two_colorable_iff_forall_loop_even] at hb
    push Not at hb
    obtain ⟨u,p,h⟩ := hb
    exact ⟨_,u,p,rfl,Nat.not_even_iff_odd.mp h⟩
  obtain ⟨u,p,hp,ho⟩ := Nat.find_spec hloop
  rw [← hp] at ho
  have hmin : ∀ v (q : G.Walk v v), q.length<p.length → Even q.length := by
    intro v q hq
    apply Nat.not_odd_iff_even.mp
    intro hqo
    have h := Nat.find_min' hloop (show ∃ (v : V) (q' : G.Walk v v),
      q'.length=q.length ∧ Odd q.length from ⟨v,q,rfl,hqo⟩)
    omega
  have hdist (i j : Fin p.length) (hlt : i<j) : p.getVert i ≠ p.getVert j := by
    intro he
    have hlt' : i.val < j.val := hlt
    let e : G.Walk (p.getVert i) (p.getVert j) := Walk.nil.copy rfl he
    have he0 : e.length=0 := by simp [e]
    exact no_shortcut p ho hmin hlt'.le j.isLt.le e (by rw [he0]; omega) (by rw [he0]; omega)
  let f : Fin p.length ↪ V := ⟨fun i => p.getVert i, fun i j eq => by
    rcases lt_trichotomy i j with h | h | h
    · exact (hdist i j h eq).elim
    · exact h
    · exact (hdist j i h eq.symm).elim⟩
  have hthree : 3 ≤ p.length := by
    by_contra! hlow
    obtain ⟨m,hm⟩ := ho
    have hone : p.length=1 := by omega
    have he := p.adj_getVert_succ (i := 0) (by omega)
    rw [Walk.getVert_zero, show 0+1=p.length by omega, Walk.getVert_length] at he
    exact G.loopless.irrefl u he
  suffices hh : ∀ i j : Fin p.length, i<j → (G.Adj (f i) (f j) ↔ cycleNeighbors i j) by
    refine ⟨_,ho,hthree,⟨⟨f,?_⟩⟩⟩
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · exact (hh _ _ h).trans (cycleNeighbors_iff h).symm
    · subst j
      simp
    · rw [adj_comm, (cycleGraph p.length).adj_comm]
      exact (hh _ _ h).trans (cycleNeighbors_iff h).symm
  intro i j hij
  change G.Adj (p.getVert i) (p.getVert j) ↔ _
  have hij' : i.val < j.val := hij
  constructor
  · intro hadj
    by_contra! hn
    simp only [cycleNeighbors, not_or, not_and] at hn
    let e : G.Walk (p.getVert i) (p.getVert j) := .cons hadj .nil
    have he : e.length=1 := rfl
    exact no_shortcut p ho hmin hij'.le j.isLt.le e
      (by rw [he]; have := j.isLt; by_cases h : i.val=0 <;> grind)
      (by rw [he]; omega)
  · rintro (hj | ⟨hi,hj⟩)
    · simpa only [hj] using p.adj_getVert_succ i.isLt
    · have h := p.adj_getVert_succ j.isLt
      rw [hj, Walk.getVert_length] at h
      simpa only [hi, Walk.getVert_zero] using h.symm

private theorem two_colorable_card_le (G : SimpleGraph V) (A : Finset V)
    (hb : (G.induce (A : Set V)).Colorable 2) : A.card ≤ 2*rankOn G A := by
  classical
  obtain ⟨c⟩ := hb
  let C (j : Fin 2) := (univ : Finset A).filter fun v => c v=j
  have hsum : (∑ j, (C j).card) = A.card := by
    simpa [C] using sum_card_fiberwise_eq_card_filter (univ : Finset A) (univ : Finset (Fin 2)) c
  have hc (j : Fin 2) : (C j).card ≤ rankOn G A := by
    let val : A ↪ V := Function.Embedding.subtype _
    have hsub : (C j).map val ⊆ A := by
      intro x hx
      obtain ⟨v,_,rfl⟩ := mem_map.mp hx
      exact v.property
    have hind : G.IsIndepSet ((C j).map val : Set V) := by
      intro x hx y hy hne hadj
      obtain ⟨v,hv,rfl⟩ := mem_map.mp hx
      obtain ⟨w,hw,rfl⟩ := mem_map.mp hy
      exact c.valid (show (G.induce (A : Set V)).Adj v w from hadj)
        ((mem_filter.mp hv).2.trans (mem_filter.mp hw).2.symm)
    simpa using card_le_rankOn G hsub hind
  rw [← hsum]
  simpa using sum_le_sum (s := univ) fun j _ => hc j

private theorem cycle_rank_bound {n : ℕ} (hn : 3 ≤ n) (ho : Odd n)
    (f : cycleGraph n ↪g G) :
    2*rankOn G (univ.map f.toEmbedding) < n := by
  classical
  let next (i : Fin n) : Fin n := ⟨if i.val+1=n then 0 else i.val+1, by
    have := i.isLt
    split <;> omega⟩
  have hninj : Function.Injective next := by
    intro i j hij
    have hh := congrArg Fin.val hij
    change (if i.val+1=n then 0 else i.val+1)=(if j.val+1=n then 0 else j.val+1) at hh
    apply Fin.ext
    split_ifs at hh <;> omega
  have hadj (i : Fin n) : (cycleGraph n).Adj i (next i) := by
    by_cases h : i.val+1=n
    · have hlt : next i < i := by
        simp only [Fin.lt_def, next, h, ↓reduceIte]
        omega
      apply Adj.symm
      exact (cycleNeighbors_iff hlt).2 (Or.inr ⟨by simp [next,h],h⟩)
    · have hlt : i < next i := by
        change i.val < (if i.val+1=n then 0 else i.val+1)
        simp only [h, ↓reduceIte]; omega
      exact (cycleNeighbors_iff hlt).2 (Or.inl (by simp [next,h]))
  obtain ⟨I,hI,hi,hr⟩ := exists_max_indep G (univ.map f.toEmbedding)
  let P := univ.filter fun i => f i ∈ I
  have him : P.map f.toEmbedding=I := by
    ext v
    constructor
    · intro hv
      obtain ⟨i,hi,rfl⟩ := mem_map.mp hv
      exact (mem_filter.mp hi).2
    · intro hv
      obtain ⟨i,_,rfl⟩ := mem_map.mp (hI hv)
      exact mem_map.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hv⟩,rfl⟩
  have hd : Disjoint P (P.image next) := by
    rw [Finset.disjoint_left]
    intro i hiP hiim
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hiim
    have he := f.map_rel_iff.mpr (hadj j)
    exact hi (mem_filter.mp hj).2 (mem_filter.mp hiP).2 he.ne he
  have hcap := card_le_univ (P ∪ P.image next)
  rw [card_union_of_disjoint hd,card_image_of_injective _ hninj,Fintype.card_fin] at hcap
  have hcard : P.card=I.card := by rw [← him, card_map]
  obtain ⟨k,hk⟩ := ho
  omega

private theorem obstruction_cycle {G H : SimpleGraph V} {S A : Finset V}
    (h : RankProductObstruction G H S) (h₂ : rankOn H S = 2) (hA : A ⊆ S)
    (hbad : ¬ (G.induce (A : Set V)).Colorable 2) :
    A=S ∧ Odd A.card ∧ Nonempty (cycleGraph A.card ≃g G.induce (A : Set V)) := by
  classical
  obtain ⟨n,ho,hn,⟨f⟩⟩ := shortest_cycle hbad
  let e : cycleGraph n ↪g G := (Embedding.induce (A : Set V)).comp f
  let Y := univ.map e.toEmbedding
  have hYA : Y ⊆ A := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := mem_map.mp hx
    exact (f i).property
  have hsize : Y.card=n := by simp [Y]
  have hviol : 2*rankOn G Y < Y.card := by rw [hsize]; exact cycle_rank_bound hn ho e
  have hYS : Y=S := by
    by_contra hne
    have lower := h.smaller Y (Finset.ssubset_iff_subset_ne.mpr ⟨hYA.trans hA,hne⟩)
    have cap := rankOn_mono H (hYA.trans hA)
    rw [h₂] at cap
    have upper := Nat.mul_le_mul_left (rankOn G Y) cap
    omega
  have heq : A=S := Subset.antisymm hA (hYS ▸ hYA)
  have hcard : A.card=n := by rwa [hYS, ← heq] at hsize
  have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2
    ⟨f.injective,by simpa using hcard.symm⟩
  refine ⟨heq,hcard ▸ ho,?_⟩
  rw [hcard]
  exact ⟨RelIso.ofSurjective f hbij.surjective⟩

/-- If the second independence rank is two, the first graph is vertex-minimal
among induced restrictions that do not admit a bipartition. -/
theorem RankProductObstruction.minimal_nonbipartite_of_rank_two
    (h : RankProductObstruction G H S) (h₂ : rankOn H S = 2) :
    ¬ (G.induce (S : Set V)).Colorable 2 ∧
      ∀ A ⊂ S, (G.induce (A : Set V)).Colorable 2 := by
  constructor
  · intro hc
    have cap := two_colorable_card_le G S hc
    have hlo := h.large
    rw [h₂] at hlo
    omega
  · intro A hA
    by_contra! hc
    exact (Finset.ssubset_iff_subset_ne.mp hA).2 (obstruction_cycle h h₂ hA.le hc).1

/-- The first graph of a rank-product obstruction whose second rank is two
induces an odd cycle on the entire obstruction. -/
theorem RankProductObstruction.induced_odd_cycle_of_rank_two
    (h : RankProductObstruction G H S) (h₂ : rankOn H S = 2) :
    Odd S.card ∧ Nonempty (cycleGraph S.card ≃g G.induce (S : Set V)) :=
  (obstruction_cycle h h₂ (Subset.rfl : S ⊆ S) (h.minimal_nonbipartite_of_rank_two h₂).1).2

/-- At parameter at most five, a minimal obstruction contains a spanning odd
cycle on a set where a second color has independence rank exactly two. -/
theorem MinimalObstruction.exists_nested_odd_cycle [DecidableEq V]
    {r t : ℕ} {c : Sym2 V → Fin r} {k : Fin r} (h : MinimalObstruction c k t S)
    (hr : 3 ≤ r) (hb : Balanced c) (htr : t < r) (ht : t ≤ 5) :
    ∃ j : Fin r, j ≠ k ∧ ∃ W ⊆ S,
      RankProductObstruction (colorGraph c k) (colorGraph c j) W ∧
      rankOn (colorGraph c j) W=2 ∧ 5≤W.card ∧ W.card≤2*t+1 ∧ Odd W.card ∧
      Nonempty (cycleGraph W.card ≃g (colorGraph c k).induce (W : Set V)) := by
  obtain ⟨j,hj,W,hW,hw,hk,hhalf,hk₂,hj₂,_⟩ := h.exists_nested_product_obstruction hr hb htr
  have h₂ : rankOn (colorGraph c j) W=2 := by omega
  have hcard := hw.card_eq
  rw [h₂] at hcard
  exact ⟨j,hj,W,hW,hw,h₂,by omega,by omega,hw.induced_odd_cycle_of_rank_two h₂⟩

end Erdos617
