import Erdos617.LineObstruction

namespace Erdos617

open SimpleGraph Finset

variable {V L : Type*} [Fintype V] [DecidableEq V] [DecidableEq L]

/-- Count ordered pairs of distinct vertices through each shared label. -/
private theorem common_label_sum (f : V → Finset L) (C : Finset L) (hC : ∀ x, f x ⊆ C) :
    (∑ i ∈ C, (univ.filter (fun x => i∈f x)).card*((univ.filter (fun x => i∈f x)).card-1)) =
    ∑ x, ∑ y ∈ univ.erase x, (f x ∩ f y).card := by
  classical
  let K (i : L) := univ.filter fun x => i∈f x
  let F (i : L) (x y : V) := if i∈f x then (if i∈f y then 1 else 0 : ℕ) else 0
  have shared (x y : V) : (f x ∩ f y).card = ∑ i ∈ C, F i x y := by
    have eq : f x ∩ f y=C.filter (fun i => i∈f x ∧ i∈f y) := by
      ext i
      simp only [mem_inter,mem_filter]
      exact ⟨fun h => ⟨hC x h.1,h⟩,And.right⟩
    rw [eq,card_filter]
    apply sum_congr rfl
    intro i _
    by_cases h : i∈f x <;> simp [F,h]
  have row (i : L) (x : V) : (∑ y ∈ univ.erase x,F i x y) =
      if i∈f x then (K i).card-1 else 0 := by
    by_cases h : i∈f x
    · have hx : x∈K i := mem_filter.mpr ⟨mem_univ _,h⟩
      simp only [F,h,ite_true,sum_boole,filter_erase]
      exact card_erase_of_mem hx
    · simp [F,h]
  have each (i : L) : (∑ x, ∑ y ∈ univ.erase x,F i x y)=(K i).card*((K i).card-1) := by
    simp_rw [row]
    rw [←sum_filter,sum_const,nsmul_eq_mul]
    rfl
  simp_rw [shared]
  symm
  calc
    _ = ∑ x, ∑ i ∈ C, ∑ y ∈ univ.erase x, F i x y :=
      sum_congr rfl fun x _ => sum_comm
    _ = ∑ i ∈ C, ∑ x, ∑ y ∈ univ.erase x, F i x y := sum_comm
    _ = _ := sum_congr rfl fun i _ => each i

omit [Fintype V] [DecidableEq V] in
private theorem distinct_endpairs_inter_le_one {a b : Sym2 L} (h : a≠b) :
    (a.toFinset ∩ b.toFinset).card ≤ 1 := by
  apply card_le_one.mpr
  intro x hx y hy
  by_contra hxy
  have eq (z : Sym2 L) (hxz : x∈z.toFinset) (hyz : y∈z.toFinset) :
      z=s(x,y) := (Sym2.mem_and_mem_iff hxy).mp ⟨Sym2.mem_toFinset.mp hxz,Sym2.mem_toFinset.mp hyz⟩
  exact h ((eq a (mem_inter.mp hx).1 (mem_inter.mp hy).1).trans
    (eq b (mem_inter.mp hx).2 (mem_inter.mp hy).2).symm)

/-- Ordered incidence pairs count a line-graph edge twice and a parallel
pair an additional twice. The last sum counts those ordered parallel pairs. -/
theorem LineRepresentation.edge_count {G : SimpleGraph V} [DecidableRel G.Adj]
    {p : V → Sym2 L} (rep : LineRepresentation G univ p) (C : Finset L)
    (hC : ∀ x, (p x).toFinset ⊆ C) :
    (∑ i ∈ C, (univ.filter (fun x => i∈(p x).toFinset)).card*
      ((univ.filter (fun x => i∈(p x).toFinset)).card-1)) = 2*G.edgeFinset.card +
    ∑ e ∈ univ.image p, (univ.filter (fun x => p x=e)).card*
      ((univ.filter (fun x => p x=e)).card-1) := by
  classical
  let f (x : V) := (p x).toFinset
  have eq (x y : V) (hxy : x≠y) : (f x ∩ f y).card =
      (if G.Adj x y then 1 else 0 : ℕ) + (if p x=p y then 1 else 0) := by
    have adj := rep.adj _ (mem_univ _) _ (mem_univ _) hxy
    by_cases hp : p x=p y
    · have he : f x=f y := congrArg Sym2.toFinset hp
      have hadj : G.Adj x y := adj.mpr (by
        rw [hp]
        simp)
      rw [he,inter_self,ite_eq_left hadj,ite_eq_left hp]
      exact (p y).card_toFinset_of_not_isDiag (rep.distinct _ (mem_univ _))
    · rw [ite_eq_right hp,Nat.add_zero]
      by_cases hg : G.Adj x y
      · have hi := Finset.not_disjoint_iff_nonempty_inter.mp (adj.mp hg)
        have one := distinct_endpairs_inter_le_one hp
        have pos := card_pos.mpr hi
        rw [ite_eq_left hg]
        change 0 < (f x ∩ f y).card at pos
        change (f x ∩ f y).card ≤ 1 at one
        omega
      · have hd : Disjoint (f x) (f y) := Classical.not_not.mp (fun hn => hg (adj.mpr hn))
        rw [ite_eq_right hg,disjoint_iff_inter_eq_empty.mp hd,card_empty]
  have neis (x : V) : (∑ y ∈ univ.erase x, if G.Adj x y then 1 else 0 : ℕ) = G.degree x := by
    rw [sum_boole,filter_erase,erase_eq_of_notMem (by simp)]
    rw [← G.card_neighborFinset_eq_degree]
    change (univ.filter (G.Adj x)).card=(G.neighborFinset x).card
    apply congrArg Finset.card
    ext y
    simp [G.mem_neighborFinset]
  have parallel := common_label_sum (fun x => {p x}) (univ.image p)
    (fun x => singleton_subset_iff.mpr (mem_image_of_mem p (mem_univ x)))
  have simpPair (x y : V) : (({p x} : Finset (Sym2 L)) ∩ {p y}).card =
      if p x=p y then 1 else 0 := by
    by_cases h : p x=p y <;> simp [h]
  simp only [mem_singleton,simpPair] at parallel
  have weights (e : Sym2 L) : (univ.filter fun x => e=p x)=(univ.filter fun x => p x=e) := by
    ext x
    simp [eq_comm]
  simp_rw [weights] at parallel
  rw [common_label_sum _ C hC,← G.sum_degrees_eq_twice_card_edges,parallel,←sum_add_distrib]
  apply sum_congr rfl
  intro x _
  rw [← neis x,←sum_add_distrib]
  exact sum_congr rfl fun y hy => eq x y (mem_erase.mp hy).1.symm

/-- For a simple endpoint graph the correction for parallel pairs vanishes. -/
theorem LineRepresentation.edge_count_of_injective {G : SimpleGraph V} [DecidableRel G.Adj]
    {p : V → Sym2 L} (rep : LineRepresentation G univ p) (C : Finset L)
    (hC : ∀ x, (p x).toFinset ⊆ C) (hp : Function.Injective p) :
    (∑ i ∈ C, (univ.filter (fun x => i∈(p x).toFinset)).card*
      ((univ.filter (fun x => i∈(p x).toFinset)).card-1)) = 2*G.edgeFinset.card := by
  rw [rep.edge_count C hC]
  have cap (e : Sym2 L) : (univ.filter (fun x => p x=e)).card ≤ 1 :=
    card_le_one.mpr fun x hx y hy => hp ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm)
  simp only [Nat.sub_eq_zero_of_le (cap _),Nat.mul_zero,sum_const_zero,Nat.add_zero]

end Erdos617
