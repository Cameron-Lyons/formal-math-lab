module

public import Erdos617.IndependentSets
public import Erdos617.ColorGraph

@[expose] public section

namespace Erdos617

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

omit [DecidableEq V] in
/-- An r-clique of one color is a maximum independent set in every other color. -/
theorem full_clique_maximum_in_other_color (c : Sym2 V → Fin r) (hb : Balanced c) {k j : Fin r}
    (hjk : j≠k) {C : Finset V} (hC : (colorGraph c k).IsNClique r C) :
    (colorGraph c j).IsMaximumIndepSet C := by
  refine ⟨fun x hx y hy hxy ha => hjk (ha.2.symm.trans (hC.isClique hx hy hxy).2),?_⟩
  intro I hi
  by_contra! large
  obtain ⟨T,hTI,hT⟩ := exists_subset_card_eq (s:=I) (show r+1 ≤ I.card by rw [hC.card_eq] at large; omega)
  obtain ⟨u,hu,v,hv,huv,he⟩ := hb T hT j
  exact hi (hTI hu) (hTI hv) huv ⟨huv,he⟩

/-- Count the foreign colors for which an outside vertex has a unique
neighbor on the specified full clique. Each such color supplies one anchor. -/
theorem full_line_unique_spoke_count (hr : 2 ≤ r) (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r)
    {C : Finset V} (hC : (colorGraph c k).IsNClique r C) {x : V} (hx : x ∉ C) :
    r-2+(if (C.filter ((colorGraph c k).Adj x)).Nonempty then 1 else 0) ≤
      ∑ j ∈ univ.erase k, (C.filter fun i => C.filter ((colorGraph c j).Adj x)={i}).card := by
  classical
  let N (j : Fin r) := C.filter ((colorGraph c j).Adj x)
  have low (j : Fin r) (hj : j ∈ univ.erase k) :
      2 ≤ (N j).card+(C.filter fun i => N j={i}).card := by
    have hI := full_clique_maximum_in_other_color c hb (mem_erase.mp hj).1 hC
    have pos : 0<(N j).card := by
      by_contra! h
      have ind := independent_insert_of_nonadjacent _ hI.isIndepSet x (by
        intro y hy hadj
        exact (Nat.not_lt_of_ge h) (card_pos.mpr ⟨y,mem_filter.mpr ⟨hy,hadj⟩⟩))
      have bound := hI.maximum _ ind
      rw [card_insert_of_notMem hx] at bound
      omega
    by_cases h : (N j).card=1
    · obtain ⟨i,hi⟩ := card_eq_one.mp h
      have hiN : i ∈ N j := hi ▸ mem_singleton_self _
      have right : 0<(C.filter fun a => N j={a}).card :=
        card_pos.mpr ⟨i,mem_filter.mpr ⟨(mem_filter.mp hiN).1,hi⟩⟩
      omega
    · omega
  have equal (j : Fin r) : N j=C.filter (fun i => c s(x,i)=j) := by
    ext i
    by_cases hi : i∈C
    · have ne : x≠i := fun h => hx (h ▸ hi)
      simp [N,hi,ne]
    · simp [N,hi]
  have all : ∑ j,(N j).card = r := by
    simp only [equal,sum_card_fiberwise_eq_card_filter,filter_true_of_mem (fun _ _ => mem_univ _),hC.card_eq]
  have split := sum_erase_add univ (fun j => (N j).card) (mem_univ k)
  have lower := sum_le_sum low
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id,card_erase_of_mem (mem_univ k),
    card_univ,Fintype.card_fin] at lower
  change r-2+(if (N k).Nonempty then 1 else 0) ≤ ∑ j∈univ.erase k,(C.filter fun i => N j={i}).card
  split <;> rename_i h
  · have := card_pos.mpr h
    omega
  · omega

/-- In a balanced coloring every full monochromatic clique meets at least
r−2 further full cliques in other colors. Every outside vertex sending an
edge of the original color into the clique increases the lower bound by one. -/
theorem full_clique_propagation (hr : 2 ≤ r) (hn : Fintype.card V=r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r) (C : Finset V)
    (hC : (colorGraph c k).IsNClique r C) :
    ∃ P : Finset (Finset V),
      r-2+(Cᶜ.filter (fun x => (C.filter ((colorGraph c k).Adj x)).Nonempty)).card ≤ P.card ∧
      ∀ A ∈ P, (A∩C).card=1 ∧ ∃ j ≠ k, (colorGraph c j).IsNClique r A := by
  classical
  let F := univ.erase k
  let Z := F ×ˢ C
  let N (j : Fin r) (x : V) := C.filter ((colorGraph c j).Adj x)
  let B (a : Fin r × V) := Cᶜ.filter (fun x => N a.1 x={a.2})
  let A (a : Fin r × V) := insert a.2 (B a)
  let T := Z.filter (fun a => (A a).card=r)
  let K := Cᶜ.filter fun x => (N k x).Nonempty
  have acl (a : Fin r × V) (ha : a∈Z) : (colorGraph c a.1).IsClique (A a : Set V) :=
    private_clique _ C (full_clique_maximum_in_other_color c hb (mem_erase.mp (mem_product.mp ha).1).1 hC)
      a.2 (mem_product.mp ha).2
  have split (a : Fin r × V) (ha : a∈Z) : A a ∩ C={a.2} := by
    ext x
    have hi : a.2∈C := (mem_product.mp ha).2
    simp only [A,B,mem_inter,mem_insert,mem_filter,mem_compl,mem_singleton]
    grind
  have same {U : Finset V} {i j : Fin r} (hU : U.card=r)
      (hz : (colorGraph c i).IsClique (U : Set V)) (hw : (colorGraph c j).IsClique (U : Set V)) : i=j := by
    obtain ⟨x,hx,y,hy,hxy⟩ := one_lt_card.mp (by omega : 1<U.card)
    exact (hz hx hy hxy).2.symm.trans (hw hx hy hxy).2
  have inj : Set.InjOn A (T : Set (Fin r × V)) := by
    intro a ha b hb' he
    obtain ⟨hZa,hnA⟩ := mem_filter.mp ha
    obtain ⟨hZb,_⟩ := mem_filter.mp hb'
    have hs := (split a hZa).symm.trans ((congrArg (· ∩ C) he).trans (split b hZb))
    exact Prod.ext (same hnA (acl a hZa) (he ▸ acl b hZb)) (singleton_inj.mp hs)
  refine ⟨T.image A,?_,?_⟩
  · rw [card_image_of_injOn inj]
    have row (a : Fin r × V) (ha : a∈Z) : (B a).card ≤ (r-2)+(if (A a).card=r then 1 else 0) := by
      have ne : a.2 ∉ B a := fun h => (mem_compl.mp (mem_filter.mp h).1) (mem_product.mp ha).2
      have sz : (A a).card=(B a).card+1 := card_insert_of_notMem ne
      have cap : (A a).card ≤ r := by
        by_contra! high
        obtain ⟨U,hU,hnU⟩ := exists_subset_card_eq (s:=A a) (show r+1≤(A a).card by omega)
        obtain ⟨x,hx,y,hy,hxy,he⟩ := hb U hnU k
        exact (mem_erase.mp (mem_product.mp ha).1).1 (((acl a ha) (hU hx) (hU hy) hxy).2.symm.trans he)
      split <;> omega
    have upper := sum_le_sum row
    simp only [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id,sum_boole] at upper
    change (∑ a∈Z,(B a).card) ≤ Z.card*(r-2)+T.card at upper
    have count (j : Fin r) : (∑ x∈Cᶜ,(C.filter fun i => N j x={i}).card) = ∑ i∈C,(B (j,i)).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun x i => N j x={i})
    have per (x : V) (hx : x∈Cᶜ) :
        r-2+(if (N k x).Nonempty then 1 else 0) ≤ ∑ j∈F,(C.filter fun i => N j x={i}).card :=
      full_line_unique_spoke_count hr c hb k hC (mem_compl.mp hx)
    have lower := sum_le_sum per
    rw [sum_comm (s:=Cᶜ) (t:=F)] at lower
    simp_rw [count] at lower
    simp only [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id,sum_boole] at lower
    rw [←sum_product'] at lower
    change Cᶜ.card*(r-2)+K.card ≤ ∑ a∈Z,(B a).card at lower
    have total := lower.trans upper
    have hnC := C.card_add_card_compl
    rw [hC.card_eq,hn] at hnC
    have hZ : Z.card=(r-1)*r := by simp [Z,F,hC.card_eq]
    rw [hZ] at total
    have gap : Cᶜ.card=(r-1)*r+1 := by
      have e := congrArg (·*r) (show r-1+1=r by omega)
      rw [Nat.add_mul,Nat.one_mul] at e
      rw [pow_two] at hnC
      omega
    rw [gap,Nat.add_mul,Nat.one_mul] at total
    change r-2+K.card ≤ T.card
    omega
  · intro U hU
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hU
    obtain ⟨ha,hnA⟩ := mem_filter.mp ha
    exact ⟨by rw [split a ha]; simp, a.1, (mem_erase.mp (mem_product.mp ha).1).1, acl a ha,hnA⟩

end Erdos617
