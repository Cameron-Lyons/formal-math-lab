import Erdos617.OddBags

namespace Erdos617

open Finset SimpleGraph

/-- In any balanced coloring with at least six colors, an (r+1)-set
containing no r-clique in the target color has two disjoint edges avoiding it. -/
theorem two_missing_pairs_of_six_le {V : Type*} [DecidableEq V] {r : ℕ} {c : Sym2 V → Fin r} {k : Fin r}
    {B : Finset V} (hr : 6≤r) (hb : Balanced c) (n : B.card=r+1)
    (no : ∀ T⊆B, ¬(colorGraph c k).IsNClique r T) :
    ∃ a∈B, ∃ b∈B, ∃ u∈B, ∃ v∈B, a≠b ∧ u≠v ∧ Disjoint ({a,b}:Finset V) {u,v} ∧
      ¬(colorGraph c k).Adj a b ∧ ¬(colorGraph c k).Adj u v := by
  classical
  let G := colorGraph c k
  let N (a : V) := B.filter fun b => a≠b ∧ ¬G.Adj a b
  have avoid (a : V) (ha : a∈B) :
      ∃ u∈B.erase a, ∃ v∈B.erase a, u≠v ∧ ¬G.Adj u v := by
    by_contra! clique
    apply no (B.erase a) (erase_subset ..)
    exact ⟨fun u hu v hv uv => clique u hu v hv uv, by rw [card_erase_of_mem ha,n,Nat.add_sub_cancel]⟩
  by_contra fail
  have low (a : V) (ha : a∈B) : (N a).card ≤ 2 := by
    obtain ⟨u,hu,v,hv,uv,noUV⟩ := avoid a ha
    have sub : N a ⊆ {u,v} := by
      intro b hB
      obtain ⟨hb,ab,noAB⟩ := mem_filter.mp hB
      by_contra notin
      apply fail
      have notA : a∉({u,v}:Finset V) := by
        simp only [mem_insert,mem_singleton,not_or]
        exact ⟨Ne.symm (mem_erase.mp hu).1,Ne.symm (mem_erase.mp hv).1⟩
      refine ⟨a,ha,b,hb,u,mem_of_mem_erase hu,v,mem_of_mem_erase hv,ab,uv,?_,noAB,noUV⟩
      apply Finset.disjoint_left.mpr
      intro w hw
      rcases mem_insert.mp hw with rfl | hw
      · exact notA
      · exact mem_singleton.mp hw ▸ notin
    exact (card_le_card sub).trans card_le_two
  obtain ⟨z,hz⟩ := card_pos.mp (show 0<B.card by omega)
  obtain ⟨a,ha,b,hb',ab,non⟩ := avoid z hz
  have aB := mem_of_mem_erase ha
  have bB := mem_of_mem_erase hb'
  let R (z : V) := (N z).image fun w => (z,w)
  have memR {u v : V} (hv : v∈B) (hne : u≠v) (nh : ¬G.Adj u v) : (u,v)∈R u :=
    mem_image_of_mem _ (mem_filter.mpr ⟨hv,hne,nh⟩)
  have cap := foreign_pair_budget c hb k B (R a ∪ R b) (by
    intro u hu v hv uv col
    have nv : ¬G.Adj u v := fun e => col e.2
    by_cases au : a=u
    · subst u; exact Or.inl (mem_union_left _ (memR hv uv nv))
    by_cases av : a=v
    · subst v; exact Or.inr (mem_union_left _ (memR hu uv.symm (fun e => nv e.symm)))
    by_cases bu : b=u
    · subst u; exact Or.inl (mem_union_right _ (memR hv uv nv))
    by_cases bv : b=v
    · subst v; exact Or.inr (mem_union_right _ (memR hu uv.symm (fun e => nv e.symm)))
    exfalso
    apply fail
    refine ⟨a,aB,b,bB,u,hu,v,hv,ab,uv,?_,non,nv⟩
    simp [Finset.disjoint_left,au,av,bu,bv])
  have aCap : (R a).card≤2 := card_image_le.trans (low a aB)
  have bCap : (R b).card≤2 := card_image_le.trans (low b bB)
  have comb := card_union_le (R a) (R b)
  rw [n,Nat.mul_add,Nat.mul_one] at cap
  omega

/-- Inside eight vertices of a balanced seven-color coloring with no full
clique of the prescribed color there are two vertex-disjoint edges avoiding it. -/
theorem two_missing_pairs {V : Type*} [DecidableEq V] {c : Sym2 V → Fin 7} {k : Fin 7}
    {B : Finset V} (hb : Balanced c) (n : B.card=8)
    (no : ∀ T⊆B, ¬(colorGraph c k).IsNClique 7 T) :
    ∃ a∈B, ∃ b∈B, ∃ u∈B, ∃ v∈B, a≠b ∧ u≠v ∧ Disjoint ({a,b}:Finset V) {u,v} ∧
      ¬(colorGraph c k).Adj a b ∧ ¬(colorGraph c k).Adj u v :=
  two_missing_pairs_of_six_le (by decide) hb n no

end Erdos617
