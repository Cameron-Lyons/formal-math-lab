import Erdos617.OnePairMerge
import Erdos617.ColorGraph

namespace Erdos617

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every (s+1)-set contains one of the prescribed unordered edges. -/
def HitsEdges (s : ℕ) (E : Finset (Sym2 V)) : Prop :=
  ∀ A : Finset V, A.card=s+1 → ∃ x∈A, ∃ y∈A, x≠y ∧ s(x,y)∈E

/-- A color hitting all (s+1)-sets contains an inclusion-minimal family
with this property. Every retained edge has a witness set where it is the
only retained edge. -/
theorem minimal_hitting_edges {r s : ℕ} (d : Sym2 V → Fin r) (j : Fin r)
    (hit : HitsPalette d s {j}) :
    ∃ E : Finset (Sym2 V), (∀ e∈E,d e=j) ∧ HitsEdges s E ∧
      ∀ e∈E, ∃ A : Finset V, A.card=s+1 ∧
        ∀ x∈A, ∀ y∈A, x≠y → s(x,y)∈E → s(x,y)=e := by
  classical
  let K := univ.filter fun e => d e=j
  have hh : HitsEdges s K := by
    intro A n
    obtain ⟨x,hx,y,hy,ne,he⟩ := hit A n
    exact ⟨x,hx,y,hy,ne,mem_filter.mpr ⟨mem_univ _,mem_singleton.mp he⟩⟩
  let F := K.powerset.filter (HitsEdges s)
  have nonempty : F.Nonempty := ⟨K,mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl,hh⟩⟩
  obtain ⟨E,hE,least⟩ := F.exists_min_image card nonempty
  have ⟨sub,good⟩ := mem_filter.mp hE
  refine ⟨E,fun e he => (mem_filter.mp (mem_powerset.mp sub he)).2,good,?_⟩
  intro e he
  have missing : ¬HitsEdges s (E.erase e) := by
    intro yes
    have lim := least _ (mem_filter.mpr ⟨mem_powerset.mpr ((erase_subset ..).trans (mem_powerset.mp sub)),yes⟩)
    exact (card_erase_lt_of_mem he).not_ge lim
  unfold HitsEdges at missing
  push Not at missing
  obtain ⟨A,sz,only⟩ := missing
  refine ⟨A,sz,fun x hx y hy ne edge => ?_⟩
  by_contra distinct
  exact only x hx y hy ne (mem_erase.mpr ⟨distinct,edge⟩)

/-- On a square where s-color balance is impossible, every choice of
s−1 disjoint hitting edge families covers all pairs of some (s+1)-set.
Here each family is selected from its own original color. -/
theorem covered_set_for_any_thinning {r s : ℕ} (d : Sym2 V → Fin r)
    (nof : ∀ g : Sym2 V → Fin s, ¬Balanced g) (J : Finset (Fin r)) (size : J.card+1=s)
    (E : J → Finset (Sym2 V)) (color : ∀ j e, e∈E j → d e=j.val) (hits : ∀ j, HitsEdges s (E j)) :
    ∃ T : Finset V, T.card=s+1 ∧
      ∀ x∈T, ∀ y∈T, x≠y → ∃ j : J, s(x,y)∈E j := by
  classical
  let lab := Fintype.equivFinOfCardEq (show Fintype.card (Option J)=s by simpa using size)
  let assign (e : Sym2 V) : Option J := if h : ∃ j : J,e∈E j then some h.choose else none
  let g := lab ∘ assign
  have keep (j : J) (e : Sym2 V) (he : e∈E j) : assign e=some j := by
    have ex : ∃ j : J,e∈E j := ⟨j,he⟩
    have eq : ex.choose=j := Subtype.ext ((color _ e ex.choose_spec).symm.trans (color j e he))
    dsimp only [assign]
    rw [dite_eq_left ex,eq]
  by_contra! fail
  apply nof g
  intro T sizeT col
  obtain ⟨u,eu⟩ := lab.surjective col
  cases u with
  | none =>
    obtain ⟨x,hx,y,hy,ne,unused⟩ := fail T sizeT
    have off : ¬∃ j : J,s(x,y)∈E j := by simpa using unused
    exact ⟨x,hx,y,hy,ne,by change lab (assign s(x,y))=col; dsimp only [assign]; rw [dite_eq_right off]; exact eu⟩
  | some j =>
    obtain ⟨x,hx,y,hy,ne,he⟩ := hits j T sizeT
    exact ⟨x,hx,y,hy,ne,(congrArg lab (keep j _ he)).trans eu⟩

/-- In the two-bad-colors case of descent, the other colors can all be
thinned to essential edges. Some r-set still has every edge in the retained
families, and each edge of that set has an individual witness to its necessity. -/
theorem two_bad_critical_square {r : ℕ} (hr : 2≤r) (d : Sym2 V → Fin r)
    (nof : ∀ g : Sym2 V → Fin (r-1), ¬Balanced g) :
    let good := univ.filter fun j => HitsPalette d (r-1) {j}
    goodᶜ.card=2 → ∃ (E : good → Finset (Sym2 V)) (T : Finset V),
      T.card=r ∧ (∀ j, HitsEdges (r-1) (E j)) ∧ (∀ j e, e∈E j → d e=j.val) ∧
      (∀ x∈T, ∀ y∈T, x≠y → ∃ j, s(x,y)∈E j) ∧
      ∀ j e, e∈E j → ∃ A : Finset V, A.card=r ∧
        ∀ x∈A, ∀ y∈A, x≠y → s(x,y)∈E j → s(x,y)=e := by
  classical
  intro J two
  have all := card_compl_add_card J
  rw [Fintype.card_fin,two] at all
  have sz : J.card+1=r-1 := by omega
  have pred : r-1+1=r := by omega
  have present (j : J) : HitsPalette d (r-1) {j.val} := (mem_filter.mp j.prop).2
  choose E color hits critical using fun j : J => minimal_hitting_edges d j.val (present j)
  obtain ⟨T,n,allT⟩ := covered_set_for_any_thinning d nof J sz E color hits
  exact ⟨E,T,n.trans pred,hits,color,allT,fun j e he => by simpa only [pred] using critical j e he⟩

end Erdos617
