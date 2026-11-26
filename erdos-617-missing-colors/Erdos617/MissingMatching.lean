module

public import Erdos617.OddBags
public import Erdos617.MatchingCertificate
public import Erdos617.RankEdges

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] {r b : ℕ} {c : Sym2 V → Fin r} {k : Fin r}

private theorem matching_at_order [Fintype V] (hr : 2*b+3≤r) (hb : Balanced c)
    (n : Fintype.card V=r+b) (no : ∀ A : Finset V, ¬(colorGraph c k).IsNClique r A) :
    ∃ F : Finset (Sym2 V), F.card=b+1 ∧ (∀ e∈F,e∈(colorGraph c k)ᶜ.edgeSet) ∧
      (↑F : Set (Sym2 V)).PairwiseDisjoint Sym2.toFinset := by
  classical
  let M := (colorGraph c k)ᶜ
  by_contra fail
  have bound (F : Finset (Sym2 V)) (ed : ∀ e∈F,e∈M.edgeSet)
      (dis : (↑F : Set (Sym2 V)).PairwiseDisjoint Sym2.toFinset) : F.card≤b := by
    by_contra! lg
    obtain ⟨Q,sub,sz⟩ := exists_subset_card_eq (s:=F) (Nat.succ_le_of_lt lg)
    exact fail ⟨Q,sz,fun e he => ed e (sub he),fun _ ha _ hb ne => dis (sub ha) (sub hb) ne⟩
  obtain ⟨X,P,hu,_,inside,cost⟩ := matching_certificate M b bound
  let W := univ \ X
  let d := b-X.card
  have split : X.card+d=b := by dsimp [d]; omega
  have ws : W.card=r+d := by
    have h := card_sdiff_add_card_eq_card (subset_univ X)
    change W.card+X.card=Fintype.card V at h
    omega
  have budget : (∑ A∈P,A.card/2)≤d := by omega
  have lim (A : Finset V) (ha : A∈P) : A.card/2≤d :=
    (single_le_sum (f:=fun C : Finset V => C.card/2) (fun _ _ => Nat.zero_le _) ha).trans budget
  let R (A : Finset V) := (inducedEdgeSet M A).image (fun e : Sym2 V => e.out)
  have lower := foreign_pair_budget c hb k W (P.biUnion R) (by
    intro x hx y hy xy other
    have edge : M.Adj x y := ⟨xy,fun h => other h.2⟩
    obtain ⟨A,ha,xa,ya⟩ := inside x y (mem_sdiff.mp hx).2 (mem_sdiff.mp hy).2 edge
    have pair : (s(x,y) : Sym2 V).out ∈ P.biUnion R := mem_biUnion.mpr ⟨A,ha,
      mem_image_of_mem _ ((mem_inducedEdgeSet M).mpr ⟨xa,ya,edge⟩)⟩
    have rep : s((s(x,y) : Sym2 V).out.1,(s(x,y) : Sym2 V).out.2)=s(x,y) := Quot.out_eq _
    rcases (Sym2.mk_eq_mk_iff (p:=(s(x,y):Sym2 V).out) (q:=(x,y))).mp rep with h|h
    · exact Or.inl (h ▸ pair)
    · change (s(x,y) : Sym2 V).out=(y,x) at h
      exact Or.inr (h ▸ pair))
  have cap (A : Finset V) (ha : A∈P) : (R A).card≤(A.card/2)*(2*d+1) := by
    have le : (R A).card≤blockEdges M A := card_image_le.trans_eq (card_inducedEdgeSet ..)
    have edges : blockEdges M A≤A.card.choose 2 := by
      simpa [blockEdges] using (M.induce (A : Set V)).card_edgeFinset_le_card_choose_two
    let a := A.card/2
    have up : A.card≤2*a+1 := by dsimp [a]; omega
    have ch := Nat.choose_le_choose 2 up
    have eq : (2*a+1).choose 2=a*(2*a+1) := by nlinarith only [twice_choose_two (2*a+1)]
    rw [eq] at ch
    exact (le.trans edges).trans (ch.trans (Nat.mul_le_mul_left a (by have := lim A ha; change a≤d at this; omega)))
  have upper := (card_biUnion_le : (P.biUnion R).card≤∑ A∈P,(R A).card).trans (sum_le_sum cap)
  rw [←sum_mul] at upper
  rw [ws,Nat.mul_add] at lower
  have d0 : d=0 := by
    by_contra nz
    have prod := Nat.mul_lt_mul_of_pos_left (show 2*d+1 < r-1 by omega) (show 0<d by omega)
    have ub := Nat.mul_le_mul_right (2*d+1) budget
    rw [Nat.mul_comm (r-1) d] at lower
    omega
  apply no W
  refine ⟨?_,by omega⟩
  intro x hx y hy xy
  by_contra missing
  obtain ⟨A,ha,xa,ya⟩ := inside x y (mem_sdiff.mp hx).2 (mem_sdiff.mp hy).2 ⟨xy,missing⟩
  have one := lim A ha
  have two := one_lt_card.mpr ⟨x,xa,y,ya,xy⟩
  omega

/-- In a set of r+b vertices with no monochromatic r-clique of color k,
one can find b+1 vertex-disjoint edges avoiding k whenever r>2b+2.
The edges are represented by their unordered pairs of endpoints. -/
theorem missing_matching (hr : 2*b+3≤r) (hb : Balanced c)
    {B : Finset V} (sz : B.card=r+b) (no : ∀ T⊆B, ¬(colorGraph c k).IsNClique r T) :
    ∃ F : Finset (Finset V), F.card=b+1 ∧ (↑F : Set (Finset V)).PairwiseDisjoint id ∧
      ∀ A∈F, A⊆B ∧ ∃ x y : V, x≠y ∧ A={x,y} ∧ ¬(colorGraph c k).Adj x y := by
  classical
  let incl := Function.Embedding.subtype (·∈B)
  let cp (e : Sym2 B) := c (e.map Subtype.val)
  have subset (T : Finset B) : T.map incl⊆B := fun _ hx => T.property_of_mem_map_subtype hx
  obtain ⟨F,cnt,edge,dis⟩ := matching_at_order hr (balanced_pullback c hb incl)
    ((Fintype.card_coe B).trans sz) (k:=k) (fun T hc => no (T.map incl) (subset T)
      ⟨by
        intro x hx y hy xy
        obtain ⟨u,hu,rfl⟩ := mem_map.mp hx
        obtain ⟨v,hv,rfl⟩ := mem_map.mp hy
        exact ⟨xy,(hc.isClique hu hv (fun e => xy (congrArg incl e))).2⟩,
      (card_map _).trans hc.card_eq⟩)
  let T (e : Sym2 B) := e.toFinset.map incl
  have sep (e : Sym2 B) (he : e∈F) (f : Sym2 B) (hf : f∈F) (ne : e≠f) : Disjoint (T e) (T f) :=
    (disjoint_map _).mpr (dis he hf ne)
  have inj : Set.InjOn T F := by
    intro e he f hf eq
    by_contra ne
    have empty := disjoint_self.mp (eq ▸ sep e he f hf ne)
    let x := f.out.1
    have hx : x∈f.toFinset := Sym2.mem_toFinset.mpr (Sym2.out_fst_mem f)
    have mem : incl x∈T f := mem_map.mpr ⟨x,hx,rfl⟩
    simp [empty] at mem
  refine ⟨F.image T,(card_image_of_injOn inj).trans cnt,?_,?_⟩
  · intro A ha B' hb ne
    obtain ⟨e,he,rfl⟩ := mem_image.mp ha
    obtain ⟨f,hf,rfl⟩ := mem_image.mp hb
    exact sep e he f hf (fun eq => ne (congrArg T eq))
  · intro A ha
    obtain ⟨e,he,rfl⟩ := mem_image.mp ha
    refine ⟨subset e.toFinset,?_⟩
    induction e using Sym2.inductionOn with
    | _ x y =>
      have ed : (colorGraph cp k)ᶜ.Adj x y := edge _ he
      have xy : x.val≠y.val := fun e => ed.1 (Subtype.ext e)
      refine ⟨x.val,y.val,xy,?_,fun e => ed.2 ⟨ed.1,e.2⟩⟩
      simp [T,Sym2.toFinset_mk_eq,incl]

end Erdos617
