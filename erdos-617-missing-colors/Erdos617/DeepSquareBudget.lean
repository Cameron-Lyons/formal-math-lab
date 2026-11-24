import Erdos617.SquarePaletteBudget
import Erdos617.LocalPaletteEnergy

namespace Erdos617

open Finset SimpleGraph

theorem turan_degree_floor {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ} (hr : 0<r) (cap : G.indepNum≤r) :
    (Fintype.card V)^2≤r*(2*G.edgeFinset.card+Fintype.card V) := by
  classical
  have cf : Gᶜ.CliqueFree (r+1) := by
    intro C hC
    have ind := G.isNClique_compl.mp hC
    have bound := ind.isIndepSet.card_le_indepNum.trans cap
    rw [ind.card_eq] at bound
    omega
  have up := (Nat.mul_le_mul_left (2*r) cf.card_edgeFinset_le).trans mul_turanNumber_le
  have dis : Disjoint G.edgeFinset Gᶜ.edgeFinset := disjoint_edgeFinset.mpr disjoint_compl_right
  have all : G.edgeFinset ∪ Gᶜ.edgeFinset=(⊤ : SimpleGraph V).edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
      by_cases h : G.Adj u v
      · simp [mem_union,mem_edgeFinset,h,h.ne]
      · simp [mem_union,mem_edgeFinset,h]
  have eq := congrArg Finset.card all
  rw [card_union_of_disjoint dis,card_edgeFinset_top_eq_card_choose_two] at eq
  have pred : r-1+1=r := by omega
  nlinarith only [up,congrArg (2*r*·) eq,congrArg (r*·) (twice_choose_two (Fintype.card V)),
    congrArg (·*(Fintype.card V)^2) pred]

/-- On s²+1 vertices let g be the number of colors of independence number
at most s. The remaining colors have independence number at most s+m.
If no original color contains an (s+1)-clique, this bound on g holds at
every depth m. -/
theorem deep_square_good_count {V : Type*} [Fintype V] [DecidableEq V]
    {s m : ℕ} (hs : 2≤s) (hn : Fintype.card V=s^2+1) (c : Sym2 V → Fin (s+m))
    (hb : Balanced c) (hcl : ∀ k,(colorGraph c k).CliqueFree (s+1)) :
    let g := (univ.filter fun k => (colorGraph c k).indepNum≤s).card
    g*(m*s^3+2*s^2+4*m*s) ≤ (s+m)*(s+m-1)*(s^2+1)+g*(s+m+1) := by
  classical
  let r := s+m
  let n := Fintype.card V
  let E (k : Fin (s+m)) := (colorGraph c k).edgeFinset.card
  let T := univ.filter fun k => (colorGraph c k).indepNum≤s
  let e (k : Fin (s+m)) := r*(2*E k+n)
  have high (k : Fin (s+m)) (hk : k∈T) : r*(s^3+4*s)≤e k+r := by
    have rank := (mem_filter.mp hk).2
    have le := edge_bound_of_clique_and_indep_caps (colorGraph c k) hs
      (by simpa [pow_two] using hn : Fintype.card V=s*s+1)
      (fun I ind => by have t := ind.isIndepSet.card_le_indepNum; rw [ind.card_eq] at t; omega)
      (hcl k)
    have pos : 1≤s*s.choose 2+2*s := by omega
    have bound := Nat.sub_add_cancel pos
    change s*s.choose 2+2*s-1≤E k at le
    have num : s^3+4*s ≤ (2*E k+n)+1 := by
      change n=s^2+1 at hn
      nlinarith only [congrArg (s*·) (twice_choose_two s),le,bound,hn]
    simpa only [e,Nat.mul_add,Nat.mul_one] using Nat.mul_le_mul_left r num
  have low (k : Fin (s+m)) (_ : k∈Tᶜ) : n^2≤e k :=
    turan_degree_floor _ (by dsimp [r]; omega) (balanced_indepNum_le c hb k)
  have goods := sum_le_sum high
  have bads := sum_le_sum low
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,sum_add_distrib] at goods bads
  have split := sum_add_sum_compl T e
  have eq : ∑ k,e k = r*(2*n.choose 2+r*n) := by
    simp only [e,←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul,card_univ,
      Fintype.card_fin,Nat.cast_id,E,sum_color_edges,n,r]
  rw [eq] at split
  have nt : T.card+Tᶜ.card=r := by simp [r]
  have total : T.card*(r*(s^3+4*s))+Tᶜ.card*n^2 ≤ r*(2*n.choose 2+r*n)+T.card*r := by omega
  have cancel := congrArg (·*n^2) nt
  have pairs := congrArg (r*·) (twice_choose_two n)
  change n=s^2+1 at hn
  change T.card*(m*s^3+2*s^2+4*m*s) ≤ r*(r-1)*(s^2+1)+T.card*(r+1)
  have pred : r-1+1=r := by dsimp [r]; omega
  have mv := congrArg (r*n*·) pred
  rw [hn] at total cancel pairs mv
  dsimp [r] at total cancel pairs mv ⊢
  nlinarith only [total,cancel,pairs,mv]

/-- Without a clique cap, either the same budget applies or a monochromatic
(s+1)-clique itself avoids all other colors, leaving at most one good color. -/
theorem deep_square_good_count_unconditional {V : Type*} [Fintype V] [DecidableEq V]
    {s m : ℕ} (hs : 2≤s) (hn : Fintype.card V=s^2+1) (c : Sym2 V → Fin (s+m))
    (hb : Balanced c) :
    let g := (univ.filter fun k => (colorGraph c k).indepNum≤s).card
    g*(m*s^3+2*s^2+4*m*s) ≤ (s+m)*(s+m-1)*(s^2+1)+g*(s+m+1) := by
  classical
  by_cases hcl : ∀ k,(colorGraph c k).CliqueFree (s+1)
  · exact deep_square_good_count hs hn c hb hcl
  push Not at hcl
  obtain ⟨j,notfree⟩ := hcl
  obtain ⟨A,cl⟩ := not_forall.mp notfree
  have full : (colorGraph c j).IsNClique (s+1) A := of_not_not cl
  let T := univ.filter fun k => (colorGraph c k).indepNum≤s
  have sub : T⊆{j} := by
    intro i hi
    have rank := (mem_filter.mp hi).2
    obtain ⟨x,hx,y,hy,ne,edge⟩ := (hitsPalette_singleton_iff_indepNum c s i).mpr rank A full.card_eq
    exact mem_singleton.mpr ((mem_singleton.mp edge).symm.trans (full.isClique hx hy ne).2)
  have small : T.card≤1 := (card_le_card sub).trans_eq (card_singleton j)
  intro g
  change T.card*(m*s^3+2*s^2+4*m*s) ≤ (s+m)*(s+m-1)*(s^2+1)+T.card*(s+m+1)
  rcases show T.card=0 ∨ T.card=1 by omega with emp|one
  · simp [emp]
  · rw [one,one_mul,one_mul]
    obtain ⟨z,ez⟩ := Nat.exists_eq_add_of_le hs
    zify [show 1≤s+m by omega]
    apply sub_nonneg.mp
    rw [ez]; push_cast; ring_nf; positivity

private theorem deep_square_int {s m g : ℕ} (hs : 2≤s)
    (bound : g*(m*s^3+2*s^2+4*m*s) ≤ (s+m)*(s+m-1)*(s^2+1)+g*(s+m+1)) :
    (g:ℤ)*(m*s^3+2*s^2+4*m*s-(s+m+1)) ≤ (s+m)*(s+m-1)*(s^2+1) := by
  zify [show 1≤s+m by omega] at bound
  linarith only [bound]

/-- At depth two, strictly fewer than half of the original colors pass
the reduced independence test. -/
theorem deep_square_two {V : Type*} [Fintype V] [DecidableEq V] {s : ℕ} (hs : 2≤s)
    (hn : Fintype.card V=s^2+1) (c : Sym2 V → Fin (s+2)) (hb : Balanced c)
    : 2*(univ.filter fun k => (colorGraph c k).indepNum≤s).card < s+2 := by
  let g := (univ.filter fun k => (colorGraph c k).indepNum≤s).card
  have bound := deep_square_int (g:=g) hs (deep_square_good_count_unconditional hs hn c hb)
  change (g:ℤ)*(2*s^3+2*s^2+4*2*s-(s+2+1)) ≤ (s+2)*(s+2-1)*(s^2+1) at bound
  by_contra! many
  change s+2≤2*g at many
  obtain ⟨z,eq⟩ := Nat.exists_eq_add_of_le hs
  zify at many
  have coeff : (0:ℤ)≤2*s^3+2*s^2+4*2*s-(s+2+1) := by rw [eq]; push_cast; ring_nf; positivity
  have mul := mul_le_mul_of_nonneg_right many coeff
  rw [eq] at mul bound
  push_cast at mul bound
  nlinarith only [mul,bound,Nat.cast_nonneg (α:=ℤ) z,Nat.cast_nonneg (α:=ℤ) (z*z)]

/-- At depth three, three times the number of colors passing the reduced
test is at most the original palette size plus one. -/
theorem deep_square_three {V : Type*} [Fintype V] [DecidableEq V] {s : ℕ} (hs : 2≤s)
    (hn : Fintype.card V=s^2+1) (c : Sym2 V → Fin (s+3)) (hb : Balanced c)
    : 3*(univ.filter fun k => (colorGraph c k).indepNum≤s).card ≤ s+4 := by
  let g := (univ.filter fun k => (colorGraph c k).indepNum≤s).card
  have bound := deep_square_int (g:=g) hs (deep_square_good_count_unconditional hs hn c hb)
  change (g:ℤ)*(3*s^3+2*s^2+4*3*s-(s+3+1)) ≤ (s+3)*(s+3-1)*(s^2+1) at bound
  by_contra! many
  change s+4<3*g at many
  have large : (s:ℤ)+5≤3*g := by exact_mod_cast (show s+5≤3*g by omega)
  obtain ⟨z,eq⟩ := Nat.exists_eq_add_of_le hs
  have coeff : (0:ℤ)≤3*s^3+2*s^2+4*3*s-(s+3+1) := by rw [eq]; push_cast; ring_nf; positivity
  have mul := mul_le_mul_of_nonneg_right large coeff
  have gap : ((s:ℤ)+5)*(3*s^3+2*s^2+4*3*s-(s+3+1)) > 3*((s+3)*(s+3-1)*(s^2+1)) := by
    apply sub_pos.mp
    rw [eq]; push_cast; ring_nf; positivity
  linarith only [mul,bound,gap]

private theorem merger_copies {V : Type*} [Fintype V] [DecidableEq V] {s m : ℕ}
    (hs : 2≤s) (hn : Fintype.card V=s^2+1) (c : Sym2 V → Fin (s+m)) (f : Fin (s+m) → Fin s)
    (hb : Balanced (f ∘ c)) :
    s ≤ m+(univ.filter fun k => (colorGraph c k).indepNum≤s).card ∧
    ∀ k,(colorGraph c k).CliqueFree (s+1) := by
  classical
  let T := univ.filter fun k => (colorGraph c k).indepNum≤s
  let F (j : Fin s) := univ.filter fun k => f k=j
  have sz : s+1≤(univ : Finset V).card := by
    rw [card_univ,hn]
    have := Nat.mul_le_mul_left s (show 1≤s by omega)
    simpa [pow_two] using Nat.add_le_add_right this 1
  obtain ⟨S,_,Ssize⟩ := exists_subset_card_eq sz
  have pos (j : Fin s) : 1≤(F j).card := by
    obtain ⟨x,_,y,_,_,e⟩ := hb S Ssize j
    exact card_pos.mpr ⟨_,mem_filter.mpr ⟨mem_univ (c s(x,y)),e⟩⟩
  have total : ∑ j,(F j).card=s+m := by simp [F,sum_card_fiberwise_eq_card_filter]
  let J := univ.filter fun j => (F j).card=1
  have sub : J⊆T.image f := by
    intro j hj
    obtain ⟨k,eq⟩ := card_eq_one.mp (mem_filter.mp hj).2
    have single {l : Fin (s+m)} (hl : f l=j) : l=k :=
      mem_singleton.mp (eq ▸ (show l∈F j from mem_filter.mpr ⟨mem_univ _,hl⟩))
    have hit : HitsPalette c s {k} := by
      intro D n
      obtain ⟨x,hx,y,hy,ne,col⟩ := hb D n j
      exact ⟨x,hx,y,hy,ne,mem_singleton.mpr (single col)⟩
    have fk : k∈F j := eq ▸ mem_singleton_self _
    exact mem_image.mpr ⟨k,mem_filter.mpr ⟨mem_univ _,(hitsPalette_singleton_iff_indepNum ..).mp hit⟩,
      (mem_filter.mp fk).2⟩
  have few := (card_le_card sub).trans card_image_le
  have bad := sum_le_sum (s:=Jᶜ) (f:=fun _ => 2) (g:=fun j => (F j).card) (fun j hj => by
    have neq : (F j).card≠1 := fun eq => (mem_compl.mp hj) (mem_filter.mpr ⟨mem_univ _,eq⟩)
    have := pos j
    omega)
  have ones := sum_le_sum (s:=J) (f:=fun _ => 1) (fun j _ => pos j)
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at bad ones
  have div := sum_add_sum_compl J (fun j => (F j).card)
  rw [total] at div
  have cards : J.card+Jᶜ.card=s := by simp
  refine ⟨?_,?_⟩
  · change s≤m+T.card
    omega
  · intro k A cl
    obtain ⟨j,hj⟩ : (univ.erase (f k)).Nonempty := card_pos.mp (by simp; omega)
    obtain ⟨x,hx,y,hy,xy,eq⟩ := hb A cl.card_eq j
    exact (mem_erase.mp hj).1 (eq.symm.trans (congrArg f (cl.isClique hx hy xy).2))

/-- Relabeling the edges of a balanced coloring cannot produce another
balanced coloring on s²+1 vertices with s target colors if the palette loses
at least two colors and the target exceeds the number removed by at least four.
The choice of the restricted vertex set is arbitrary. -/
theorem no_deep_square_palette_merger {V : Type*} [Fintype V] [DecidableEq V] {s m : ℕ}
    (hm : 2≤m) (hs : m+4≤s) (hn : Fintype.card V=s^2+1) (c : Sym2 V → Fin (s+m))
    (hb : Balanced c) (f : Fin (s+m) → Fin s) : ¬Balanced (f ∘ c) := by
  classical
  intro merged
  obtain ⟨count,cl⟩ := merger_copies (by omega) hn c f merged
  let g := (univ.filter fun k => (colorGraph c k).indepNum≤s).card
  change s≤m+g at count
  have bound := deep_square_int (g:=g) (by omega) (deep_square_good_count (by omega) hn c hb cl)
  obtain ⟨k,em⟩ := Nat.exists_eq_add_of_le hm
  obtain ⟨z,es⟩ := Nat.exists_eq_add_of_le hs
  have low : (4:ℤ)+z≤g := by exact_mod_cast (show 4+z≤g by omega)
  let D : ℤ := m*s^3+2*s^2+4*m*s-(s+m+1)
  change (g:ℤ)*D ≤ _ at bound
  have nonneg : 0≤D := by dsimp [D]; rw [es,em]; push_cast; ring_nf; positivity
  have high := (mul_le_mul_of_nonneg_right low nonneg).trans bound
  have gap : (4+(z:ℤ))*D > ((s:ℤ)+m)*(s+m-1)*(s^2+1) := by
    apply sub_pos.mp
    dsimp [D]
    rw [es,em]; push_cast; ring_nf; positivity
  exact gap.not_ge high

end Erdos617
