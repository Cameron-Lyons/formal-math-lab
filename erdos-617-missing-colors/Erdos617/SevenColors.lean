module

public import Erdos617.NestedObstruction
public import Erdos617.SevenCore
public import Erdos617.SevenPairs
public import Erdos617.SevenProfile

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] {c : Sym2 V → Fin 7} {k : Fin 7} {S : Finset V}

/-- The closed-neighborhood reduction of Sneiderman's seven-color argument,
with a subset edge bound on the endpoints of two disjoint missing edges.
See https://github.com/Robby955/erdos-617-fixed-cases/blob/main/r7-r8/main.tex. -/
theorem MinimalObstruction.not_seven_four (h : MinimalObstruction c k 4 S) (hb : Balanced c) :
    False := by
  classical
  let G := colorGraph c k
  obtain ⟨edge,x,hx,degree⟩ := h.seven_edge_profile hb
  let N := S.filter (G.Adj x)
  let B := insert x N
  let W := S \ B
  have sub : B⊆S := insert_subset hx (filter_subset ..)
  have xn : x∉N := by simp [N]
  have sizeB : B.card=8 := by rw [show B=insert x N from rfl,card_insert_of_notMem xn]; exact congrArg (·+1) degree
  have size : S.card=29 := h.card_eq
  have szw := card_sdiff_add_card_eq_card sub
  have sizeW : W.card=21 := by change (S \ B).card=21; omega
  have union : B∪W=S := union_sdiff_of_subset sub
  have apart : Disjoint B W := disjoint_sdiff
  have wS : W⊆S := sdiff_subset
  have rk : rankOn G W≤3 := by
    obtain ⟨I,hI,ind,eq⟩ := exists_max_indep G W
    have nI : x∉I := fun hm => (mem_sdiff.mp (hI hm)).2 (mem_insert_self ..)
    have add := independent_insert_of_nonadjacent G ind x (by
      intro v hv ev
      exact (mem_sdiff.mp (hI hv)).2 (mem_insert_of_mem (mem_filter.mpr ⟨wS (hI hv),ev⟩)))
    have cap := card_le_rankOn G (insert_subset hx (hI.trans wS)) add
    rw [card_insert_of_notMem nI,eq] at cap
    have re : rankOn G S=4 := h.rank_eq (by decide)
    omega
  have res : 76≤blockEdges G W := h.seven_residual_edges hb wS sizeW rk
  have d (y : V) (hy : y∈B) : B.card≤((B∪W).filter (G.Adj y)).card+1 := by
    rw [union,sizeB]
    exact Nat.succ_le_succ (h.degree_ge y (sub hy))
  obtain ⟨cost,ledger,_,_,_,quartet⟩ := block_account_with_subsets G B W apart d
  rw [union,sizeB] at ledger
  norm_num [Nat.choose] at ledger
  change blockEdges G S≤112 at edge
  have cheap : cost≤8 := by omega
  obtain ⟨a,ha,b,hb',u,hu,v,hv,ab,uv,dis,noAB,noUV⟩ := two_missing_pairs hb sizeB
    (fun T ht => h.no_clique hb (by decide) T (ht.trans sub))
  let A : Finset V := {a,b}
  let U : Finset V := {u,v}
  have aB : A⊆B := insert_subset ha (singleton_subset_iff.mpr hb')
  have uB : U⊆B := insert_subset hu (singleton_subset_iff.mpr hv)
  have lim := quartet (A∪U) (union_subset aB uB)
  rw [card_union_of_disjoint dis,sum_union dis,show A.card=2 from card_pair ab,
    show U.card=2 from card_pair uv] at lim
  simp only [sum_pair ab,sum_pair uv] at lim
  norm_num [Nat.choose] at lim
  let out (w : V) := (W.filter (G.Adj w)).card
  change out a+out b+(out u+out v)≤_ at lim
  have split : out a+out b≤7 ∨ out u+out v≤7 := by omega
  rcases split with l|l
  · exact h.seven_no_light_pair hb wS sizeW (sub ha) (sub hb') (disjoint_left.mp apart ha)
      (disjoint_left.mp apart hb') ab noAB l
  · exact h.seven_no_light_pair hb wS sizeW (sub hu) (sub hv) (disjoint_left.mp apart hu)
      (disjoint_left.mp apart hv) uv noUV l

/-- The seven-color case of the Erdős–Gyárfás conjecture. -/
theorem seven_colors [Fintype V] (hn : Fintype.card V=7^2+1)
    (c : Sym2 V → Fin 7) : ∃ (S : Finset V) (k : Fin 7), S.card=7+1 ∧
      ∀ u∈S, ∀ v∈S, u≠v → c s(u,v)≠k := by
  by_contra bad
  have hb := balanced_of_no_witness c bad
  obtain ⟨k,t,S,_,upper,h⟩ := exists_minimalObstruction_ceil_half (by decide) hn c hb
  have lt : t<7 := by omega
  obtain ⟨_,_,_,_,_,_,half,_,two,_⟩ := h.exists_nested_product_obstruction (by decide) hb lt
  obtain rfl : t=4 := by omega
  exact h.not_seven_four hb

end Erdos617
