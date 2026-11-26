module

public import Erdos617.MinimalObstruction
public import Erdos617.MultiCoverDegree
public import Erdos617.MultiCoverPartition

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V ι : Type*} [DecidableEq V] [Fintype ι] [DecidableEq ι]

private theorem qfold_counts (S : Finset V) (B : ι → Finset V) {q : ℕ}
    (hsub : ∀ i, B i ⊆ S) (hcov : ∀ x ∈ S, (univ.filter fun i => x ∈ B i).card = q) :
    (∑ i, (B i).card) = q*S.card ∧
      ∀ i, (∑ j ∈ univ.erase i, (B i ∩ B j).card) = (q-1)*(B i).card := by
  classical
  constructor
  · have hc : (∑ i, (S.filter fun x => x ∈ B i).card) =
        ∑ x ∈ S, (univ.filter fun i => x ∈ B i).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun i x => x ∈ B i)
    have left (i : ι) : S.filter (fun x => x ∈ B i) = B i := by
      rw [filter_mem_eq_inter, inter_eq_right.mpr (hsub i)]
    simpa only [left, sum_congr rfl hcov, sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm S.card] using hc
  · intro i
    have hc : (∑ j ∈ univ.erase i, ((B i).filter fun x => x ∈ B j).card) =
        ∑ x ∈ B i, ((univ.erase i).filter fun j => x ∈ B j).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun j x => x ∈ B j)
    have one (x : V) (hx : x ∈ B i) : ((univ.erase i).filter fun j => x ∈ B j).card = q-1 := by
      have hi : i ∈ univ.filter (fun j => x ∈ B j) := mem_filter.mpr ⟨mem_univ i,hx⟩
      rw [filter_erase, card_erase_of_mem hi, hcov x (hsub i hx)]
    simpa only [filter_mem_eq_inter, sum_congr rfl one, sum_const, nsmul_eq_mul,
      Nat.cast_id, Nat.mul_comm (B i).card] using hc

private def tightGraph (B : ι → Finset V) (r t : ℕ) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ (B i ∪ B j).card ≤ r+t-1
  symm.symm i j h := ⟨h.1.symm, union_comm (B i) (B j) ▸ h.2⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private theorem tight_degree_bound (B : ι → Finset V) {q r t : ℕ}
    (hq : 2 ≤ q) (ht : 2 ≤ t) (hn : Fintype.card ι=q*t+1)
    (hsize : ∀ i, (B i).card ≤ r-1) (hr : 2 ≤ r)
    (hcount : (∑ i,(B i).card)=q*(t*r+1))
    (hrow : ∀ i,(∑ j ∈ univ.erase i,(B i ∩ B j).card)=(q-1)*(B i).card)
    [DecidableRel (tightGraph B r t).Adj] (i : ι) : (tightGraph B r t).degree i ≤ q-1 := by
  classical
  let δ (j : ι) := r-(B j).card
  have dpos (j : ι) : 1 ≤ δ j := by dsimp [δ]; have := hsize j; omega
  have cancel (j : ι) : (B j).card+δ j=r := by dsimp [δ]; have := hsize j; omega
  have dsum : (∑ j,δ j)+q=r := by
    have all := sum_congr (s₁ := univ) rfl fun j _ => cancel j
    simp only [sum_add_distrib,sum_const,card_univ,hn,nsmul_eq_mul,Nat.cast_id,hcount] at all
    nlinarith only [all]
  by_contra! hlarge
  have deg := (tightGraph B r t).card_neighborFinset_eq_degree i
  obtain ⟨J,hJ,hJcard⟩ := exists_subset_card_eq (s := (tightGraph B r t).neighborFinset i)
    (show q ≤ _ by omega)
  have neigh (j : ι) (hj : j ∈ J) := ((tightGraph B r t).mem_neighborFinset i j).mp (hJ hj)
  have hi : i ∉ J := fun h => (neigh i h).1 rfl
  have Jsub : J ⊆ univ.erase i := by
    intro j hj
    exact mem_erase.mpr ⟨(neigh j hj).1.symm,mem_univ _⟩
  have cost (j : ι) (hj : j ∈ J) :
      (B i).card ≤ (B i ∩ B j).card+δ j+(t-1) := by
    have hb := (neigh j hj).2
    have hu := card_union_add_card_inter (B i) (B j)
    have hc := cancel j
    omega
  have lower := sum_le_sum (s := J) cost
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id,hJcard] at lower
  have overlaps := (sum_le_sum_of_subset (f := fun j => (B i ∩ B j).card) Jsub).trans_eq (hrow i)
  let T := univ \ insert i J
  have tcnt : T.card=q*t-q := by
    rw [show T = univ \ insert i J by rfl,card_sdiff_of_subset (subset_univ _),
      card_insert_of_notMem hi,hJcard,card_univ,hn]
    omega
  have small : T.card ≤ ∑ j ∈ T,δ j := by simpa using sum_le_sum (s := T) fun j _ => dpos j
  have rest := sum_sdiff (f := δ) (subset_univ (insert i J))
  rw [sum_insert hi] at rest
  change (∑ j ∈ T,δ j)+(δ i+∑ j ∈ J,δ j)=∑ j,δ j at rest
  have hqt : q ≤ q*t := by simpa using Nat.mul_le_mul_left q (show 1≤t by omega)
  have hc := cancel i
  have hqa := congrArg (·*(B i).card) (show q-1+1=q by omega)
  have hta := congrArg (q*·) (show t-1+1=t by omega)
  rw [Nat.add_mul,Nat.one_mul] at hqa
  rw [Nat.mul_add,Nat.mul_one] at hta
  omega

/-- Exact multi-covers by qt+1 cliques are incompatible with balance on tr+1
vertices if each covering clique has size less than r. -/
theorem no_exact_qfold_clique_cover {q r t : ℕ} (hr : 2 ≤ r) (hq : 2 ≤ q) (ht : 2 ≤ t)
    (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r) (S : Finset V) (B : ι → Finset V)
    (hn : Fintype.card ι=q*t+1) (hS : S.card=t*r+1) (hsub : ∀ i, B i ⊆ S)
    (hcl : ∀ i, (colorGraph c k).IsClique (B i : Set V)) (hsize : ∀ i, (B i).card ≤ r-1) :
    ¬ ∀ x ∈ S,(univ.filter fun i => x ∈ B i).card=q := by
  classical
  intro hcov
  let G := colorGraph c k
  let T := tightGraph B r t
  obtain ⟨hcount,hrow⟩ := qfold_counts S B hsub hcov
  rw [hS] at hcount
  have deg (i : ι) : T.degree i ≤ q-1 := tight_degree_bound B hq ht hn hsize hr hcount hrow i
  apply no_partition_into_q_cliques T hq hn deg
  intro i
  obtain ⟨x,hxi,hxdeg⟩ := exists_low_vertex_of_qfold_cover c hb k S B hr hq ht hn hS hsub hcl hcov i
  let C := univ.filter fun j => x ∈ B j
  refine ⟨C,mem_filter.mpr ⟨mem_univ _,hxi⟩,?_,hcov x (hsub i hxi)⟩
  intro j hj z hz hjz
  have hxj := (mem_filter.mp hj).2
  have hxz := (mem_filter.mp hz).2
  change j ≠ z ∧ (B j ∪ B z).card ≤ r+t-1
  refine ⟨hjz, ?_⟩
  have inside (a : ι) (hxa : x ∈ B a) : B a ⊆ insert x (S.filter (G.Adj x)) := by
    intro y hy
    by_cases he : y=x
    · exact mem_insert.mpr (Or.inl he)
    · exact mem_insert.mpr (Or.inr (mem_filter.mpr ⟨hsub a hy,hcl a hxa hy (Ne.symm he)⟩))
  have hc := card_le_card (union_subset (inside j hxj) (inside z hxz))
  have plus := card_insert_le x (S.filter (G.Adj x))
  change (S.filter (G.Adj x)).card ≤ r+t-2 at hxdeg
  omega

/-- A q-fold cover of a first obstruction by cliques of its obstruction color
needs at least qt+2 cliques for every q at least two. -/
theorem MinimalObstruction.qfold_clique_cover_card {q r t : ℕ} {S : Finset V}
    {c : Sym2 V → Fin r} {k : Fin r} (h : MinimalObstruction c k t S)
    (hb : Balanced c) (hq : 2 ≤ q) (ht : 2 ≤ t) (htr : t < r) (B : ι → Finset V)
    (hsub : ∀ i, B i ⊆ S) (hcl : ∀ i, (colorGraph c k).IsClique (B i : Set V))
    (hcover : ∀ x ∈ S, q ≤ (univ.filter fun i => x ∈ B i).card) :
    q*t+2 ≤ Fintype.card ι := by
  classical
  have chooseQ (x : S) : ∃ T ⊆ univ.filter (fun i => x.val ∈ B i), T.card=q :=
    exists_subset_card_eq (hcover x.val x.prop)
  choose f hf hfc using chooseQ
  let U (i : ι) := S.filter (fun x => ∃ hx : x ∈ S, i ∈ f ⟨x,hx⟩)
  have hUB (i : ι) : U i ⊆ B i := by
    intro x hx
    obtain ⟨_,hxS,hi⟩ := mem_filter.mp hx
    exact (mem_filter.mp (hf ⟨x,hxS⟩ hi)).2
  have hUS (i : ι) : U i ⊆ S := (hUB i).trans (hsub i)
  have hUC (i : ι) : (colorGraph c k).IsClique (U i : Set V) := (hcl i).subset (hUB i)
  have hexact (x : V) (hx : x ∈ S) : (univ.filter fun i => x ∈ U i).card=q := by
    have heq : univ.filter (fun i => x ∈ U i) = f ⟨x,hx⟩ := by ext i; simp [U,hx]
    rw [heq,hfc]
  have total := (qfold_counts S U hUS hexact).1
  have size (i : ι) : (U i).card ≤ r-1 := by
    by_contra! hlarge
    obtain ⟨C,hCU,hn⟩ := exists_subset_card_eq (s := U i) (show r ≤ (U i).card by omega)
    exact h.no_clique hb htr C (hCU.trans (hUS i)) ⟨(hUC i).subset hCU,hn⟩
  have upper := sum_le_sum (s := univ) fun i _ => (size i).trans (Nat.sub_le _ _)
  simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,total,h.card_eq] at upper
  have hgt : q*t < Fintype.card ι := by
    by_contra! hsmall
    nlinarith only [upper,Nat.mul_le_mul_right r hsmall,Nat.zero_lt_of_lt hq]
  by_contra! hshort
  exact no_exact_qfold_clique_cover (by omega) hq ht c hb k S U (by omega) h.card_eq hUS hUC size hexact

end Erdos617
