import Erdos617.SimpleLineWitness
import Erdos617.FullCliqueEndpoints

namespace Erdos617

open Finset SimpleGraph

variable {V L : Type*} [Fintype V] [DecidableEq L]

/-- Vertices of the line graph whose endpoint pair contains i. -/
def lineStar (p : V → Sym2 L) (i : L) : Finset V :=
  univ.filter (fun x => i ∈ (p x).toFinset)

/-- Number of occurrences of an endpoint pair in a line representation. -/
def lineMultiplicity (p : V → Sym2 L) (e : Sym2 L) : ℕ :=
  (univ.filter (fun x => p x=e)).card

/-- Labels whose stars have size strictly below the clique bound. -/
def deficientLineLabels (p : V → Sym2 L) (C : Finset L) (r : ℕ) : Finset L :=
  C.filter (fun i => (lineStar p i).card < r)

/-- A repeated pair has two deficient endpoints when every full star has
distinct endpoint pairs. -/
theorem repeated_endpoints_are_deficient (p : V → Sym2 L) (C : Finset L) (r : ℕ)
    (hcover : ∀ x, (p x).toFinset ⊆ C) (hsize : ∀ i ∈ C, (lineStar p i).card ≤ r)
    (hfull : ∀ i ∈ C, (lineStar p i).card=r → Set.InjOn p (↑(lineStar p i) : Set V))
    {x : V} (hm : 2 ≤ lineMultiplicity p (p x)) :
    (p x).toFinset ⊆ deficientLineLabels p C r := by
  intro i hi
  have hC := hcover x hi
  refine mem_filter.mpr ⟨hC,?_⟩
  by_contra! hn
  have inj := hfull i hC (le_antisymm (hsize i hC) hn)
  have small : lineMultiplicity p (p x) ≤ 1 := by
    apply card_le_one.mpr
    intro y hy z hz
    have hye := (mem_filter.mp hy).2
    have hze := (mem_filter.mp hz).2
    exact inj (mem_filter.mpr ⟨mem_univ _,hye ▸ hi⟩) (mem_filter.mpr ⟨mem_univ _,hze ▸ hi⟩)
      (hye.trans hze.symm)
  omega

/-- Each deficient label accounts for at least one missing incidence. -/
theorem deficient_line_label_count (p : V → Sym2 L) (C : Finset L) (r : ℕ)
    (hc : C.card ≤ 2*r+1) (hsize : ∀ i ∈ C, (lineStar p i).card ≤ r)
    (hcount : (∑ i∈C,(lineStar p i).card)=2*(r^2+1)) :
    (deficientLineLabels p C r).card ≤ r-2 := by
  classical
  have per (i : L) (hi : i∈C) :
      (lineStar p i).card + (if (lineStar p i).card < r then 1 else 0) ≤ r := by
    split <;> have := hsize i hi <;> omega
  have bound := sum_le_sum per
  simp only [sum_add_distrib,sum_const,sum_boole,nsmul_eq_mul,Nat.cast_id,hcount] at bound
  change 2*(r^2+1)+(deficientLineLabels p C r).card ≤ C.card*r at bound
  have cap := Nat.mul_le_mul_right r hc
  have eq : (2*r+1)*r=2*r^2+r := by ring
  rw [eq] at cap
  omega

/-- Each vertex represented by a repeated pair contributes both of its
ends to the incidence sum on deficient labels. -/
theorem repeated_line_incidence (p : V → Sym2 L) (D : Finset L)
    (hnd : ∀ x, ¬(p x).IsDiag)
    (hdef : ∀ x, 2 ≤ lineMultiplicity p (p x) → (p x).toFinset ⊆ D) :
    2*(univ.filter fun x => 2 ≤ lineMultiplicity p (p x)).card ≤ ∑ i ∈ D,(lineStar p i).card := by
  classical
  let X := univ.filter fun x => 2 ≤ lineMultiplicity p (p x)
  have pair (x : V) (hx : x∈X) : (D.filter fun i => i∈(p x).toFinset).card=2 := by
    rw [filter_mem_eq_inter,inter_eq_right.mpr (hdef x (mem_filter.mp hx).2)]
    exact Sym2.card_toFinset_of_not_isDiag _ (hnd x)
  have total : (∑ x∈X,(D.filter fun i => i∈(p x).toFinset).card) =
      ∑ i ∈ D, (X.filter fun x => i∈(p x).toFinset).card :=
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
  have hi := sum_le_sum (s:=D) fun i _ =>
    card_le_card (filter_subset_filter (fun x => i∈(p x).toFinset) (subset_univ X))
  rw [sum_congr rfl pair,sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_comm] at total
  exact total.le.trans hi

/-- A cap on edge multiplicities bounds the ordered parallel pairs by a
multiple of the number of vertices with repeated endpoint pairs. -/
theorem parallel_pairs_le_repeated (p : V → Sym2 L) (M : ℕ) (hm : ∀ e, lineMultiplicity p e ≤ M+1) :
    (∑ e ∈ univ.image p,lineMultiplicity p e*(lineMultiplicity p e-1)) ≤
      M*(univ.filter fun x => 2 ≤ lineMultiplicity p (p x)).card := by
  classical
  let E := univ.image p
  let T := E.filter fun e => 2 ≤ lineMultiplicity p e
  have per (e : Sym2 L) (_ : e∈E) :
      lineMultiplicity p e*(lineMultiplicity p e-1) ≤
        if 2≤lineMultiplicity p e then M*lineMultiplicity p e else 0 := by
    split
    · have mul := Nat.mul_le_mul_left (lineMultiplicity p e) (show lineMultiplicity p e-1≤M by have := hm e; omega)
      simpa [Nat.mul_comm] using mul
    · have z : lineMultiplicity p e-1=0 := by omega
      simp [z]
  have count := sum_le_sum per
  rw [←sum_filter,←mul_sum] at count
  have fib := sum_card_fiberwise_eq_card_filter (univ : Finset V) T p
  change (∑ e ∈ T,lineMultiplicity p e)=(univ.filter fun x => p x∈T).card at fib
  have eq : (univ.filter fun x => p x∈T)=univ.filter fun x => 2≤lineMultiplicity p (p x) := by
    ext x
    simp [T,E]
  rw [eq] at fib
  change (∑ e∈E,lineMultiplicity p e*(lineMultiplicity p e-1))≤M*(∑ e∈T,lineMultiplicity p e) at count
  rwa [fib] at count

/-- Under a triple multiplicity cap, each repeated pair contributes at most
twice its multiplicity to the ordered parallel-pair count. -/
theorem parallel_pairs_le_twice_repeated (p : V → Sym2 L) (hm : ∀ e, lineMultiplicity p e ≤ 3) :
    (∑ e ∈ univ.image p,lineMultiplicity p e*(lineMultiplicity p e-1)) ≤
      2*(univ.filter fun x => 2 ≤ lineMultiplicity p (p x)).card :=
  parallel_pairs_le_repeated p 2 hm

/-- Upper bound for the number of ordered parallel pairs when every full
star is injective and each endpoint pair occurs at most three times. -/
theorem line_parallel_upper_of_three (p : V → Sym2 L) (C : Finset L) (r : ℕ)
    (hc : C.card ≤ 2*r+1) (hcover : ∀ x, (p x).toFinset ⊆ C) (hnd : ∀ x, ¬(p x).IsDiag)
    (hsize : ∀ i ∈ C, (lineStar p i).card ≤ r)
    (hcount : (∑ i∈C,(lineStar p i).card)=2*(r^2+1))
    (hfull : ∀ i ∈ C, (lineStar p i).card=r → Set.InjOn p (↑(lineStar p i) : Set V))
    (hm : ∀ e, lineMultiplicity p e ≤ 3) :
    (∑ e ∈ univ.image p,lineMultiplicity p e*(lineMultiplicity p e-1)) ≤ (r-2)*r := by
  let D := deficientLineLabels p C r
  have cap := deficient_line_label_count p C r hc hsize hcount
  have hi := repeated_line_incidence p D hnd (fun _ h => repeated_endpoints_are_deficient p C r hcover hsize hfull h)
  have bounded := sum_le_sum (s:=D) fun i hx => hsize i (mem_filter.mp hx).1
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at bounded
  exact (parallel_pairs_le_twice_repeated p hm).trans (hi.trans (bounded.trans (Nat.mul_le_mul_right r cap)))


/-- A star in the endpoint graph induces a clique in its line graph. -/
theorem LineRepresentation.star_isClique {G : SimpleGraph V} {p : V → Sym2 L}
    (rep : LineRepresentation G univ p) (i : L) : G.IsClique (lineStar p i : Set V) := by
  intro x hx y hy hxy
  exact (rep.adj _ (mem_univ _) _ (mem_univ _) hxy).mpr
    (not_disjoint_iff.mpr ⟨i,(mem_filter.mp hx).2,(mem_filter.mp hy).2⟩)

variable [DecidableEq V] {r : ℕ}

/-- The deficient labels support every repeated pair under a balanced coloring.
The remaining labels have full stars with distinct endpoint pairs. -/
theorem line_label_data (hr : 3 ≤ r) (hn : Fintype.card V = r^2+1) (c : Sym2 V → Fin r)
    (hb : Balanced c) (k : Fin r) (p : V → Sym2 L) (rep : LineRepresentation (colorGraph c k) univ p) :
    ∃ C : Finset L, C.card ≤ 2*r+1 ∧ (∀ x, (p x).toFinset ⊆ C) ∧
      (∀ i, (lineStar p i).card ≤ r) ∧
      (∀ i ∈ C, (lineStar p i).card = r → Set.InjOn p (↑(lineStar p i) : Set V)) ∧
      (∑ i ∈ C,(lineStar p i).card) = 2*(r^2+1) ∧
      (deficientLineLabels p C r).card ≤ r-2 ∧
      ∀ x, 2 ≤ lineMultiplicity p (p x) → (p x).toFinset ⊆ deficientLineLabels p C r := by
  classical
  have h := line_minimal_obstruction_top hr hn c hb k p rep
  obtain ⟨C,hc,hcover⟩ := h.line_support (by omega) hb p rep
  have cover (x : V) := hcover x (mem_univ _)
  obtain ⟨j,hjk⟩ : ∃ j : Fin r,j ≠ k := by
    have ne : (univ.erase k).Nonempty := card_pos.mp (by simp; omega)
    exact ne.imp fun _ hj => (mem_erase.mp hj).1
  have size (i : L) : (lineStar p i).card ≤ r := by
    by_contra! large
    obtain ⟨I,hI,hnI⟩ := exists_subset_card_eq (s:= lineStar p i) large
    obtain ⟨x,hx,y,hy,hxy,he⟩ := hb I hnI j
    exact hjk (he.symm.trans ((rep.star_isClique i) (hI hx) (hI hy) hxy).2)
  have full (i : L) (_ : i∈C) (hf : (lineStar p i).card=r) :
      Set.InjOn p (↑(lineStar p i) : Set V) :=
    h.injOn_full_clique hb p rep _ (subset_univ _) ⟨rep.star_isClique i,hf⟩
  have count : (∑ i ∈ C,(lineStar p i).card) = 2*(r^2+1) :=
    (sum_stars C p _ rep cover).trans (by rw [hn])
  exact ⟨C,hc,cover,size,full,count,deficient_line_label_count p C r hc (fun i _ => size i) count,
    fun _ hm => repeated_endpoints_are_deficient p C r cover (fun i _ => size i) full hm⟩

/-- The missing-color conclusion holds if one color contains a spanning line
graph with independence number at most r and edge multiplicities at most three. -/
theorem missing_of_line_subgraph_of_multiplicity_le_three (hr : 3 ≤ r)
    (hn : Fintype.card V = r^2+1) (c : Sym2 V → Fin r) (k : Fin r) (H : SimpleGraph V)
    (hsub : H ≤ colorGraph c k) (hα : H.indepNum ≤ r) (p : V → Sym2 L)
    (rep : LineRepresentation H univ p) (hm : ∀ e, lineMultiplicity p e ≤ 3) :
    ∃ (S : Finset V) (l : Fin r), l ≠ k ∧ S.card = r+1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u,v) ≠ l := by
  apply missing_of_spanning_subgraph (by omega) c k H hsub hα
  intro d eq
  by_contra no
  have hb := balanced_of_no_witness d no
  have rep' : LineRepresentation (colorGraph d k) univ p := eq ▸ rep
  obtain ⟨C,hc,cover,size,full,count,_,_⟩ := line_label_data hr hn d hb k p rep'
  have upper := line_parallel_upper_of_three p C r hc cover (fun x => rep'.distinct x (mem_univ _))
    (fun i _ => size i) count full hm
  have lower := line_parallel_excess hr hn d hb k p rep'
  change (r-2)*(r+1) ≤ ∑ e ∈ univ.image p,lineMultiplicity p e*(lineMultiplicity p e-1) at lower
  rw [Nat.mul_add,Nat.mul_one] at lower
  omega

end Erdos617
