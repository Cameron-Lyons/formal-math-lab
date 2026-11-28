module

public import Erdos617.LineFive
public import Erdos617.ParallelPairBudget

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V L : Type*} [Fintype V] [DecidableEq L]

/-- Two specified deficient stars consume their entire deficits in addition
to the one incidence already charged for every other deficient label. -/
theorem deficient_count_of_two_stars (p : V → Sym2 L) (C : Finset L) {r : ℕ}
    (hn : C.card ≤ 2*r+1) (hs : ∀ i, (lineStar p i).card ≤ r)
    (hcount : (∑ i ∈ C,(lineStar p i).card)=2*(r^2+1))
    {i j : L} (hi : i ∈ deficientLineLabels p C r) (hj : j ∈ deficientLineLabels p C r)
    (hne : i ≠ j) :
    (deficientLineLabels p C r).card + (r-(lineStar p i).card) + (r-(lineStar p j).card) ≤ r := by
  classical
  let D := deficientLineLabels p C r
  let δ (v : L) := r-(lineStar p v).card
  have hiC := (mem_filter.mp hi).1
  have hjC := (mem_filter.mp hj).1
  have per (v : L) (_ : v ∈ C) : (lineStar p v).card+δ v=r := by
    dsimp [δ]
    have := hs v
    omega
  have total := sum_congr rfl per
  simp only [sum_add_distrib,hcount,sum_const,nsmul_eq_mul,Nat.cast_id] at total
  change 2*(r^2+1)+(∑ v∈C,δ v)=C.card*r at total
  have hmax := Nat.mul_le_mul_right r hn
  rw [show (2*r+1)*r=2*r^2+r by ring] at hmax
  let T := (D.erase i).erase j
  have hj' : j ∈ D.erase i := mem_erase.mpr ⟨Ne.symm hne,hj⟩
  have hcnt : T.card+2=D.card := by
    have h₁ := card_erase_add_one (s:=D) hi
    have h₂ := card_erase_add_one hj'
    dsimp [T]
    omega
  have bound := sum_le_sum (s:=T) (f:=fun _ => 1) (g:=δ) (fun v hv => by
    have hm : v ∈ D := mem_of_mem_erase (mem_of_mem_erase hv)
    have lt := (mem_filter.mp hm).2
    change (lineStar p v).card < r at lt
    dsimp [δ]
    omega)
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at bound
  have h₁ := sum_erase_add D δ hi
  have h₂ := sum_erase_add (D.erase i) δ hj'
  have h₃ := sum_le_sum_of_subset (f:=δ) (show D ⊆ C from filter_subset ..)
  change D.card+δ i+δ j ≤ r
  change T.card ≤ ∑ v∈(D.erase i).erase j,δ v at bound
  omega

variable [DecidableEq V] {r M : ℕ}

/-- An endpoint representation of one color in a balanced coloring must
have multiplicities growing at least on the scale of r to the power 2/3. -/
theorem line_multiplicity_cubic_bound (hr : 3 ≤ r) (hn : Fintype.card V = r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r) (p : V → Sym2 L)
    (rep : LineRepresentation (colorGraph c k) univ p) (hm : ∀ e, lineMultiplicity p e ≤ M) :
    16*((r-2)*(r+1)) ≤ (M-1)*(9*(M-1)^2+16) := by
  classical
  obtain ⟨C,hc,cover,size,inj,count,_,deficient⟩ := line_label_data hr hn c hb k p rep
  obtain ⟨i,hi,j,hj,hij,hdup,hheavy⟩ :=
    exists_heavy_parallel_pair_strict hr hn c hb k p rep C hc cover
  let D := deficientLineLabels p C r
  obtain ⟨x,hx⟩ := card_pos.mp (show 0<(univ.filter (fun x => p x=s(i,j))).card by
    change 2≤(univ.filter (fun x => p x=s(i,j))).card at hdup
    omega)
  have hx' := (mem_filter.mp hx).2
  have ends : {i,j} ⊆ D := by
    have h := deficient x (hx' ▸ hdup)
    simpa only [hx',Sym2.toFinset_mk_eq] using h
  have hiD : i∈D := ends (by simp)
  have hjD : j∈D := ends (by simp)
  have capped := deficient_count_of_two_stars p C hc size count hiD hjD hij
  change D.card + (r-(lineStar p i).card)+(r-(lineStar p j).card) ≤ r at capped
  have mcap := hm s(i,j)
  have dcap : 2*(D.card-1) ≤ 3*(M-1) := by omega
  have exactCount : C.card=2*r+1 := by
    have cap := sum_le_sum (s:=C) fun i _ => size i
    rw [count,sum_const,nsmul_eq_mul] at cap
    by_contra! bad
    have short : C.card ≤ 2*r := by omega
    nlinarith only [cap,Nat.mul_le_mul_right r short]
  have lower := line_deficient_parallel_bound hr hn c hb k p rep C exactCount cover
    (fun i _ => size i) inj (card_pos.mpr ⟨i,hiD⟩) M hm
  change 4*((r-2)*(r+1)) ≤ (M-1)*((D.card-1)^2+4) at lower
  have hs := Nat.pow_le_pow_left dcap 2
  have upper : 4*((D.card-1)^2+4) ≤ 9*(M-1)^2+16 := by nlinarith only [hs]
  calc
    16*((r-2)*(r+1)) = 4*(4*((r-2)*(r+1))) := by ring
    _ ≤ 4*((M-1)*((D.card-1)^2+4)) := Nat.mul_le_mul_left 4 lower
    _ = (M-1)*(4*((D.card-1)^2+4)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ upper

/-- The conjectured conclusion holds when a spanning line subgraph with
independence number at most r has multiplicity below the cubic threshold. -/
theorem missing_of_line_subgraph_of_multiplicity_range (hr : 3 ≤ r) (hn : Fintype.card V = r^2+1)
    (c : Sym2 V → Fin r) (k : Fin r) (H : SimpleGraph V) (hsub : H ≤ colorGraph c k)
    (hα : H.indepNum ≤ r) (p : V → Sym2 L) (rep : LineRepresentation H univ p)
    (hm : ∀ e, lineMultiplicity p e ≤ M) (hbound : (M-1)*(9*(M-1)^2+16)<16*((r-2)*(r+1))) :
    ∃ (S : Finset V) (l : Fin r), l ≠ k ∧ S.card=r+1 ∧
      ∀ u∈S, ∀ v∈S, u≠v → c s(u,v)≠l := by
  apply missing_of_spanning_subgraph (by omega) c k H hsub hα
  intro d eq
  by_contra no
  exact hbound.not_ge (line_multiplicity_cubic_bound hr hn d (balanced_of_no_witness d no) k p (eq ▸ rep) hm)

end Erdos617
