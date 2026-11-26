module

public import Erdos617.LineWitness
public import Erdos617.LineEdgeCount

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V L : Type*} [Fintype V] [DecidableEq V] [DecidableEq L] {r : ℕ}

/-- In a balanced coloring, a line representation can first fail the
independence bound only on the entire graph at parameter r. -/
theorem line_minimal_obstruction_top (hr : 3 ≤ r) (hn : Fintype.card V = r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r) (p : V → Sym2 L)
    (rep : LineRepresentation (colorGraph c k) univ p) : MinimalObstruction c k r univ := by
  refine ⟨by simpa [pow_two] using hn,?_,?_⟩
  · intro I _ hi
    obtain ⟨u,hu,v,hv,huv,he⟩ := hb I hi.card_eq k
    exact hi.isIndepSet hu hv huv ⟨huv,he⟩
  · intro s hs W _ hnW
    by_contra! hbad
    obtain ⟨t,T,ht,_,h⟩ := minimalObstruction_of_failure hnW hbad
    apply h.not_line_representation hb (h.two_le_parameter hr hb (by omega)) (by omega) p
    exact ⟨fun x _ => rep.distinct x (mem_univ _),fun x _ y _ => rep.adj x (mem_univ _) y (mem_univ _)⟩

omit [DecidableEq V] in
theorem sum_stars (C : Finset L) (p : V → Sym2 L) (G : SimpleGraph V)
    (rep : LineRepresentation G univ p) (hC : ∀ x, (p x).toFinset ⊆ C) :
    (∑ i ∈ C, (univ.filter (fun x => i ∈ (p x).toFinset)).card) = 2*Fintype.card V := by
  have eq := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s:=C) (t:=univ) (fun i x => i ∈ (p x).toFinset)
  have two (x : V) : (C.filter (fun i => i ∈ (p x).toFinset)).card = 2 := by
    rw [filter_mem_eq_inter,inter_eq_right.mpr (hC x)]
    exact (p x).card_toFinset_of_not_isDiag (rep.distinct x (mem_univ _))
  change (∑ i ∈ C, (univ.filter (fun x => i ∈ (p x).toFinset)).card) =
    ∑ x, (C.filter (fun i => i ∈ (p x).toFinset)).card at eq
  simpa only [two,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,Nat.mul_comm] using eq

private theorem integer_tangent (b r : ℕ) :
    2*(r-1)*b ≤ b*(b-1)+r*(r-1) := by
  cases r with
  | zero => simp
  | succ n =>
    cases b with
    | zero => simp
    | succ z =>
      simp only [Nat.add_one_sub_one]
      rcases le_or_gt n z with h | h
      · obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le h
        nlinarith only [Nat.zero_le (u*u),Nat.zero_le u]
      · obtain ⟨u,hu⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt h)
        rw [hu]
        nlinarith only [Nat.zero_le (u*u),Nat.zero_le u]

private theorem foreign_sum {r : ℕ} (hr : 3 ≤ r) (hn : Fintype.card V = r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r) :
    (r-1)*(r*r.choose 2+2*r-1) + (colorGraph c k).edgeFinset.card ≤ (r^2+1).choose 2 := by
  let E (i : Fin r) := (colorGraph c i).edgeFinset.card
  have per (j : Fin r) (hj : j ∈ univ.erase k) : r*r.choose 2+2*r-1 ≤ E j := by
    apply edge_bound_of_clique_and_indep_caps (colorGraph c j) (by omega : 2≤r) (by simpa [pow_two] using hn)
    · intro I hi
      obtain ⟨u,hu,v,hv,huv,he⟩ := hb I hi.card_eq j
      exact hi.isIndepSet hu hv huv ⟨huv,he⟩
    · intro I hi
      obtain ⟨u,hu,v,hv,huv,he⟩ := hb I hi.card_eq k
      exact (mem_erase.mp hj).1 ((hi.isClique hu hv huv).2.symm.trans he)
  have s := sum_le_sum per
  simp only [sum_const,card_erase_of_mem (mem_univ k),card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_id] at s
  have total := sum_color_edges c
  change ∑ j, E j = _ at total
  rw [←sum_erase_add _ _ (mem_univ k),hn] at total
  exact (Nat.add_le_add_right s _).trans_eq total

private theorem collision_arithmetic {r a e d : ℕ} (hr : 3 ≤ r)
    (hstars : 2*(r-1)*(2*(r^2+1)) ≤ a+(2*r+1)*(r*(r-1)))
    (hcount : a = 2*e+d)
    (he : (r-1)*(r*r.choose 2+2*r-1)+e ≤ (r^2+1).choose 2) :
    (r-2)*(r+1) ≤ d := by
  obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le hr
  let R := 3+u
  let m := R*R.choose 2+2*R-1
  have dm : m+1 = R*R.choose 2+2*R := by dsimp [m,R]; omega
  have x := congrArg (fun n => 2*(R-1)*n) dm
  have b := congrArg (fun n => (R-1)*R*n) (twice_choose_two R)
  have t := twice_choose_two (R^2+1)
  change (R-1)*m+e ≤ _ at he
  change 2*(R-1)*(2*(R^2+1)) ≤ a+(2*R+1)*(R*(R-1)) at hstars
  change (R-2)*(R+1) ≤ d
  simp only [show R-1=2+u by dsimp [R]; omega,show R-2=1+u by dsimp [R]; omega] at *
  dsimp only [R] at *
  nlinarith only [he,hstars,hcount,x,b,t]

/-- A line representation in a balanced coloring has at least the stated
number of ordered pairs of parallel edges. -/
theorem line_parallel_excess (hr : 3 ≤ r) (hn : Fintype.card V = r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r) (p : V → Sym2 L)
    (rep : LineRepresentation (colorGraph c k) univ p) :
    (r-2)*(r+1) ≤ ∑ e ∈ univ.image p,
      (univ.filter (fun x => p x=e)).card*((univ.filter (fun x => p x=e)).card-1) := by
  classical
  have h := line_minimal_obstruction_top hr hn c hb k p rep
  obtain ⟨C,hc,hcov⟩ := h.line_support (by omega) hb p rep
  have cover (x : V) := hcov x (mem_univ _)
  let b (i : L) := (univ.filter (fun x => i ∈ (p x).toFinset)).card
  have sumB : (∑ i ∈ C, b i) = 2*(r^2+1) := (sum_stars C p _ rep cover).trans (hn ▸ rfl)
  have st := sum_le_sum (s:=C) (fun i _ => integer_tangent (b i) r)
  rw [←mul_sum,sumB,sum_add_distrib] at st
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at st
  apply collision_arithmetic hr (st.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hc) _))
    (rep.edge_count C cover) (foreign_sum hr hn c hb k)

/-- A color that contains a spanning line graph of a simple graph with
independence number at most r forces some (r+1)-set to miss another color. -/
theorem missing_of_simple_line_subgraph (hr : 3 ≤ r) (hn : Fintype.card V = r^2+1)
    (c : Sym2 V → Fin r) (k : Fin r) (H : SimpleGraph V)
    (hsub : H ≤ colorGraph c k) (hα : H.indepNum ≤ r)
    (p : V → Sym2 L) (rep : LineRepresentation H univ p) (hp : Function.Injective p) :
    ∃ (S : Finset V) (l : Fin r), l ≠ k ∧ S.card = r+1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u,v) ≠ l := by
  apply missing_of_spanning_subgraph (by omega) c k H hsub hα
  intro d eq
  by_contra no
  have collision := line_parallel_excess hr hn d (balanced_of_no_witness d no) k p (eq ▸ rep)
  have atmost (e : Sym2 L) : (univ.filter (fun x => p x=e)).card ≤ 1 :=
    card_le_one.mpr fun x hx y hy => hp ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm)
  simp only [fun e => Nat.sub_eq_zero_of_le (atmost e),Nat.mul_zero,sum_const_zero] at collision
  exact (Nat.mul_pos (by omega : 0<r-2) (by omega : 0<r+1)).not_ge collision

end Erdos617
