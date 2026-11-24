import Wall133.Density
import Mathlib.Combinatorics.Enumerative.DoubleCounting

namespace Wall133
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In a core of average degree at least 2m and minimum degree above m,
some vertex has at least m+1 neighbors of degree above m+1, counting
one prescribed neighbor regardless of its degree. -/
theorem core_incidence_contradiction (S : Finset V) (hS : S.Nonempty)
    {m : ℕ} (hm : 3 ≤ m) (hmin : ∀ z : S,m < (G.induce (S : Set V)).degree z)
    (dense : S.card*(2*m) ≤ ∑ z : S,(G.induce (S : Set V)).degree z)
    (test : ∀ a x : S,(G.induce (S : Set V)).Adj a x → ∀ A : Finset S,
      (∀ z∈A,(G.induce (S : Set V)).Adj x z ∧ (z=a ∨ m+1 < (G.induce (S : Set V)).degree z)) →
      A.card ≤ m+1-1) : False := by
  classical
  let H := G.induce (S : Set V)
  let d := m+1
  change S.card*(2*m) ≤ ∑ z : S,H.degree z at dense
  let high := Finset.univ.filter (fun u : S => d < H.degree u)
  let low := Finset.univ.filter (fun u : S => ¬d < H.degree u)
  let B (x : S) := high.filter (H.Adj x)
  have isB (x z : S) : z∈B x ↔ H.Adj x z ∧ d<H.degree z := by simp [B,high,and_comm]
  have small (x : S) : (B x).card ≤ d-2 := by
    have hxdeg := hmin x
    change m < H.degree x at hxdeg
    obtain ⟨u,hu⟩ := (H.degree_pos_iff_exists_adj x).mp (by omega)
    have hle := test u x hu.symm (B x) (fun z hz =>
      ⟨((isB x z).1 hz).1,Or.inr ((isB x z).1 hz).2⟩)
    have ex : ∃ a, H.Adj x a ∧ a ∉ B x := by
      by_contra! h
      have sub : H.neighborFinset x ⊆ B x := fun z hz => h z ((H.mem_neighborFinset _ _).mp hz)
      have hh := Finset.card_le_card sub
      rw [H.card_neighborFinset_eq_degree] at hh
      dsimp [d] at hle
      omega
    obtain ⟨a,ha,ha'⟩ := ex
    have bound := test a x ha.symm (insert a (B x)) (by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | h
      · exact ⟨ha,Or.inl rfl⟩
      · exact ⟨((isB _ _).1 h).1,Or.inr ((isB _ _).1 h).2⟩)
    rw [Finset.card_insert_of_notMem ha'] at bound
    omega
  have highSum : ∑ z∈high,H.degree z ≤ S.card*(d-2) := by
    calc
      _ = ∑ z∈high, (Finset.bipartiteAbove H.Adj Finset.univ z).card := by
        apply Finset.sum_congr rfl
        intro z _
        rw [← H.card_neighborFinset_eq_degree]
        congr 1
        ext u
        simp [Finset.bipartiteAbove]
      _ = ∑ x : S, (B x).card := by
        rw [Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
        apply Finset.sum_congr rfl
        intro x _
        congr 1
        ext z
        simp [B,Finset.bipartiteBelow,H.adj_comm]
      _ ≤ ∑ _x : S, (d-2) := Finset.sum_le_sum (fun x _ => small x)
      _ = _ := by simp
  have lowSum : ∑ z ∈ low, H.degree z ≤ low.card*d := by
    simpa using Finset.sum_le_sum (s := low) (f := fun z : S => H.degree z) (g := fun _ => d)
      (fun z hz => Nat.le_of_not_gt (Finset.mem_filter.mp hz).2)
  have highNe : high.Nonempty := by
    by_contra! h
    have hlow (z : S) : H.degree z ≤ d := by
      by_contra! hh
      have : z∈high := by simp [high, hh]
      simp [h] at this
    have hsum' := Finset.sum_le_sum (s := Finset.univ) (fun z _ => hlow z)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul] at hsum'
    change (∑ z : S,H.degree z) ≤ S.card*d at hsum'
    have := Nat.mul_lt_mul_of_pos_left (show d<2*m by dsimp [d]; omega) hS.card_pos
    omega
  have ce := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun z : S => d<H.degree z)
  change high.card+low.card=Finset.univ.card at ce
  rw [Finset.card_univ,Fintype.card_coe] at ce
  have hlt := Nat.mul_lt_mul_of_pos_right
    (show low.card<S.card by have := highNe.card_pos; omega) (show 0<d by dsimp [d]; omega)
  have split := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset S) (fun z : S => d<H.degree z) (fun z : S => H.degree z)
  change (∑ z∈high,H.degree z)+(∑ z∈low,H.degree z)=∑ z : S,H.degree z at split
  have e : S.card*(d-2)+S.card*d=S.card*(2*m) := by
    rw [← Nat.mul_add]; congr 1; dsimp [d]; omega
  rw [← split] at dense
  omega

end Wall133
