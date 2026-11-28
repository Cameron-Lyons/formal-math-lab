module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Pi

@[expose] public section

namespace Erdos617

open Finset Function SimpleGraph

/-- A family of assignments fixing two different coordinates occupies at most
one out of every `m²` assignments. Varying those two coordinates is injective. -/
private theorem two_fixed_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (B : Finset (ι → Fin m)) {i j : ι} (hij : i ≠ j) {a b : Fin m}
    (hfix : ∀ σ ∈ B, σ i = a ∧ σ j = b) :
    B.card * m^2 ≤ Fintype.card (ι → Fin m) := by
  classical
  let code (w : B × Fin m × Fin m) :=
    Function.update (Function.update w.1.val i w.2.1) j w.2.2
  have hinj : Function.Injective code := by
    rintro ⟨σ, u, v⟩ ⟨τ, u', v'⟩ heq
    have hu : u = u' := by simpa [code, Function.update_of_ne hij] using congrFun heq i
    have hv : v = v' := by simpa [code] using congrFun heq j
    have hστ : σ = τ := by
      apply Subtype.ext
      funext k
      by_cases hki : k = i
      · subst k
        exact (hfix σ.val σ.prop).1.trans (hfix τ.val τ.prop).1.symm
      by_cases hkj : k = j
      · subst k
        exact (hfix σ.val σ.prop).2.trans (hfix τ.val τ.prop).2.symm
      simpa [code, Function.update_of_ne hki, Function.update_of_ne hkj] using congrFun heq k
    simp [hστ, hu, hv]
  simpa [pow_two] using Fintype.card_le_of_injective code hinj

/-- If every block has at least `m` vertices and all graph edges between
different blocks belong to a set of fewer than `m²` edges, then the
blocks admit an independent transversal. -/
theorem sparse_independent_transversal {V ι : Type*} [DecidableEq V] [Fintype ι]
    (G : SimpleGraph V) (X : ι → Finset V)
    (hd : Pairwise (fun i j => Disjoint (X i) (X j))) (F : Finset (Sym2 V))
    {m : ℕ} (hm : 0 < m) (hsize : ∀ i, m ≤ (X i).card)
    (hcover : ∀ i j, i ≠ j → ∀ x ∈ X i, ∀ y ∈ X j, G.Adj x y → s(x,y) ∈ F)
    (hsmall : F.card < m^2) :
    ∃ f : ι → V, (∀ i, f i ∈ X i) ∧ ∀ i j, i ≠ j → ¬G.Adj (f i) (f j) := by
  classical
  have hex (i : ι) : ∃ g : Fin m ↪ V, Set.range g ⊆ X i :=
    Function.Embedding.exists_of_card_le_finset (by simpa using hsize i)
  choose g hg using hex
  have hmem (i : ι) (a : Fin m) : g i a ∈ X i := hg i ⟨a, rfl⟩
  have hcoord {i j : ι} {a b : Fin m} (he : g i a = g j b) : i = j ∧ a = b := by
    have h : i = j := by
      by_contra hn
      exact Finset.disjoint_left.mp (hd hn) (hmem i a) (he ▸ hmem j b)
    subst j
    exact ⟨rfl, (g i).injective he⟩
  let bad (e : Sym2 V) := (univ : Finset (ι → Fin m)).filter fun σ =>
    ∃ i j, i ≠ j ∧ s(g i (σ i), g j (σ j)) = e
  have hcount (e : Sym2 V) : (bad e).card * m^2 ≤ Fintype.card (ι → Fin m) := by
    by_cases hb : (bad e).Nonempty
    · obtain ⟨σ, hσ⟩ := hb
      obtain ⟨i, j, hij, he⟩ := (mem_filter.mp hσ).2
      have fixed {k : ι} {a : Fin m} (ha : g k a ∈ e) (τ : ι → Fin m) (hτ : τ ∈ bad e) :
          τ k = a := by
        obtain ⟨p, q, _, hpq⟩ := (mem_filter.mp hτ).2
        rw [← hpq] at ha
        rcases Sym2.mem_iff'.mp ha with h | h
        · obtain ⟨rfl, hval⟩ := hcoord h
          exact hval.symm
        · obtain ⟨rfl, hval⟩ := hcoord h
          exact hval.symm
      apply two_fixed_coordinates (bad e) hij (a := σ i) (b := σ j)
      exact fun τ hτ => ⟨fixed (he ▸ by simp) τ hτ, fixed (he ▸ by simp) τ hτ⟩
    · simp [not_nonempty_iff_eq_empty.mp hb]
  by_contra hn
  have hcov : (univ : Finset (ι → Fin m)) ⊆ F.biUnion bad := by
    intro σ _
    by_contra havoid
    apply hn
    refine ⟨fun i => g i (σ i), fun i => hmem i _, ?_⟩
    intro i j hij hadj
    exact havoid (mem_biUnion.mpr ⟨_, hcover i j hij _ (hmem i _) _ (hmem j _) hadj,
      mem_filter.mpr ⟨mem_univ σ, i, j, hij, rfl⟩⟩)
  have htot : Fintype.card (ι → Fin m) ≤ ∑ e ∈ F, (bad e).card := by
    simpa using (card_le_card hcov).trans card_biUnion_le
  have hlim := sum_le_sum (s := F) fun e _ => hcount e
  rw [← sum_mul, sum_const, nsmul_eq_mul] at hlim
  have hpos : 0 < Fintype.card (ι → Fin m) := Fintype.card_pos_iff.mpr ⟨fun _ => ⟨0, hm⟩⟩
  have hlt := Nat.mul_lt_mul_of_pos_right hsmall hpos
  rw [Nat.mul_comm (m^2)] at hlt
  exact (not_lt_of_ge ((Nat.mul_le_mul_right (m^2) htot).trans hlim)) hlt

end Erdos617
