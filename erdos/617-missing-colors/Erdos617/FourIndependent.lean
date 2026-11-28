module

public import Erdos617.ThreeIndependent
public import Erdos617.TwoBlockBoundary
public import Erdos617.IndependentSets

@[expose] public section

/-!
This is the three-block threshold in the colored density argument for balanced
colorings. See §2 of Robert Sneiderman's
[seven- and eight-color manuscript](https://github.com/Robby955/erdos-617-fixed-cases/blob/main/r7-r8/main.tex).
-/

namespace Erdos617

open SimpleGraph

/-- Any four-clique of the complement is an independent four-set in the chosen color. -/
private theorem triangle_free_on_nonneighbors {V : Type*} [DecidableEq V] {r : ℕ}
    (c : Sym2 V → Fin r) (k : Fin r) (x : V) (B : Finset V)
    (hB : ∀ v ∈ B, (colorGraph c k)ᶜ.Adj x v)
    (hfour : (colorGraph c k).IndepSetFree 4) :
    (colorGraph (fun e : Sym2 B => c (Sym2.map Subtype.val e)) k)ᶜ.CliqueFree 3 := by
  classical
  let incl := Function.Embedding.subtype (· ∈ B)
  let G := colorGraph c k
  intro T hT
  have tri : Gᶜ.IsNClique 3 (T.map incl) := by
    refine ⟨?_, (Finset.card_map _).trans hT.card_eq⟩
    intro a ha b hb hab
    obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp hb
    have he := hT.isClique ha' hb' (fun h => hab (congrArg incl h))
    exact ⟨hab, fun e => he.2 ⟨he.ne, e.2⟩⟩
  have cone := tri.insert (a := x) (fun y hy => by
    obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp hy
    exact hB v v.property)
  exact hfour _ (G.isNClique_compl.mp cone)

/-- For r ≥ 6, balance forces an independent four-set in *each* color on
3r+1 vertices. No hypothesis is imposed on the degrees of the color graphs. -/
theorem independent_four_of_balanced {r : ℕ} (hr : 6 ≤ r)
    {V : Type*} [Fintype V] [DecidableEq V] (hV : Fintype.card V = 3*r+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r) :
    ∃ I, (colorGraph c k).IsNIndepSet 4 I := by
  classical
  let G := colorGraph c k
  by_contra! hfour
  -- A complement vertex of degree at least 2r supplies the tight 2r-vertex case.
  have lower (j : Fin r) (_hj : j ≠ k) : 3*r+3 ≤ (colorGraph c j).edgeFinset.card := by
    have h := color_edge_count_of_balanced (t := 3) (by omega) hV c hb j
    simpa [show Nat.choose 3 2 = 3 by decide, Nat.mul_comm] using h
  have count : (3*r+1)*(2*r-1) < 2*((r-1)*(3*r+3)) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hr
    rw [show 2*(6+m)-1 = 11+2*m by omega, show 6+m-1 = 5+m by omega]
    nlinarith
  obtain ⟨x, hx⟩ := exists_compl_degree_ge c k hV lower count
  have many : 2*r ≤ (Gᶜ.neighborFinset x).card := by
    rw [card_neighborFinset_eq_degree]
    change 2*r-1 < Gᶜ.degree x at hx
    omega
  obtain ⟨B, hBN, hB⟩ := Finset.exists_subset_card_eq many
  let incl := Function.Embedding.subtype (· ∈ B)
  let cB (e : Sym2 B) := c (Sym2.map incl e)
  have htri := triangle_free_on_nonneighbors c k x B
    (fun _ h => (Gᶜ.mem_neighborFinset _ _).mp (hBN h)) hfour
  obtain ⟨Q, hQ⟩ := clique_on_two_blocks_of_triangle_free r hr
    ((Fintype.card_coe B).trans hB) cB (balanced_pullback c hb incl) k htri
  let C := Q.map incl
  have hC : G.IsNClique r C := by
    refine ⟨?_, (Finset.card_map _).trans hQ.card_eq⟩
    intro a ha b hb hab
    obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp hb
    have he := hQ.isClique ha' hb' (fun h => hab (congrArg incl h))
    exact ⟨hab, he.2⟩
  -- Off this r-clique there are 2r+1 vertices, giving an independent triple.
  have rest : Cᶜ.card = 2*r+1 := by rw [Finset.card_compl, hV, hC.card_eq]; omega
  obtain ⟨J, hJC, hJ⟩ := independent_three_in_subset (by omega) c hb k Cᶜ rest
  have hdisj : Disjoint C J :=
    Finset.disjoint_left.mpr fun _ hv hJv => (Finset.mem_compl.mp (hJC hJv)) hv
  obtain ⟨S, hS⟩ := extend_across_clique G C J hC hJ hdisj (by omega)
    (fun y hy _ hu _ hv => exterior_clique_neighbor_unique c hb k C hC y hy hu hv)
  exact hfour S hS

/-- Balance forces an independent four-set in each specified set of 3r+1 vertices
for every prescribed color, whenever r ≥ 6. -/
theorem independent_four_in_subset {V : Type*} {r : ℕ} (hr : 6 ≤ r)
    (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r) (S : Finset V) (hS : S.card = 3*r+1) :
    ∃ I ⊆ S, (colorGraph c k).IsNIndepSet 4 I := by
  classical
  apply lift_independent_subset c k S
  exact independent_four_of_balanced hr ((Fintype.card_coe S).trans hS)
    _ (balanced_pullback c hb (Function.Embedding.subtype (· ∈ S))) k

end Erdos617
