import Erdos617.OneStepDescent
import Erdos617.VerifiedRange

namespace Erdos617

open Finset
open scoped Classical

private theorem balanced_contradiction {V : Type*} {r : ℕ} {c : Sym2 V → Fin r}
    (hb : Balanced c) (witness : ∃ (S : Finset V) (k : Fin r), S.card=r+1 ∧
      ∀ u∈S, ∀ v∈S, u≠v → c s(u,v)≠k) : False := by
  obtain ⟨S,k,sz,avoid⟩ := witness
  obtain ⟨x,hx,y,hy,ne,he⟩ := hb S sz k
  exact avoid x hx y hy ne he

/-- If the unrestricted conjecture fails, there is a first bad palette size s.
Every square of side s−1 in that coloring has one of the two explicit failures
of palette descent. In some such square, two prescribed colors occur on every
s-set. -/
theorem least_counterexample_descent {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (hr : 3≤r) (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c) :
    ∃ s, 11≤s ∧ s≤r ∧ ∃ d : Sym2 (Fin (s^2+1)) → Fin s, Balanced d ∧
      (∃ (U : Finset (Fin (s^2+1))) (i j : Fin s), i≠j ∧ U.card=(s-1)^2+1 ∧
        let f := fun e : Sym2 U => d (e.map Subtype.val)
        HitsPalette f (s-1) {i} ∧ HitsPalette f (s-1) {j}) ∧
      ∀ U : Finset (Fin (s^2+1)), U.card=(s-1)^2+1 →
        let f := fun e : Sym2 U => d (e.map Subtype.val)
        let bad := univ.filter fun j => ¬HitsPalette f (s-1) {j}
        (∀ g : Sym2 U → Fin (s-1), ¬Balanced g) ∧
        (3≤bad.card ∨ ∃ (a b : Fin s) (T : Finset U), a≠b ∧ bad={a,b} ∧ T.card=s ∧
          ∀ x∈T, ∀ y∈T, x≠y → f s(x,y)≠a ∧ f s(x,y)≠b) := by
  classical
  let P (n : ℕ) := 3≤n ∧ ∃ d : Sym2 (Fin (n^2+1)) → Fin n, Balanced d
  have atR : P r := ⟨hr,_,balanced_pullback c hb (Fintype.equivFinOfCardEq hn).symm.toEmbedding⟩
  have ex : ∃ n,P n := ⟨r,atR⟩
  let s := Nat.find ex
  obtain ⟨h3,d,hd⟩ := Nat.find_spec ex
  change 3≤s at h3
  have n : Fintype.card (Fin (s^2+1))=s^2+1 := Fintype.card_fin _
  have h11 : 11≤s := by
    by_contra! le
    exact balanced_contradiction hd (missing_of_at_most_ten_colors h3 (by omega) n d)
  refine ⟨s,h11,Nat.find_min' ex atR,d,hd,?_,?_⟩
  · obtain ⟨i,j,U,diff,sz,li,lj⟩ :=
      exists_square_of_at_most_two_rows (by decide : 1≤2) (by omega : 5≤s) n hd
    exact ⟨U,i,j,diff,sz,single_hit_of_rank d i li,single_hit_of_rank d j lj⟩
  · intro U sz f bad
    have u : Fintype.card U=(s-1)^2+1 := (Fintype.card_coe U).trans sz
    have none (g : Sym2 U → Fin (s-1)) (ok : Balanced g) : False := by
      have lower : P (s-1) := ⟨by omega,_,balanced_pullback _ ok (Fintype.equivFinOfCardEq u).symm.toEmbedding⟩
      exact Nat.find_min ex (show s-1<s by omega) lower
    refine ⟨none,?_⟩
    have fail : ¬∃ g : Fin s → Fin (s-1), Balanced (g ∘ f) := fun ⟨g,yes⟩ => none (g ∘ f) yes
    have room : s≤(univ : Finset U).card := by
      rw [card_univ,u]
      have factor := Nat.mul_le_mul_left (s-1) (show 1≤s-1 by omega)
      simpa [pow_two] using (show s≤(s-1)*(s-1)+1 by omega)
    obtain ⟨T,_,hT⟩ := exists_subset_card_eq room
    exact witnesses_of_failed_one_pair_merge (by omega) f ⟨T,hT⟩ fail

end Erdos617
