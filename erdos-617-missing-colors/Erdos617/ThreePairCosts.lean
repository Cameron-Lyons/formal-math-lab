import Erdos617.SevenPairs

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] {r : ℕ} {c : Sym2 V → Fin r} {k : Fin r}

private theorem two_pair_weight (hr : 6≤r) (hb : Balanced c) {B : Finset V}
    (size : B.card=r+1) (no : ∀ T⊆B, ¬(colorGraph c k).IsNClique r T)
    (w : V → ℕ) (L : ℕ)
    (cover : ∀ a∈B, ∀ b∈B, a≠b → ¬(colorGraph c k).Adj a b → L≤w a+w b) :
    ∃ A⊆B, A.card=4 ∧ 2*L≤∑ z∈A,w z := by
  obtain ⟨a,ha,b,hb',u,hu,v,hv,ab,uv,d,nn,nn'⟩ := two_missing_pairs_of_six_le hr hb size no
  refine ⟨{a,b}∪{u,v},union_subset (insert_subset ha (singleton_subset_iff.mpr hb'))
    (insert_subset hu (singleton_subset_iff.mpr hv)),by rw [card_union_of_disjoint d,card_pair ab,card_pair uv],?_⟩
  rw [sum_union d,sum_pair ab,sum_pair uv]
  have := cover a ha b hb' ab nn
  have := cover u hu v hv uv nn'
  omega

/-- The endpoint cost forced by one, two or three disjoint missing edges
in sets of sizes r, r+1 and r+2 respectively. -/
theorem missing_edge_endpoint_cost (hr : 10≤r) (hb : Balanced c) {B : Finset V}
    (no : ∀ T⊆B, ¬(colorGraph c k).IsNClique r T) (w : V → ℕ) {L cost : ℕ}
    (cover : ∀ a∈B, ∀ b∈B, a≠b → ¬(colorGraph c k).Adj a b → L≤w a+w b)
    (bound : ∀ A⊆B,(∑ a∈A,w a)≤cost+A.card.choose 2) :
    (B.card=r → L≤cost+1) ∧ (B.card=r+1 → 2*L≤cost+6) ∧ (B.card=r+2 → 3*L≤cost+15) := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro sz
    obtain ⟨a,ha,b,hb',hne,nn⟩ : ∃ a∈B, ∃ b∈B, a≠b ∧ ¬(colorGraph c k).Adj a b := by
      by_contra! every
      exact no B Subset.rfl ⟨every,sz⟩
    have lim := bound {a,b} (insert_subset ha (singleton_subset_iff.mpr hb'))
    rw [card_pair hne,sum_pair hne] at lim
    exact (cover a ha b hb' hne nn).trans lim
  · intro sz
    obtain ⟨A,sub,n,large⟩ := two_pair_weight (by omega) hb sz no w L cover
    exact large.trans (by simpa [n,Nat.choose] using bound A sub)
  · intro sz
    by_contra! low
    have four (z : V) (hz : z∈B) : ∃ A⊆B.erase z, A.card=4 ∧ 2*L≤∑ u∈A,w u :=
      two_pair_weight (by omega) hb (by rw [card_erase_of_mem hz,sz]; omega)
        (fun C sub => no C (sub.trans (erase_subset ..))) w L
        (fun a ha b hb' => cover a (mem_of_mem_erase ha) b (mem_of_mem_erase hb'))
    let N (x : V) := B.filter (fun u => x≠u ∧ ¬(colorGraph c k).Adj x u)
    have hit {A : Finset V} (sub : A⊆B) (n : A.card=4) (lar : 2*L≤∑ u∈A,w u)
        {u v : V} (hu : u∈B) (hv : v∈B) (uv : u≠v) (nn : ¬(colorGraph c k).Adj u v) : u∈A ∨ v∈A := by
      by_contra! far
      have dis : Disjoint A ({u,v}:Finset V) := by
        apply Finset.disjoint_left.mpr
        intro z hz hz'
        rcases mem_insert.mp hz' with eq | eq
        · exact far.1 (eq ▸ hz)
        · exact far.2 (mem_singleton.mp eq ▸ hz)
      have cap := bound (A∪{u,v}) (union_subset sub (insert_subset hu (singleton_subset_iff.mpr hv)))
      rw [card_union_of_disjoint dis,n,card_pair uv,sum_union dis,sum_pair uv] at cap
      have p := cover u hu v hv uv nn
      norm_num [Nat.choose] at cap
      omega
    have small (z : V) (hz : z∈B) : (N z).card≤4 := by
      obtain ⟨A,sub,n,lar⟩ := four z hz
      refine (card_le_card (t:=A) ?_).trans n.le
      intro w hw
      obtain ⟨hw,d,nn⟩ := mem_filter.mp hw
      exact (hit (sub.trans (erase_subset ..)) n lar hz hw d nn).resolve_left (fun h => notMem_erase z B (sub h))
    obtain ⟨z,hz⟩ := card_pos.mp (by omega : 0<B.card)
    obtain ⟨A,sub,n,lar⟩ := four z hz
    let R (u : V) := (N u).image (fun v => (u,v))
    have cap := foreign_pair_budget c hb k B (A.biUnion R) (by
      intro a ha b hb' ab col
      have nn : ¬(colorGraph c k).Adj a b := fun e => col e.2
      rcases hit (sub.trans (erase_subset ..)) n lar ha hb' ab nn with aA|bA
      · exact Or.inl (mem_biUnion.mpr ⟨a,aA,mem_image_of_mem _ (mem_filter.mpr ⟨hb',ab,nn⟩)⟩)
      · exact Or.inr (mem_biUnion.mpr ⟨b,bA,mem_image_of_mem _ (mem_filter.mpr ⟨ha,ab.symm,fun e => nn e.symm⟩)⟩))
    have upper := (card_biUnion_le : (A.biUnion R).card≤∑ a∈A,(R a).card).trans
      (sum_le_sum (s:=A) (g:=fun _ => 4) (fun a ha => card_image_le.trans (small a (mem_of_mem_erase (sub ha)))))
    rw [sz,Nat.mul_add] at cap
    simp [n] at upper
    omega

end Erdos617
