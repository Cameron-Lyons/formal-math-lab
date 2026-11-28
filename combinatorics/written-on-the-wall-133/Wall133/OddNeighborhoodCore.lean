module

public import Wall133.Density

@[expose] public section

/-! # Successors in a core of odd average degree -/
namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
private theorem degreeOn_mono {A B : Finset V} (h : A ⊆ B) (x : V) :
    degreeOn G A x ≤ degreeOn G B x :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

omit [Fintype V] in
private theorem totalOn_union_bound (A B L : Finset V) {c : ℕ}
    (hAB : A ⊆ B) (hLB : L ⊆ B) (hL : ∀ y ∈ L, degreeOn G B y ≤ c) :
    totalOn G (A ∪ L) ≤ totalOn G A + 2*c*L.card := by
  classical
  induction L using Finset.induction_on with
  | empty => simp
  | @insert x L hx ih =>
    have hL' : L ⊆ B := (Finset.subset_insert _ _).trans hLB
    have old := ih hL' (fun y hy => hL y (Finset.mem_insert_of_mem hy))
    rw [Finset.union_insert,Finset.card_insert_of_notMem hx,Nat.mul_succ]
    by_cases h : x ∈ A∪L
    · rw [Finset.insert_eq_of_mem h]
      omega
    · rw [totalOn_insert G h]
      have deg := (degreeOn_mono G (Finset.union_subset hAB hL') x).trans (hL x (Finset.mem_insert_self _ _))
      omega

omit [Fintype V] in
private theorem two_high_of_density {S : Finset V} (hS : S.Nonempty) {d : ℕ} (hd : 2 ≤ d)
    (dense : (2*d-1)*S.card ≤ totalOn G S) (x : V) :
    ∃ y ∈ S, y ≠ x ∧ d < degreeOn G S y := by
  classical
  by_contra! no
  have cap (z : V) : degreeOn G S z ≤ S.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have sum : (∑ y ∈ S.erase x, degreeOn G S y) ≤ (S.erase x).card*d := by
    simpa using Finset.sum_le_sum (s := S.erase x) (g := fun _ => d)
      (fun y hy => no y (Finset.mem_erase.mp hy).2 (Finset.mem_erase.mp hy).1)
  have eq : totalOn G S ≤ (∑ y ∈ S.erase x, degreeOn G S y)+S.card := by
    by_cases h : x ∈ S
    · rw [totalOn,←Finset.sum_erase_add _ _ h]
      exact Nat.add_le_add_left (cap x) _
    · simp only [Finset.erase_eq_of_notMem h, totalOn]
      omega
  have card : (S.erase x).card ≤ S.card := Finset.card_le_card (Finset.erase_subset ..)
  have enough : (d+1)*S.card ≤ (2*d-1)*S.card :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm d S.card] at enough
  by_cases hx : x∈S
  · have smaller := Nat.mul_lt_mul_of_pos_right (Finset.card_erase_lt_of_mem hx) (by omega : 0<d)
    omega
  · have all := Finset.sum_le_sum (s := S) (g := fun _ => d)
      (fun y hy => no y hy (fun e => hx (e ▸ hy)))
    simp only [Finset.sum_const,nsmul_eq_mul] at all
    change totalOn G S ≤ S.card*d at all
    have := hS.card_pos
    omega

/-- An odd average threshold admits an induced core of minimum degree d.
A vertex of degree d+t has at most 2t neighbors of degree d. In particular
all neighbors of a vertex of minimum degree d have higher degree. -/
theorem exists_odd_neighborhood_core [Nonempty V] {d : ℕ} (hd : 2 ≤ d)
    (hav : (2*d-1)*Fintype.card V ≤ ∑ v,G.degree v) :
    ∃ S : Finset V, S.Nonempty ∧
      (2*d-1)*S.card ≤ ∑ u : S,(G.induce (S : Set V)).degree u ∧
      (∀ u : S, d ≤ (G.induce (S : Set V)).degree u) ∧
      ∀ x : S, ∀ L : Finset S,
        (∀ y ∈ L, (G.induce (S : Set V)).Adj x y ∧ (G.induce (S : Set V)).degree y = d) →
        L.card ≤ 2*((G.induce (S : Set V)).degree x-d) := by
  classical
  let k := 2*d-1
  let sets := Finset.univ.filter (fun S : Finset V => S.Nonempty ∧ k*S.card ≤ totalOn G S)
  have mem (S : Finset V) : S ∈ sets ↔ S.Nonempty ∧ k*S.card ≤ totalOn G S := by simp [sets]
  have base : Finset.univ ∈ sets := (mem _).2 ⟨Finset.univ_nonempty,by
    simpa only [Finset.card_univ,k,totalOn,degreeOn_univ] using hav⟩
  obtain ⟨S,hS,small⟩ := sets.exists_min_image Finset.card ⟨_,base⟩
  obtain ⟨hne,hs⟩ := (mem S).1 hS
  have fail (A : Finset V) (hA : A.Nonempty) (hc : A.card < S.card) : totalOn G A < k*A.card := by
    by_contra! h
    exact hc.not_ge (small A ((mem A).2 ⟨hA,h⟩))
  have htot : totalOn G S = ∑ u : S,(G.induce (S : Set V)).degree u := by
    rw [totalOn,←Finset.sum_attach]
    exact Finset.sum_congr rfl (fun u _ => degreeOn_induce G S u)
  have leave (x : V) (hx : x∈S) : totalOn G S=totalOn G (S.erase x)+2*degreeOn G S x := by
    have hh := totalOn_insert G (Finset.notMem_erase x S)
    rw [Finset.insert_erase hx] at hh
    have he : degreeOn G (S.erase x) x = degreeOn G S x := by
      unfold degreeOn
      congr 1
      ext y
      simp only [Finset.mem_filter, Finset.mem_erase]
      exact ⟨fun ⟨⟨_, hy⟩, hadj⟩ => ⟨hy, hadj⟩, fun ⟨hy, hadj⟩ => ⟨⟨hadj.ne.symm, hy⟩, hadj⟩⟩
    simpa [he] using hh
  have dmin (x : V) (hx : x∈S) : d ≤ degreeOn G S x := by
    obtain ⟨y,hy,hn,_⟩ := two_high_of_density G hne hd hs x
    have hh := fail (S.erase x) ⟨y,Finset.mem_erase.mpr ⟨hn,hy⟩⟩ (Finset.card_erase_lt_of_mem hx)
    have c : S.card=(S.erase x).card+1 := by rw [Finset.card_erase_of_mem hx]; have := hne.card_pos; omega
    have hs' := hs
    rw [c,Nat.mul_succ] at hs'
    have := leave x hx
    dsimp [k] at *
    omega
  refine ⟨S,hne,hs.trans_eq htot,fun x => (dmin _ x.property).trans_eq (degreeOn_induce G S x),?_⟩
  intro x L near
  let M := L.map (Function.Embedding.subtype (·∈S))
  have spec (z : V) (hz : z ∈ M) : z ∈ S ∧ G.Adj x.val z ∧ degreeOn G S z=d := by
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hz
    exact ⟨y.property,(near _ hy).1,(degreeOn_induce G S y).trans (near _ hy).2⟩
  let B := S.erase x.val
  let A := B \ M
  have hMB : M ⊆ B := fun z hz => Finset.mem_erase.mpr ⟨(spec z hz).2.1.ne.symm,(spec z hz).1⟩
  have hA : A.Nonempty := by
    obtain ⟨y,hy,hn,hhigh⟩ := two_high_of_density G hne hd hs x.val
    exact ⟨y,Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hn,hy⟩,
      fun h => hhigh.ne ((spec _ h).2.2).symm⟩⟩
  have cnt : A.card+M.card=B.card := Finset.card_sdiff_add_card_eq_card hMB
  have cnt' : S.card=B.card+1 := by
    simp only [B,Finset.card_erase_of_mem x.property]
    have := hne.card_pos
    omega
  have smallA := fail A hA (by omega)
  have hdeg (y : V) (hy : y∈M) : degreeOn G B y ≤ d-1 := by
    have one : degreeOn G S y=degreeOn G B y+1 := by
      calc
        _ = degreeOn G (insert x.val B) y := by rw [Finset.insert_erase x.property]
        _ = _ := by
          have hxy := (spec y hy).2.1.symm
          have hxB : x.val ∉ B := Finset.notMem_erase _ _
          simp only [degreeOn,Finset.filter_insert,ite_eq_left hxy,Finset.card_insert_of_notMem
            (show x.val ∉ B.filter (G.Adj y) from fun h => hxB (Finset.mem_filter.mp h).1)]
    have := (spec y hy).2.2
    omega
  have removed := totalOn_union_bound G A B M (Finset.sdiff_subset) hMB hdeg
  have AB : A∪M=B := Finset.sdiff_union_of_subset hMB
  rw [AB] at removed
  have hc : S.card=A.card+M.card+1 := by omega
  rw [hc,Nat.mul_succ,Nat.mul_add] at hs
  have le := leave x.val x.property
  change totalOn G S=totalOn G B+2*degreeOn G S x.val at le
  have e : k * M.card=2*(d-1)*M.card+M.card := by
    rw [show k=2*(d-1)+1 by dsimp [k]; omega,Nat.add_mul,Nat.one_mul]
  rw [e] at hs
  have ms : M.card=L.card := Finset.card_map _
  rw [← degreeOn_induce G S x]
  dsimp [k] at hs smallA
  omega

end Wall133
