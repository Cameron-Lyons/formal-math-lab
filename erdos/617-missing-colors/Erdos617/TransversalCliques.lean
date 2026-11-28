module

public import Erdos617.GlobalCliqueEnergy
public import Erdos617.CliqueBouquet

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} {c : Sym2 V → Fin (q+1)}
    {x : V} {T : Finset (Fin (q+1))} {P : Fin (q+1) → Finset V}

omit [Fintype V] in
private theorem petal_degree (U : Finset V) (y : U) (j : Fin (q+1)) :
    (colorGraph (fun e : Sym2 U => c (Sym2.map Subtype.val e)) j).degree y =
      (U.filter ((colorGraph c j).Adj y.val)).card := by
  let G := colorGraph (fun e : Sym2 U => c (Sym2.map Subtype.val e)) j
  have eq : (G.neighborFinset y).map (Function.Embedding.subtype (·∈U)) =
      U.filter ((colorGraph c j).Adj y.val) := by
    ext v
    constructor
    · intro hv
      obtain ⟨z,hz,rfl⟩ := mem_map.mp hv
      have a := (G.mem_neighborFinset _ _).mp hz
      exact mem_filter.mpr ⟨z.prop, fun he => a.1 (Subtype.ext he),a.2⟩
    · intro hv
      obtain ⟨hU,ha⟩ := mem_filter.mp hv
      refine mem_map.mpr ⟨⟨v,hU⟩, (G.mem_neighborFinset _ _).mpr ⟨?_,ha.2⟩,rfl⟩
      exact fun he => ha.1 (congrArg Subtype.val he)
  simpa only [card_map,card_neighborFinset_eq_degree] using congrArg Finset.card eq

/-- The vertices of p monochromatic r-cliques through x, with x removed,
form p disjoint rows. In each additional color a clique meets each row at
most once. The sum of the shortfalls from p, over all additional colors and
all row vertices, is at most (p−1) times the total number of row vertices. -/
theorem transversal_clique_deficit (hq : 1≤q) (hp : 2≤T.card) (hb : Balanced c)
    (rows : ∀ j ∈ T, x∉P j ∧ (colorGraph c j).IsNClique (q+1) (insert x (P j)))
    (dis : (T : Set (Fin (q+1))).PairwiseDisjoint P) :
    let U := T.biUnion P
    let d := fun e : Sym2 U => c (Sym2.map Subtype.val e)
    (∀ j ∉ T, ∀ y : U, pointClique (colorGraph d j) y ≤ T.card) ∧
    (∑ j∈Tᶜ, ∑ y : U,(T.card-pointClique (colorGraph d j) y)) ≤ (T.card-1)*U.card := by
  classical
  intro U d
  let p := T.card
  let G := colorGraph d
  let n := Fintype.card U
  have rsz (j : Fin (q+1)) (hj : j∈T) : (P j).card=q := by
    have h := (rows j hj).2.card_eq
    rwa [card_insert_of_notMem (rows j hj).1,Nat.add_right_cancel_iff] at h
  have nc : n=U.card := Fintype.card_coe _
  have size : n=p*q := by
    rw [nc,show U.card=∑ j∈T,(P j).card from card_biUnion dis,sum_congr rfl rsz]
    simp [p]
  have sub (i : Fin (q+1)) (hi : i∈T) : P i ⊆ U := subset_biUnion_of_mem _ hi
  have away : x∉U := by
    rintro hx
    obtain ⟨i,hi,hm⟩ := mem_biUnion.mp hx
    exact (rows i hi).1 hm
  have rowCol (i : Fin (q+1)) (hi : i∈T) (z : V) (hz : z∈P i) :
      c s(z,x)=i := ((rows i hi).2.isClique (mem_insert_of_mem hz) (mem_insert_self ..)
        (fun he => (rows i hi).1 (he ▸ hz))).2
  have free (j : Fin (q+1)) : (colorGraph c j).IndepSetFree (q+1+1) := by
    intro I hi
    obtain ⟨a,ha,b,hb',ne,he⟩ := hb I hi.card_eq j
    exact hi.isIndepSet ha hb' ne ⟨ne,he⟩
  have rank (j : Fin (q+1)) (hj : j∉T) : (G j).indepNum≤q := by
    obtain ⟨I,hI⟩ := (G j).exists_isNIndepSet_indepNum
    obtain ⟨B,hBU,ind⟩ := lift_independent_subset c j U ⟨I,hI⟩
    have expanded := independent_insert_of_nonadjacent _ ind.isIndepSet x (by
      intro y hy hadj
      obtain ⟨i,hi,hyi⟩ := mem_biUnion.mp (hBU hy)
      have eq := hadj.symm.2.symm.trans (rowCol i hi y hyi)
      exact hj (eq ▸ hi))
    have bound := expanded.card_le_indepNum.trans (balanced_indepNum_le c hb j)
    rw [card_insert_of_notMem (fun hx => away (hBU hx)),ind.card_eq] at bound
    omega
  have cap (j : Fin (q+1)) (hj : j∉T) (y : U) : pointClique (G j) y≤p := by
    obtain ⟨C,_,cl⟩ := exists_pointClique (G j) y
    let row (z : U) : Fin (q+1) := (mem_biUnion.mp z.prop).choose
    have spec (z : U) : row z ∈ T ∧ z.val∈P (row z) := (mem_biUnion.mp z.prop).choose_spec
    have inj : Set.InjOn row (C : Set U) := by
      intro a ha b hb' he
      by_contra hne
      have hh := (rows (row a) (spec a).1).2.isClique (mem_insert_of_mem (spec a).2)
        (mem_insert_of_mem (he ▸ (spec b).2)) (fun e => hne (Subtype.ext e))
      exact hj (((cl.isClique ha hb' hne).2.symm.trans hh.2) ▸ (spec a).1)
    have incl : C.image row ⊆ T := by
      intro z hz
      obtain ⟨v,_,rfl⟩ := mem_image.mp hz
      exact (spec v).1
    rw [←cl.card_eq,←card_image_of_injOn inj]
    exact card_le_card incl
  refine ⟨cap,?_⟩
  have paid (y : U) : q-1+(p-1)*(p-2) ≤ ∑ j∈T,(G j).degree y := by
    obtain ⟨i,hi,hy⟩ := mem_biUnion.mp y.prop
    have own : q-1≤(G i).degree y := by
      rw [petal_degree (c:=c)]
      have incl : (P i).erase y.val ⊆ U.filter ((colorGraph c i).Adj y.val) := by
        intro z hz
        exact mem_filter.mpr ⟨sub i hi (mem_erase.mp hz).2,(rows i hi).2.isClique
          (mem_insert_of_mem hy) (mem_insert_of_mem (mem_erase.mp hz).2) (mem_erase.mp hz).1.symm⟩
      simpa [card_erase_of_mem hy,rsz i hi] using card_le_card incl
    have other (j : Fin (q+1)) (hj : j∈T.erase i) : p-2 ≤ (G j).degree y := by
      let B := T.erase j
      have hB : CliqueBouquet c j (q+1) x B P :=
        ⟨fun _ hm => (mem_erase.mp hm).1,fun a ha => rows a (mem_of_mem_erase ha),
         fun _ ha _ hb' ne => dis (mem_of_mem_erase ha) (mem_of_mem_erase hb') ne⟩
      have count := hB.neighbor_count (free j) (fun eq => away (eq ▸ y.prop))
        (fun he => (mem_erase.mp hj).1 (he.2.symm.trans (rowCol i hi y.val hy)))
      have incl : (B.biUnion P).filter ((colorGraph c j).Adj y.val) ⊆ U.filter ((colorGraph c j).Adj y.val) :=
        filter_subset_filter _ (biUnion_subset.mpr (fun a ha => sub a (mem_of_mem_erase ha)))
      have le := card_le_card incl
      have eq : B.card=p-1 := card_erase_of_mem (mem_of_mem_erase hj)
      rw [eq] at count
      rw [petal_degree (c:=c)]
      split at count <;> omega
    have lower := sum_le_sum other
    rw [sum_const,nsmul_eq_mul,card_erase_of_mem hi] at lower
    rw [←sum_erase_add T _ hi]
    change (p-1)*(p-2) ≤ _ at lower
    omega
  have fcount : Tᶜ.card+p=q+1 := by
    have le := T.card_le_univ
    simp only [Fintype.card_fin] at le
    simp [p,card_compl,le]
  have edges := sum_palette_degrees d
  change (∑ j, ∑ y,(G j).degree y)=n*(n-1) at edges
  have parts := sum_add_sum_compl T (fun j => ∑ y,(G j).degree y)
  rw [edges] at parts
  have pa := sum_le_sum (s:=univ) fun y _ => paid y
  simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id] at pa
  rw [sum_comm] at pa
  let D (j : Fin (q+1)) := ∑ y : U,(p-pointClique (G j) y)
  have per (j : Fin (q+1)) (hj : j∈Tᶜ) :
      n*(p-1)+D j ≤ ∑ y,(G j).degree y := by
    have low := (card_square_le_local_clique_energy (G j) _ (card_le_pointClique _)).trans
      (Nat.mul_le_mul_right _ (rank j (mem_compl.mp hj)))
    change 2*n^2 ≤ q*((∑ y,(G j).degree y)+n+∑ y,pointClique (G j) y) at low
    have ws := sum_congr (s₁:=univ) rfl fun y _ => Nat.sub_add_cancel (cap j (mem_compl.mp hj) y)
    rw [sum_add_distrib,sum_const,nsmul_eq_mul] at ws
    change D j+(∑ y,pointClique (G j) y)=n*p at ws
    have cancel : 2*n*p ≤ (∑ y,(G j).degree y)+n+∑ y,pointClique (G j) y := by
      apply Nat.le_of_mul_le_mul_right (c:=q) _ hq
      nlinarith only [low,congrArg (2*n*·) size]
    have ph : p-1+1=p := by dsimp [p]; omega
    nlinarith only [ws,cancel,congrArg (n*·) ph]
  have budget := sum_le_sum per
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id] at budget
  change (∑ j∈Tᶜ,D j) ≤ (p-1)*U.card
  rw [←nc]
  have hp' : 2≤p := hp
  have pos : 0<n := size ▸ Nat.mul_pos (by omega) hq
  have predn : n-1+1=n := by omega
  have predq : q-1+1=q := by omega
  have predp : p-1+1=p := by omega
  have pp : p-2+1=p-1 := by omega
  have arithmetic : n-1=(q-1)+(p-1)*(p-2)+Tᶜ.card*(p-1)+(p-1) := by
    nlinarith only [size,predn,predq,predp,pp,fcount,
      congrArg (·*(p-1)) fcount,congrArg ((p-1)*·) pp,congrArg (·*q) predp,
      congrArg (·*(p-1)) predp]
  rw [arithmetic] at parts
  dsimp only [n] at parts budget ⊢
  nlinarith only [parts,pa,budget]

end Erdos617
