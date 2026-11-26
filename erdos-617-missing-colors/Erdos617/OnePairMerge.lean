module

public import Erdos617.PaletteMatching

@[expose] public section

namespace Erdos617

open Finset

variable {V : Type*} {r : ℕ}

private theorem merge_one_pair (hr : 2≤r) (d : Sym2 V → Fin r) {a b : Fin r} (_ab : a≠b)
    (pair : HitsPalette d (r-1) {a,b})
    (single : ∀ j, j≠a → j≠b → HitsPalette d (r-1) {j}) :
    ∃ f : Fin r → Fin (r-1), Balanced (f ∘ d) := by
  classical
  let J := univ.erase b
  let B (j : J) : Finset (Fin r) := if j.val=a then {a,b} else {j.val}
  apply balanced_merge_of_disjoint_groups (ι:=J) (by omega) (by simp [J]) d B
  · intro i j ij
    have ne : i.val≠j.val := fun e => ij (Subtype.ext e)
    have ib := (mem_erase.mp i.prop).1
    have jb := (mem_erase.mp j.prop).1
    by_cases ia : i.val=a <;> by_cases ja : j.val=a <;>
      simp_all [B,Finset.disjoint_left,Ne.symm jb]
  · intro i
    by_cases ia : i.val=a
    · simpa [B,ia] using pair
    · simpa [B,ia] using single i.val ia (mem_erase.mp i.prop).1

/-- A balanced merger from r colors to r−1 colors has exactly one two-color
fiber. Every other original color must already occur on every r-vertex set. -/
theorem one_pair_merge_iff (hr : 2≤r) (d : Sym2 V → Fin r)
    (nonempty : ∃ S : Finset V, S.card=r) :
    (∃ f : Fin r → Fin (r-1), Balanced (f ∘ d)) ↔
      ∃ a b : Fin r, a≠b ∧ HitsPalette d (r-1) {a,b} ∧
        ∀ j, j≠a → j≠b → HitsPalette d (r-1) {j} := by
  classical
  refine ⟨?_,fun ⟨_,_,ne,p,q⟩ => merge_one_pair hr d ne p q⟩
  rintro ⟨f,hf⟩
  let F (l : Fin (r-1)) := univ.filter fun j => f j=l
  have hit (l : Fin (r-1)) : HitsPalette d (r-1) (F l) := by
    intro S hs
    obtain ⟨x,hx,y,hy,ne,eq⟩ := hf S hs l
    exact ⟨x,hx,y,hy,ne,mem_filter.mpr ⟨mem_univ _,eq⟩⟩
  obtain ⟨T,ht⟩ := nonempty
  have pos (l : Fin (r-1)) : 1≤(F l).card := by
    obtain ⟨x,_,y,_,_,he⟩ := hit l T (by omega)
    exact card_pos.mpr ⟨_,he⟩
  have total : ∑ l,(F l).card=r := by
    simp [F,sum_card_fiberwise_eq_card_filter]
  obtain ⟨q,hq⟩ : ∃ q, 2≤(F q).card := by
    by_contra! small
    have hsum := sum_le_sum (s:=univ) (g:=fun _ : Fin (r-1) => 1) (fun l _ => Nat.le_of_lt_succ (small l))
    simp only [sum_const,nsmul_eq_mul,Nat.mul_one,Nat.cast_id,card_univ,Fintype.card_fin,total] at hsum
    omega
  let R := univ.erase q
  have lower := sum_le_sum (s:=R) (f:=fun _ => 1) fun j _ => pos j
  have nR : R.card=r-1-1 := by simp [R]
  simp only [sum_const,nsmul_eq_mul,Nat.mul_one,Nat.cast_id,nR] at lower
  have split := sum_erase_add univ (fun l => (F l).card) (mem_univ q)
  change (∑ l∈R,(F l).card)+(F q).card=∑ l,(F l).card at split
  rw [total] at split
  obtain ⟨a,b,ab,eq⟩ := card_eq_two.mp (show (F q).card=2 by omega)
  refine ⟨a,b,ab,eq ▸ hit q,?_⟩
  have ones : ∀ j∈R,1=(F j).card := by
    apply (sum_eq_sum_iff_of_le (fun j (_:j∈R) => pos j)).mp
    simp only [sum_const,nsmul_eq_mul,Nat.mul_one,Nat.cast_id,nR]
    omega
  intro j ja jb
  have mem : j∈F (f j) := mem_filter.mpr ⟨mem_univ _,rfl⟩
  have neq : f j≠q := by
    rintro eqf
    rw [eqf,eq] at mem
    simp [ja,jb] at mem
  obtain ⟨u,eu⟩ := card_eq_one.mp (ones _ (mem_erase.mpr ⟨neq,mem_univ _⟩)).symm
  rw [eu,mem_singleton] at mem
  exact (eu.trans (congrArg singleton mem.symm)) ▸ hit (f j)

open scoped Classical in
/-- Failure of a one-color descent has an explicit obstruction. Either at least
three original colors each miss some r-set, or precisely two colors do and
one r-set misses both simultaneously. -/
theorem one_pair_merge_or_obstruction (hr : 2≤r) (d : Sym2 V → Fin r)
    (nonempty : ∃ S : Finset V, S.card=r) :
    let bad := univ.filter fun j => ¬ HitsPalette d (r-1) {j}
    (∃ f : Fin r → Fin (r-1), Balanced (f ∘ d)) ↔
      bad.card≤2 ∧ ∀ a b : Fin r, a≠b → a∈bad → b∈bad → HitsPalette d (r-1) {a,b} := by
  classical
  intro bad
  rw [one_pair_merge_iff hr d nonempty]
  have mem (j : Fin r) : j∈bad ↔ ¬ HitsPalette d (r-1) {j} := by simp [bad]
  constructor
  · rintro ⟨a,b,ab,p,q⟩
    have sub : bad⊆{a,b} := by
      intro j hj
      by_contra no
      simp only [mem_insert,mem_singleton,not_or] at no
      exact (mem j).mp hj (q j no.1 no.2)
    refine ⟨(card_le_card sub).trans_eq (card_pair ab),?_⟩
    intro i j ij hi hj
    have ei := sub hi
    have ej := sub hj
    simp only [mem_insert,mem_singleton] at ei ej
    rcases ei with rfl|rfl <;> rcases ej with rfl|rfl <;> try contradiction
    · exact p
    · simpa [pair_comm] using p
  · rintro ⟨count,p⟩
    obtain ⟨A,sub,_,size⟩ := exists_subsuperset_card_eq (subset_univ bad) count
      (by simpa using hr : 2≤(univ : Finset (Fin r)).card)
    obtain ⟨a,b,ab,eq⟩ := card_eq_two.mp size
    subst A
    have enlarge {u : Fin r} (hu : u∈({a,b} : Finset (Fin r))) (h : HitsPalette d (r-1) {u}) :
        HitsPalette d (r-1) {a,b} := by
      intro S hs
      obtain ⟨x,hx,y,hy,ne,he⟩ := h S hs
      exact ⟨x,hx,y,hy,ne,(singleton_subset_iff.mpr hu) he⟩
    refine ⟨a,b,ab,?_,fun j ja jb => ?_⟩
    · by_cases ha : a∈bad
      · by_cases hb : b∈bad
        · exact p a b ab ha hb
        · exact enlarge (by simp) (not_not.mp (mt (mem b).mpr hb))
      · exact enlarge (mem_insert_self ..) (not_not.mp (mt (mem a).mpr ha))
    · by_contra fail
      have := sub ((mem j).mpr fail)
      simp [ja,jb] at this

open scoped Classical in
/-- A failed descent supplies three individually avoidable colors or a
single r-set avoiding the only two individually avoidable colors. -/
theorem witnesses_of_failed_one_pair_merge (hr : 2≤r) (d : Sym2 V → Fin r)
    (nonempty : ∃ S : Finset V, S.card=r) (failed : ¬∃ f : Fin r → Fin (r-1), Balanced (f ∘ d)) :
    let bad := univ.filter fun j => ¬ HitsPalette d (r-1) {j}
    3≤bad.card ∨ ∃ (a b : Fin r) (T : Finset V), a≠b ∧ bad={a,b} ∧
      T.card=r ∧ ∀ x∈T, ∀ y∈T,x≠y → d s(x,y)≠a ∧ d s(x,y)≠b := by
  classical
  intro bad
  by_cases many : 3≤bad.card
  · exact Or.inl many
  right
  have few : bad.card≤2 := by omega
  have no : ¬∀ a b : Fin r, a≠b → a∈bad → b∈bad → HitsPalette d (r-1) {a,b} :=
    fun all => failed ((one_pair_merge_or_obstruction hr d nonempty).mpr ⟨few,all⟩)
  push Not at no
  obtain ⟨a,b,ne,ha,hb,miss⟩ := no
  have eq : {a,b}=bad := eq_of_subset_of_card_le (insert_subset ha (singleton_subset_iff.mpr hb))
    (by rw [card_pair ne]; exact few)
  unfold HitsPalette at miss
  push Not at miss
  obtain ⟨T,size,missing⟩ := miss
  exact ⟨a,b,T,ne,eq.symm,by omega,fun x hx y hy xy => by simpa using missing x hx y hy xy⟩

end Erdos617
