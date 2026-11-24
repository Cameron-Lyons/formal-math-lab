import Erdos617.Affine
import Erdos617.BipartiteColor

namespace Erdos617

open Finset

/-- When directions correspond to partitions into lines, merging them in a
balanced coloring above the square threshold needs at least three directions
per resulting color. -/
theorem at_least_three_directions_per_color {V D L : Type*}
    [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D] [Fintype L] {s : ℕ}
    (hs : 2≤s) (big : s^2<Fintype.card V) (dir : Sym2 V → D) (line : D → V → L)
    (label : ∀ j x y,x≠y → (dir s(x,y)=j ↔ line j x=line j y)) (f : D → Fin s)
    (hb : Balanced (f ∘ dir)) (k : Fin s) :
    3 ≤ (univ.filter fun j => f j=k).card := by
  classical
  let K := univ.filter fun j => f j=k
  have size : s+1≤(univ : Finset V).card := by
    rw [card_univ]
    have := Nat.mul_le_mul_left s (show 1≤s by omega)
    simp only [Nat.mul_one,←pow_two] at this
    omega
  obtain ⟨T,_,sz⟩ := exists_subset_card_eq size
  obtain ⟨x,_,y,_,_,e⟩ := hb T sz k
  have pos : 0<K.card := card_pos.mpr ⟨_,mem_filter.mpr ⟨mem_univ (dir s(x,y)),e⟩⟩
  by_contra! small
  change K.card<3 at small
  obtain ⟨a,b,eq⟩ : ∃ a b,K={a,b} := by
    rcases show K.card=1 ∨ K.card=2 by omega with one|two
    · obtain ⟨a,eq⟩ := card_eq_one.mp one
      exact ⟨a,a,by simpa using eq⟩
    · obtain ⟨a,b,_,eq⟩ := card_eq_two.mp two
      exact ⟨a,b,eq⟩
  apply big.not_ge
  apply balanced_two_partitions_bound hs (f ∘ dir) hb k (line a) (line b)
  intro u v ne
  change f (dir s(u,v))=k ↔ _
  have member : dir s(u,v)∈K ↔ f (dir s(u,v))=k := by simp [K]
  rw [←member,eq,mem_insert,mem_singleton,label a u v ne,label b u v ne]

section AffineField

variable {F : Type} [Field F] [DecidableEq F]

/-- The distinct affine directions, including vertical. -/
private def affineDirection : Sym2 (F×F) → Option F :=
  Sym2.lift ⟨fun u v => if u.1=v.1 then none else some ((u.2-v.2)/(u.1-v.1)), by
    intro u v
    by_cases h : u.1=v.1
    · simp [h]
    · simp only [h,Ne.symm h,ite_false]
      rw [←neg_sub v.2 u.2,←neg_sub v.1 u.1,neg_div_neg_eq]⟩

private def affineIntercept (j : Option F) (v : F×F) : F :=
  match j with
  | none => v.1
  | some a => v.2-a*v.1

private theorem affine_line_label (j : Option F) (u v : F×F) (ne : u≠v) :
    affineDirection s(u,v)=j ↔ affineIntercept j u=affineIntercept j v := by
  cases j with
  | none =>
    change (if u.1=v.1 then none else some ((u.2-v.2)/(u.1-v.1)))=none ↔ u.1=v.1
    by_cases h : u.1=v.1 <;> simp [h]
  | some a =>
    change (if u.1=v.1 then none else some ((u.2-v.2)/(u.1-v.1)))=some a ↔ u.2-a*u.1=v.2-a*v.1
    by_cases h : u.1=v.1
    · simp [h,show u.2≠v.2 from fun e => ne (Prod.ext h e)]
    · simp only [h,ite_false,Option.some.injEq,div_eq_iff (sub_ne_zero.mpr h)]
      constructor <;> intro e <;> linear_combination e

private theorem ordinary_slope_of_direction (e : Sym2 (F×F)) :
    (affineDirection e).getD 0=slopeColor e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    by_cases h : u.1=v.1 <;> simp [affineDirection,slopeColor,h]

/-- For the balanced affine coloring on q² vertices, every restriction to
more than s² vertices and every palette relabeling to s≥2 colors can be
balanced only if 3s≤q+1. This applies to arbitrary choices of the vertices. -/
theorem affine_palette_merger_bound [Fintype F] {s : ℕ} (hs : 2≤s) (U : Finset (F×F))
    (big : s^2<U.card) (f : F → Fin s)
    (hb : Balanced (fun e : Sym2 U => f (slopeColor (e.map Subtype.val)))) :
    3*s ≤ Fintype.card F+1 := by
  classical
  let d (e : Sym2 U) := affineDirection (e.map Subtype.val)
  let g (j : Option F) := f (j.getD 0)
  have hbalanced : Balanced (g ∘ d) := by
    simpa only [g,d,Function.comp_def,ordinary_slope_of_direction] using hb
  have each (k : Fin s) (_ : k∈univ) : 3≤(univ.filter fun j => g j=k).card :=
    at_least_three_directions_per_color hs (by simpa using big) d (fun j x => affineIntercept j x.val)
      (fun j x y ne => affine_line_label j x.val y.val (fun eq => ne (Subtype.ext eq))) g hbalanced k
  have sum := sum_le_sum each
  simpa [sum_card_fiberwise_eq_card_filter,Nat.mul_comm s 3] using sum

end AffineField

end Erdos617
