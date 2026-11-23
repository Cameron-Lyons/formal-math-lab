import CoreCounts
import AdditiveCore
import MultiplierSAT
import Lean

/-! # The order-eight multiplier on the finite part of a 20-point seed -/

namespace Erdos835.TwentyPoint
namespace MultiplierCore

open Finset

/-- Multiply residues by nine modulo seventeen. The three extra labels are fixed. -/
def multiplier (x : Vertex) : Vertex :=
  if x.val < 17 then ⟨9 * x.val % 17, by omega⟩ else x

private abbrev Quad := Finset Vertex
private abbrev Rule := List (List Nat)
private abbrev Lit := Nat × Bool

private def makeQuad (xs : List Nat) : Quad := (xs.map (Fin.ofNat 20)).toFinset

private def decode {α : Type} [Lean.FromJson α] [Inhabited α] (s : String) : α :=
  ((Lean.Json.parse s).bind Lean.fromJson?).toOption.getD default

private def blocks : Array Quad :=
  ((decode (include_str "certificates"/"multiplier8-blocks.json") : List (List Nat)).map makeQuad).toArray
private def rules : List Rule := decode (include_str "certificates"/"multiplier8-rules.json")
private def block (i : Nat) : Quad := blocks[i]?.getD ∅
private def header (r : Rule) := r[0]?.getD []
private def terms (r : Rule) := r[1]?.getD []
private def exceptions (r : Rule) := r[2]?.getD []
private inductive Kind where
  | orbit (q : Quad)
  | shift (d : Fin 17)
  | overlap
  | degree (x y : Vertex)
  | additive
  | bad

private def kind (r : Rule) : Kind :=
  match header r with
  | [0,a,b,c,d] => .orbit (makeQuad [a,b,c,d])
  | [1,d] => .shift (Fin.ofNat 17 d)
  | [2] => .overlap
  | [3,x,y] => .degree (Fin.ofNat 20 x) (Fin.ofNat 20 y)
  | [4] => .additive
  | _ => .bad

private def positive (r : Rule) : Bool :=
  match kind r with
  | .orbit _ | .degree _ _ => true
  | _ => false

private def rawClause (r : Rule) : List Lit := (terms r).map (fun u => (u/8, positive r))
private def setOfBlocks (l : List Nat) : Finset Quad := (l.map block).toFinset
private def mobile : Quad := univ.filter fun x => x.val < 17
private def allQuads := mobile.powersetCard 4
private def additiveBlocks := allQuads.filter fun s => s.sum Fin.val % 17 = 0

private def valid (r : Rule) : Bool :=
  let o := terms r
  match kind r with
  | .orbit q =>
    decide (q.card = 4 ∧ o.map block = List.ofFn (fun j : Fin 17 => translate j q))
  | .shift d =>
    let b := block (o.headD 0)
    decide (o.length = 2 ∧ b.card = 4 ∧ d ≠ 0 ∧
      block (o[1]?.getD 0) = translate d b)
  | .overlap =>
    let b := block (o.headD 0)
    let b' := block (o[1]?.getD 0)
    decide (o.length = 2 ∧ b ≠ b' ∧ (b ∩ b').card = 3)
  | .degree x y =>
    let e := setOfBlocks (exceptions r)
    let l := setOfBlocks o
    decide (x.val < 17 ∧ y.val < 17 ∧ x ≠ y ∧ e.card < 6 ∧
      (allQuads.filter fun B => x ∈ B ∧ y ∈ B) ⊆ e ∪ l)
  | .additive => decide (additiveBlocks ⊆ setOfBlocks o)
  | _ => false

private def scaledTable : Bool :=
  (List.range blocks.size).all fun n => decide
    ((block n).image multiplier = block (8*(n/8) + (n%8+1)%8) ∧
      ∀ x ∈ block n, x.val < 17)

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 20000000

private theorem tableSize : blocks.size = 2416 := by native_decide
private theorem table_scales : scaledTable = true := by native_decide

private theorem equivBlock {D : Quad → Prop}
    (invariant : ∀ Q, (∀ x ∈ Q, x.val < 17) → (D (Q.image multiplier) ↔ D Q))
    {n : Nat} (hn : n < blocks.size) : D (block n) ↔ D (block (8 * (n / 8))) := by
  let k := n/8
  have aux (e : Nat) (he : e < 8) : D (block (8*k+e)) ↔ D (block (8*k)) := by
    induction e with
    | zero => simp
    | succ e ih =>
      have hbound : 8*k+e < blocks.size := by rw [tableSize] at hn ⊢; dsimp [k]; omega
      have ht := of_decide_eq_true (List.all_eq_true.mp table_scales (8*k+e)
        (List.mem_range.mpr hbound))
      have ei : 8 * ((8*k+e)/8) + ((8*k+e)%8+1)%8 = 8*k+(e+1) := by omega
      rw [ei] at ht
      exact (ht.1 ▸ invariant _ ht.2).trans (ih (by omega))
  simpa only [show 8*k+n%8 = n by dsimp [k]; omega] using aux (n%8) (by omega)

private theorem mem_all {D : Quad → Prop} (hD : QuadrupleSeed univ translate D)
    {Q : Quad} (h : D Q) (hf : ∀ x ∈ Q, x.val < 17) : Q ∈ allQuads :=
  mem_powersetCard.mpr ⟨fun _ hx => mem_filter.mpr ⟨mem_univ _, hf _ hx⟩, (hD.blocks _ h).2⟩

private theorem mem_named {xs : List Nat} {Q : Quad} :
    Q ∈ setOfBlocks xs ↔ ∃ n ∈ xs, block n = Q := by simp [setOfBlocks]

private theorem shiftZero (B : Quad) : translate 0 B = B := by
  have hz (x : Vertex) : shift 0 x = x := by
    unfold shift
    split <;> rename_i h
    · apply Fin.ext
      simp [Nat.mod_eq_of_lt h]
    · rfl
  have eq : shift 0 = id := funext hz
  simp [translate, eq]

/-- Every certified clause is a necessary condition for the design. -/
private theorem geometry {D : Quad → Prop} (hD : QuadrupleSeed univ translate D)
    {a : Nat → Bool} {r : Rule}
    (hv : valid r = true)
    (agreement : ∀ n ∈ terms r, (a (n/8) = true ↔ D (block n))) :
    ∃ l ∈ rawClause r, a l.1 = l.2 := by
  classical
  by_contra no
  have all (n : Nat) (hn : n ∈ terms r) : a (n/8) ≠ positive r :=
    fun eq => no ⟨_, List.mem_map.mpr ⟨n, hn, rfl⟩, eq⟩
  have neg (hpol : positive r = false) (n : Nat) (hn : n ∈ terms r) : D (block n) := by
    apply (agreement n hn).mp
    have := all n hn
    rw [hpol] at this
    cases e : a (n/8) <;> simp_all
  have pos (hpol : positive r = true) (n : Nat) (hn : n ∈ terms r) : ¬ D (block n) := by
    exact fun h => all n hn (hpol ▸ (agreement n hn).mpr h)
  have both (hl : (terms r).length = 2) (hp : positive r = false) :
      D (block ((terms r).headD 0)) ∧ D (block (((terms r)[1]?).getD 0)) := by
    obtain ⟨x,y,he⟩ : ∃ x y, terms r = [x,y] := by
      generalize he : terms r = l at hl ⊢
      rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, zs⟩⟩⟩ <;> simp_all
    rw [he]
    exact ⟨neg hp x (by simp [he]), neg hp y (by simp [he])⟩
  cases hk : kind r with
  | bad => simp [valid, hk] at hv
  | orbit q =>
    simp only [valid, hk, decide_eq_true_eq] at hv
    obtain ⟨j,hj,_⟩ := hD.orbits q (subset_univ _) hv.1
    have hm : translate j q ∈ (terms r).map block := hv.2 ▸ List.mem_ofFn.mpr ⟨j,rfl⟩
    obtain ⟨n,hn,eq⟩ := List.mem_map.mp hm
    exact pos (by simp [positive,hk]) n hn (eq ▸ hj)
  | shift d =>
    simp only [valid, hk, decide_eq_true_eq] at hv
    obtain ⟨hd, hd'⟩ := both hv.1 (by simp [positive,hk])
    have hu := hD.orbits _ (subset_univ _) hv.2.1
    exact hv.2.2.1 (hu.unique (hv.2.2.2 ▸ hd') (by simpa only [shiftZero] using hd))
  | overlap =>
    simp only [valid, hk, decide_eq_true_eq] at hv
    obtain ⟨hd, hd'⟩ := both hv.1 (by simp [positive,hk])
    have hu := hD.triples _ (subset_univ _) hv.2.2
    exact hv.2.1 (hu.unique ⟨hd, inter_subset_left⟩ ⟨hd', inter_subset_right⟩)
  | degree x y =>
    simp only [valid, hk, decide_eq_true_eq] at hv
    obtain ⟨hx,hy,hxy,hsmall,hcover⟩ := hv
    have sub : coreBlocks D {x,y} ⊆ setOfBlocks (exceptions r) := by
      intro Q hQ
      obtain ⟨⟨hd,hp⟩,hm⟩ := mem_coreBlocks.mp hQ
      have inside := hcover (mem_filter.mpr ⟨mem_all hD hd hm, hp (by simp), hp (by simp)⟩)
      rcases mem_union.mp inside with he | hc
      · exact he
      · obtain ⟨n, hn, eq⟩ := mem_named.mp hc
        exact (pos (by simp [positive,hk]) n hn (eq ▸ hd)).elim
    have := card_le_card sub
    have := core_pair_degree_lower hD hx hy hxy
    omega
  | additive =>
    simp only [valid, hk, decide_eq_true_eq] at hv
    apply Erdos835.no_additive_quadruple_extension D (fun B h => (hD.blocks B h).2)
      (fun T ht => hD.triples T (subset_univ _) ht)
    intro Q h4 hf hs
    have hm : Q ∈ allQuads := mem_powersetCard.mpr
      ⟨fun _ hx => mem_filter.mpr ⟨mem_univ _, hf _ hx⟩, h4⟩
    obtain ⟨n,hn,rfl⟩ := mem_named.mp (hv (mem_filter.mpr ⟨hm,hs⟩))
    exact neg (by simp [positive,hk]) n hn

private def packets := rules.toArray

private def check (r : Rule) (c : List Lit) : Bool :=
  valid r && (terms r).all (fun n => decide (n < blocks.size)) &&
  (rawClause r).all (fun l => c.contains l)

private def checkAll : Bool :=
  (MultiplierSAT.certificateClauses.zipIdx).all (fun p =>
    check (packets[p.2]?.getD []) p.1)

private theorem checks_pass : checkAll = true := by native_decide

/-- A cyclic 20-point seed cannot have even its all-moving part preserved
by multiplication by 9 on the 17-cycle. No multiplier action on blocks
involving any of the three extra points is assumed. -/
theorem no_order_eight_multiplier {D : Finset Vertex → Prop}
    (hD : QuadrupleSeed univ translate D)
    (invariant : ∀ Q, (∀ x ∈ Q, x.val < 17) → (D (Q.image multiplier) ↔ D Q)) : False := by
  classical
  let a (i : Nat) : Bool := decide (D (block (8*i)))
  apply MultiplierSAT.unrealizable a
  intro C hC
  obtain ⟨i, hi, eq⟩ := List.mem_iff_getElem.mp hC
  have hpair : (C,i) ∈ MultiplierSAT.certificateClauses.zipIdx := by
    apply List.mem_iff_getElem.mpr
    exact ⟨i, by simpa using hi, by simp [eq]⟩
  have hc := List.all_eq_true.mp checks_pass (C,i) hpair
  let r := packets[i]?.getD []
  change check r C = true at hc
  obtain ⟨⟨hv, hbound⟩, literals⟩ := Bool.and_eq_true_iff.mp hc |>.imp_left Bool.and_eq_true_iff.mp
  have agreement (n : Nat) (hn : n ∈ terms r) : a (n/8) = true ↔ D (block n) := by
    simpa only [a, decide_eq_true_eq] using
      (equivBlock invariant (of_decide_eq_true (List.all_eq_true.mp hbound n hn))).symm
  obtain ⟨l,hl,ha⟩ := geometry hD hv agreement
  exact ⟨l, List.contains_iff_mem.mp (List.all_eq_true.mp literals l hl), ha⟩

end MultiplierCore
end Erdos835.TwentyPoint
