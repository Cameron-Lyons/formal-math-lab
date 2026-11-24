import Std.Sat.CNF
import Std.Tactic.BVDecide.LRAT
import Lean.Elab.Term
import Laws

/-! No nine-element multiplication table obeys Equation 677 and breaks Equation 255. -/

namespace Nine
open Std.Sat
abbrev Table (n : Nat) := Fin n → Fin n → Fin n
abbrev Point := Fin 9

private def FailsAt (op : Table 9) (x : Point) := x ≠ op (op (op x x) x) x

/-- Equation 677 supplies a preimage in each row. -/
private theorem row_surjective {op : Table 9} (h : Eq677 op) (y : Point) : Function.Surjective (op y) :=
  fun x => ⟨_, (h x y).symm⟩

/-- If two inputs had the same output, eight inputs would still cover all nine outputs. -/
private theorem row_injective {op : Table 9} (h : Eq677 op) (y : Point) : Function.Injective (op y) := by
  intro a b eq
  apply Classical.byContradiction
  intro ne
  let xs := List.finRange 9
  have cover : xs ⊆ (xs.erase a).map (op y) := by
    intro v _
    obtain ⟨w, rfl⟩ := row_surjective h y v
    by_cases hw : w = a
    · subst w
      exact List.mem_map.mpr ⟨b, (List.mem_erase_of_ne (Ne.symm ne)).2 (List.mem_finRange _), eq.symm⟩
    · exact List.mem_map.mpr ⟨w, (List.mem_erase_of_ne hw).2 (List.mem_finRange _), rfl⟩
  have impossible := (List.nodup_finRange 9).length_le_of_subset cover
  simp [xs, List.length_erase_of_mem (List.mem_finRange a)] at impossible

private def swap (a b x : Point) := if x = a then b else if x = b then a else x
private def relabel (p : Point → Point) (op : Table 9) : Table 9 := fun x y => p (op (p x) (p y))

private theorem transport {op : Table 9} {p : Point → Point} (inv : ∀ z, p (p z) = z)
    (h : Eq677 op) (x : Point) (bad : FailsAt op (p x)) :
    Eq677 (relabel p op) ∧ FailsAt (relabel p op) x := by
  constructor
  · intro a b
    simpa [relabel, inv] using congrArg p (h (p a) (p b))
  · intro eq
    exact bad (by simpa [relabel, inv] using congrArg p eq)

/-- Move an output above the bound down to the bound, fixing every smaller label. -/
private def lower (bound out : Point) := if bound < out then swap bound out else id

private theorem swap_facts : ∀ a b : Point,
    (∀ z, swap a b (swap a b z) = z) ∧ swap a b a = b := by decide +kernel

/-- A renaming at column i fixes earlier column labels and bounds their outputs. -/
private theorem lower_facts : ∀ (i : Fin 8) (b : Point),
    let p := lower i.succ b
    (∀ z, p (p z) = z) ∧ p 0 = 0 ∧
    ∀ j z : Point, j.val ≤ i.val → (j.val < i.val → z.val ≤ j.val+1) →
      (j = i.castSucc → z = b) → p j = j ∧ (p z).val ≤ j.val+1 := by decide +kernel

/-- Name the failing point zero. Scanning row zero, swap an output above i+1
with i+1. This fixes all earlier inputs and outputs. -/
private theorem normalized {op : Table 9} (law : Eq677 op) (fail : ¬Eq255 op) :
    ∃ t : Table 9, Eq677 t ∧ FailsAt t 0 ∧ ∀ j : Point, (t 0 j).val ≤ j.val+1 := by
  obtain ⟨x, hx⟩ := Classical.not_forall.mp fail
  have ⟨inv, atZero⟩ := swap_facts 0 x
  obtain ⟨h, bad⟩ := transport inv law 0 (atZero ▸ hx)
  have step (k : Nat) (hk : k < 9) :
      ∃ t : Table 9, Eq677 t ∧ FailsAt t 0 ∧ ∀ j : Point, j.val < k → (t 0 j).val ≤ j.val+1 := by
    induction k with
    | zero => exact ⟨_, h, bad, fun _ hj => by omega⟩
    | succ k ih =>
      obtain ⟨t, ht, hb, prev⟩ := ih (by omega)
      let i : Fin 8 := ⟨k, by omega⟩
      let b := t 0 i.castSucc
      obtain ⟨inv, atZero, localBound⟩ := lower_facts i b
      obtain ⟨law',bad'⟩ := transport inv ht 0 (by simpa only [atZero] using hb)
      refine ⟨_,law',bad',fun j hj => ?_⟩
      obtain ⟨fixed, bound⟩ := localBound j (t 0 j) (Nat.le_of_lt_succ hj) (prev j) (congrArg (t 0))
      simpa only [relabel, atZero, fixed] using bound
  obtain ⟨t, ht, hb, norm⟩ := step 8 (by decide)
  exact ⟨t, ht, hb, fun j => if hj : j.val < 8 then norm j hj else by have := (t 0 j).isLt; omega⟩

/-- An entry `(r,c,v)` asserts that row r, column c contains v. -/
private abbrev Entry := Point × Point × Point

/-- A rule says that if all its premises hold, at least one conclusion holds. -/
private structure Rule where
  premises : List Entry
  conclusions : List Entry

private abbrev holds (op : Table 9) (e : Entry) : Prop :=
  let (r,c,v) := e
  op r c = v
private def Rule.Valid (op : Table 9) (rule : Rule) : Prop :=
  (∀ e ∈ rule.premises, holds op e) → ∃ e ∈ rule.conclusions, holds op e

private abbrev points := List.finRange 9
private def each (f : Point → List α) := points.flatMap f

private def exactlyOne (entry : Point → Entry) : List Rule :=
  ⟨[], points.map entry⟩ :: each fun a =>
    (points.filter fun b => a < b).map fun b => ⟨[entry a, entry b], []⟩

private theorem exactlyOne_valid {op : Table 9} {entry : Point → Entry} (i : Point)
    (h : ∀ j, holds op (entry j) ↔ j = i) : ∀ r ∈ exactlyOne entry, r.Valid op := by
  simp only [exactlyOne, each, List.forall_mem_cons, List.forall_mem_flatMap,
    List.forall_mem_map, List.mem_finRange, forall_const, List.mem_filter, true_and, decide_eq_true_eq]
  constructor
  · exact fun _ => ⟨entry i, List.mem_map.mpr ⟨i, List.mem_finRange _, rfl⟩, (h i).2 rfl⟩
  · intro a b hab
    simp [Rule.Valid, h]
    grind

/-- The rows are permutations, Equation 677 holds, Equation 255 fails at zero,
and the first row has been relabelled as above. -/
private def rules : List Rule :=
  (each fun x => each fun y =>
    exactlyOne (fun z => (x,y,z)) ++ exactlyOne (fun z => (x,z,y))) ++
  (each fun x => each fun y => each fun a => each fun b => each fun c =>
    [⟨[(y,x,a), (a,y,b), (x,b,c)], [(y,c,x)]⟩]) ++
  (each fun a => each fun b => [⟨[(0,0,a), (a,0,b), (b,0,0)], []⟩]) ++
  (each fun i => (points.filter fun z => i.val + 1 < z.val).map fun z => ⟨[(0,i,z)], []⟩)

private theorem rules_valid {op : Table 9} (h : Eq677 op) (bad : FailsAt op 0)
    (bound : ∀ i : Point, (op 0 i).val ≤ i.val+1) : ∀ r ∈ rules, r.Valid op := by
  simp only [rules, each, List.forall_mem_append, List.forall_mem_flatMap, List.forall_mem_map,
    List.mem_finRange, forall_const, List.mem_filter, true_and, decide_eq_true_eq,
    List.forall_mem_singleton]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro x y
    obtain ⟨j, hj⟩ := row_surjective h x y
    exact ⟨exactlyOne_valid (op x y) (by simp [holds, eq_comm]),
      exactlyOne_valid j (by simp [holds, ← hj, (row_injective h x).eq_iff])⟩
  · intro x y a b c
    simp [Rule.Valid, holds]
    grind [h x y]
  · intro a b
    simp [Rule.Valid, holds]
    unfold FailsAt at bad
    grind
  · intro i z hz
    simp [Rule.Valid, holds]
    intro he
    exact (Nat.not_lt_of_ge (bound i)) (he ▸ hz)

private def number : Entry → Nat
  | (r,c,v) => (r.val * 9 + c.val) * 9 + v.val
private def entryOf (n : Nat) : Entry := (Fin.ofNat 9 (n/81), Fin.ofNat 9 (n/9), Fin.ofNat 9 n)
private theorem entry_number : ∀ x y z, entryOf (number (x,y,z)) = (x,y,z) := by decide +kernel

private def clause (r : Rule) : CNF.Clause Nat := .ofLiterals
  ((r.premises.map fun e => (number e, false)) ++ (r.conclusions.map fun e => (number e, true)))

def formula : CNF Nat := ⟨(rules.map clause).toArray⟩

private theorem encode {t : Table 9} (valid : ∀ r ∈ rules, r.Valid t) :
    formula.Sat (fun n => decide (holds t (entryOf n))) := by
  apply CNF.sat_iff_all_mem_sat.mpr
  intro c hc
  obtain ⟨r, hr, rfl⟩ : ∃ r ∈ rules, clause r = c := by
    simpa [formula, CNF.Internal.mem_iff] using hc
  have roundtrip : ∀ e, entryOf (number e) = e := fun (x,y,z) => entry_number x y z
  have vr := valid r hr
  simp only [Rule.Valid] at vr
  simp [CNF.Clause.Sat, CNF.Clause.eval, clause, List.any_map, Function.comp_def,
    List.any_eq_true, roundtrip, -Prod.exists]
  grind

/-- Obtain an LRAT proof from the CaDiCaL executable shipped with Lean. -/
elab "orderNineCertificate%" : term => do
  let exe := ((← IO.appPath).parent.get! / "cadical").withExtension System.FilePath.exeExtension
  IO.FS.withTempFile fun input cnfPath => IO.FS.withTempFile fun _ proofPath => do
    input.putStr formula.dimacs
    input.flush
    let result ← IO.Process.output {
      cmd := exe.toString
      args := #["--quiet", "--lrat", "--no-binary", cnfPath.toString, proofPath.toString] }
    unless result.exitCode == 20 do throwError "CaDiCaL did not produce a refutation: {result.stderr}"
    return Lean.mkStrLit (← IO.FS.readFile proofPath)

set_option maxHeartbeats 0 in
private def certificate : String := orderNineCertificate%

open Std.Tactic.BVDecide in
private theorem no_counterexample : formula.Unsat :=
  LRAT.check_sound ((LRAT.parseLRATProof certificate.toUTF8).toOption.getD #[]) formula (by native_decide)

/-- Every nine-element multiplication table obeying Equation 677 obeys Equation 255. -/
theorem eq677_implies_eq255 (op : Table 9) (h : Eq677 op) : Eq255 op := by
  apply Classical.byContradiction
  intro failure
  obtain ⟨t, law, bad, bound⟩ := normalized h failure
  exact (CNF.unsat_iff_not_sat.mp no_counterexample _) (encode (rules_valid law bad bound))

end Nine
