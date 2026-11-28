import ThreeStacks.Model

namespace ThreeStacks.OrderProof

/-- All the assumptions used by the finite order refutation. -/
structure Witness where
  first : List Nat
  second : List Nat
  firstDeck : IsDeck 21 first
  secondDeck : IsDeck 21 second
  entering : Respects published first
  middle : Respects first second
  leaving : Respects second (target 21)

/-- Card `a` precedes card `b` in the indicated intermediate order. -/
def Before (w : Witness) (layer : Bool) (a b : Nat) : Prop :=
  let p := if layer then w.second else w.first
  p.idxOf a < p.idxOf b

/- A direct proof of distinct index positions keeps the generated theorem free
   even of the standard extensionality and choice axioms. -/
private theorem transfer {p q : List Nat} (e : p.Perm q) {a : Nat} : a ∈ q → a ∈ p := by
  induction e with
  | nil => exact id
  | cons x _ ih =>
    intro h
    cases h with
    | head => exact .head _
    | tail _ m => exact .tail _ (ih m)
  | swap x y l =>
    intro h
    cases h with
    | head => exact .tail _ (.head _)
    | tail _ m =>
      cases m with
      | head => exact .head _
      | tail _ m => exact .tail _ (.tail _ m)
  | trans _ _ ih₁ ih₂ => exact fun h => ih₁ (ih₂ h)

private theorem consFalse {a x : Nat} (h : (x == a) = false) (xs : List Nat) (n : Nat) :
    List.findIdx.go (fun v => v == a) (x :: xs) n = List.findIdx.go (fun v => v == a) xs (n+1) := by
  change (if (x == a) then n else _) = _
  rw [h]
  rfl

private theorem consTrue {a x : Nat} (h : (x == a) = true) (xs : List Nat) (n : Nat) :
    List.findIdx.go (fun v => v == a) (x :: xs) n = n := by
  change (if (x == a) then n else _) = _
  rw [h]
  rfl

private theorem above (a : Nat) (xs : List Nat) (n : Nat) : n ≤ List.findIdx.go (fun v => v == a) xs n := by
  induction xs generalizing n with
  | nil => exact Nat.le_refl n
  | cons x xs ih =>
    cases test : (x == a) with
    | true => rw [consTrue test]; exact Nat.le_refl n
    | false => rw [consFalse test]; exact Nat.le_trans (Nat.le_succ _) (ih _)

private theorem reflexiveBEq (a : Nat) : (a == a) = true := by
  induction a with
  | zero => rfl
  | succ a ih => exact ih

private theorem beqImpliesEq (x y : Nat) : (x == y) = true → x = y := by
  induction x generalizing y with
  | zero =>
    cases y with
    | zero => exact fun _ => rfl
    | succ y => exact fun h => False.elim (Bool.false_ne_true h)
  | succ x ih =>
    cases y with
    | zero => exact fun h => False.elim (Bool.false_ne_true h)
    | succ y => exact fun h => congrArg Nat.succ (ih y h)

private theorem tailMem {a x : Nat} {xs : List Nat} (neg : (x == a) = false) (h : a ∈ x :: xs) : a ∈ xs := by
  cases h with
  | head => exact False.elim (Bool.noConfusion ((reflexiveBEq a).symm.trans neg))
  | tail _ hm => exact hm

private theorem separate (a b : Nat) (neq : a ≠ b) (xs : List Nat) (ma : a ∈ xs) (mb : b ∈ xs) (n : Nat) :
    List.findIdx.go (fun v => v == a) xs n ≠ List.findIdx.go (fun v => v == b) xs n := by
  induction xs generalizing n with
  | nil => cases ma
  | cons x xs ih =>
    cases isA : (x == a) with
    | true =>
      cases isB : (x == b) with
      | true => exact False.elim (neq ((beqImpliesEq _ _ isA).symm.trans (beqImpliesEq _ _ isB)))
      | false => rw [consTrue isA, consFalse isB]; exact Nat.ne_of_lt (above b xs (n+1))
    | false =>
      cases isB : (x == b) with
      | true => rw [consFalse isA, consTrue isB]; exact (Nat.ne_of_lt (above a xs (n+1))).symm
      | false => rw [consFalse isA, consFalse isB]; exact ih (tailMem isA ma) (tailMem isB mb) _

theorem alternatives (w : Witness) (layer : Bool) (a b : Nat)
    (ha : a ∈ target 21) (hb : b ∈ target 21) (hne : a ≠ b) :
    Before w layer a b ∨ Before w layer b a := by
  let p := if layer then w.second else w.first
  have hp : p.Perm (target 21) := by
    cases layer <;> first | exact w.firstDeck | exact w.secondDeck
  exact Nat.lt_or_gt_of_ne (separate a b hne p (transfer hp ha) (transfer hp hb) 0)

theorem cycle (w : Witness) (layer : Bool) (a b c : Nat)
    (h₁ : Before w layer a b) (h₂ : Before w layer b c) (h₃ : Before w layer c a) :
    False := (Nat.lt_irrefl _) (Nat.lt_trans (Nat.lt_trans h₁ h₂) h₃)

theorem forceLeft {p q : Prop} (h : p ∨ q) (impossible : q → False) : p :=
  h.elim id (fun b => False.elim (impossible b))

theorem forceRight {p q : Prop} (h : p ∨ q) (impossible : p → False) : q :=
  h.elim (fun a => False.elim (impossible a)) id

end ThreeStacks.OrderProof
