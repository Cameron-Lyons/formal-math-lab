import Std

namespace ThreeStacks

/-- `Pass input stack output` is a complete legal run on one LIFO stack.
    The head of each list is the next card, or the top of the stack. -/
inductive Pass : List Nat → List Nat → List Nat → Prop where
  | done : Pass [] [] []
  | push {x : Nat} {i s o : List Nat} : Pass i (x :: s) o → Pass (x :: i) s o
  | pop {x : Nat} {i s o : List Nat} : Pass i s o → Pass i (x :: s) (x :: o)

/-- The two intermediate lists are the orders in which cards leave stacks 1 and 2. -/
def SortsTo (p q : List Nat) : Prop :=
  ∃ A B, Pass p [] A ∧ Pass A [] B ∧ Pass B [] q

def target (n : Nat) : List Nat := List.range' 1 n

def IsDeck (n : Nat) (p : List Nat) : Prop := p.Perm (target n)

def Sortable (n : Nat) (p : List Nat) : Prop := SortsTo p (target n)

def published : List Nat := [6, 3, 12, 8, 17, 5, 2, 11, 7, 19, 14, 10, 4, 18, 13, 21, 16, 9, 20, 15, 1]

/-- A single stack forbids the input triple a,b,c leaving as c,a,b. -/
def Respects (u v : List Nat) : Prop :=
  ∀ a b c : Nat, u.idxOf a < u.idxOf b → u.idxOf b < u.idxOf c →
    v.idxOf c < v.idxOf a → v.idxOf a < v.idxOf b → False

end ThreeStacks
