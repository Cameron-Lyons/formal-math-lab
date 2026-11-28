import Ramsey556.Cert16.Tables

namespace Ramsey556.Cert16

def GoodRange (n lo hi : Nat) : Prop :=
  ∀ i, lo ≤ i → i < hi → RowGood n ((table n).get i) (table (n+1))

theorem joinRanges {n a b c : Nat} (left : GoodRange n a b) (right : GoodRange n b c) : GoodRange n a c := by
  intro i lo hi
  by_cases h : i < b
  · exact left i lo h
  · exact right i (by omega) hi

end Ramsey556.Cert16
