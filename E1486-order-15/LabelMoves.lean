import Std

namespace E1486.Encoding

abbrev V := Fin 15
def verts := List.finRange 15

def swap (a b x : V) := if x=a then b else if x=b then a else x
def perm (kind : Nat) (a b x : V) : V :=
  if kind = 2 then swap a b (swap (a+1) (b+1) x) else swap a b x

def sqMoves (k j : Nat) : List (Nat × V × V) := Id.run do
  let mut ls := []
  for a in verts do
    for b in verts do
      if a < b then
        if b.val < j then ls := (0,a,b)::ls
        if j ≤ a.val && b.val < k && (a.val-j)%2=0 then
          if b.val = a.val+1 then ls := (1,a,b)::ls
          if (b.val-j)%2=0 then ls := (2,a,b)::ls
  return ls

end E1486.Encoding
