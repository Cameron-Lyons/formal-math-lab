import Splice

/-!
Verify a 25-cell cap or a 64-cell tail using one base-three integer. Reading a row
from its right end exposes the lower triple as a residue modulo 27. The kernel
proof identifies the resulting mask with the ordinary geometric row scan and
recovers the integer as the fingerprint of the decoded piece.
-/
namespace TBoards.Splice.Packed

/-- Decode a fixed-width row, retaining any leading zeros. -/
def row : Nat → Nat → List Nat
  | 0, _ => []
  | w+1, n => row w (n/3) ++ [n%3]

@[simp] theorem row_length (w n : Nat) : (row w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [row, ih]

@[simp] theorem row_colors (w n : Nat) : (row w n).all (· < 3) = true := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [row, ih, Nat.mod_lt n (by decide : 0 < 3)]

theorem fold_row (w n start : Nat) :
    (row w n).foldl (fun a c => 3*a+c) start = start*3^w + n%3^w := by
  induction w generalizing n with
  | zero => simp [row, Nat.mod_one]
  | succ w ih =>
    simp only [row, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    rw [Nat.pow_succ', Nat.mod_mul]
    simp [Nat.mul_add, Nat.mul_left_comm, Nat.add_comm,
      Nat.add_left_comm]

private theorem scan_snoc (u s : List Nat) (x a b c : Nat) (h : u.length = s.length) :
    scanRow (u ++ [x]) (s ++ [a,b,c]) =
      scanRow u (s ++ [a,b]) ++ [(x,a,b,c)] := by
  induction u generalizing s with
  | nil =>
    have : s = [] := List.length_eq_zero_iff.mp h.symm
    simp [this, scanRow]
  | cons v vs ih =>
    cases s with
    | nil => simp at h
    | cons z zs =>
      have ht : vs.length = zs.length := by simpa using h
      have hi := ih zs ht
      cases zs with
      | nil => simpa only [List.cons_append, List.nil_append, scanRow, List.cons.injEq,
          true_and] using hi
      | cons q qs =>
        cases qs with
        | nil => simpa only [List.cons_append, List.nil_append, scanRow, List.cons.injEq,
            true_and] using hi
        | cons t ts => simpa only [List.cons_append, scanRow, List.cons.injEq, true_and] using hi

private theorem mask_append (a b : List Nat) :
    codeMask (a ++ b) = codeMask a ||| codeMask b := by
  induction a with
  | nil => simp [codeMask]
  | cons c cs ih => simp [codeMask, ih, Nat.or_assoc]

/-- Compute the pattern mask from right to left. -/
def rowMask : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | w+1, u, l => (1 <<< (27*(u%3) + l%27)) ||| rowMask w (u/3) (l/3)

theorem mask_scan (w u l : Nat) :
    codeMask ((scanRow (row w u) (row (w+2) l)).map patternKey) = rowMask w u l := by
  induction w generalizing u l with
  | zero => simp [row, scanRow, codeMask, rowMask]
  | succ w ih =>
    let a := l/3/3%3
    let b := l/3%3
    let c := l%3
    let s := row w (l/3/3/3)
    have e3 : row (w+1+2) l = s ++ [a,b,c] := by simp [row, s, a, b, c]
    have e2 : row (w+2) (l/3) = s ++ [a,b] := by simp [row, s, a, b]
    have eh : (row w (u/3)).length = s.length := by simp [s]
    change codeMask ((scanRow (row w (u/3) ++ [u%3]) _).map _) = _
    rw [e3, scan_snoc _ _ _ _ _ _ eh, ← e2, List.map_append, mask_append, ih]
    simp only [List.map_cons, List.map_nil, codeMask, Nat.or_zero, rowMask]
    rw [Nat.or_comm, Nat.shiftLeft_eq, Nat.one_mul]
    have ee : patternKey (u%3,a,b,c) = 27*(u%3)+l%27 := by
      change 27*(u%3) + 9*(l/3/3%3) + 3*(l/3%3) + l%3 = 27*(u%3) + l%27
      omega
    rw [ee]

-- The last digits of each quotient encode the row ending at that position.
private def throughRow8 (x : Nat) := x / 3^19
private def throughRow7 (x : Nat) := throughRow8 x / 3^17
private def throughRow6 (x : Nat) := throughRow7 x / 3^15

def tail (x : Nat) : Board := [row 13 (throughRow6 x), row 15 (throughRow7 x), row 17 (throughRow8 x), row 19 x]

def tailMask (pivot x : Nat) :=
  rowMask 11 pivot (throughRow6 x) ||| rowMask 13 (throughRow6 x) (throughRow7 x) |||
    rowMask 15 (throughRow7 x) (throughRow8 x) ||| rowMask 17 (throughRow8 x) x

theorem tail_mask (p x : Nat) : codeMask (stripCodes (row 11 p :: tail x)) = tailMask p x := by
  simp only [tail, stripCodes, mask_append, codeMask]
  rw [mask_scan 11, mask_scan 13, mask_scan 15, mask_scan 17]
  simp only [tailMask, Nat.or_zero, Nat.or_assoc]

theorem tail_code (x : Nat) (hx : x < 3^64) : boardCode (tail x) = x := by
  simp only [boardCode, tail, List.flatten_cons, List.flatten_nil, List.foldl_append, fold_row,
    Nat.zero_mul, Nat.zero_add, List.foldl_nil, throughRow6, throughRow7, throughRow8]
  omega

def fastTail (g : Group) (p x : Nat) := decide (x < 3^64) && decide (tailMask p x = g.lowerMask)

theorem tail_checked (g : Group) (p x : Nat) (hk : g.k = 5) (hp : g.pivot = row 11 p)
    (hx : fastTail g p x = true) : g.tailOK (tail x) = true := by
  unfold Group.tailOK
  rw [hk, hp, tail_mask]
  simp only [fastTail, Bool.and_eq_true_iff, decide_eq_true_eq] at hx
  simp [tail, rowsOK, hx.2]

private def cap3 (x : Nat) := x / 3^9
private def cap2 (x : Nat) := cap3 x / 3^7
private def cap1 (x : Nat) := cap2 x / 3^5
private def cap0 (x : Nat) := cap1 x / 3^3

def cap (x : Nat) : Board :=
  [row 1 (cap0 x), row 3 (cap1 x), row 5 (cap2 x), row 7 (cap3 x), row 9 x]

def capMask (pivot x : Nat) :=
  rowMask 1 (cap0 x) (cap1 x) ||| rowMask 3 (cap1 x) (cap2 x) |||
    rowMask 5 (cap2 x) (cap3 x) ||| rowMask 7 (cap3 x) x ||| rowMask 9 x pivot

theorem cap_mask (p x : Nat) : codeMask (stripCodes (cap x ++ [row 11 p])) = capMask p x := by
  simp only [cap, List.cons_append, List.nil_append, stripCodes, mask_append, codeMask]
  rw [mask_scan 1, mask_scan 3, mask_scan 5, mask_scan 7, mask_scan 9]
  simp only [capMask, Nat.or_zero, Nat.or_assoc]

theorem cap_code (x : Nat) (hx : x < 3^25) : boardCode (cap x) = x := by
  simp only [boardCode, cap, List.flatten_cons, List.flatten_nil, List.foldl_append, fold_row,
    Nat.zero_mul, Nat.zero_add, List.foldl_nil, cap0, cap1, cap2, cap3]
  omega

def fastCap (g : Group) (p x : Nat) := decide (x < 3^25) && decide (capMask p x = g.upperMask)

theorem cap_checked (g : Group) (p x : Nat) (hk : g.k = 5) (hp : g.pivot = row 11 p)
    (hx : fastCap g p x = true) : g.capOK (cap x) = true := by
  unfold Group.capOK
  rw [hk, hp, cap_mask]
  simp only [fastCap, Bool.and_eq_true_iff, decide_eq_true_eq] at hx
  simp [cap, rowsOK, hx.2]

private def checkedBatch {check : Board → Bool} (decode : Nat → Board) (test : Nat → Bool)
    (valid : ∀ x, test x = true → check (decode x) = true)
    (roundtrip : ∀ x, test x = true → boardCode (decode x) = x)
    (codes : List Nat) (h : codes.all test = true) : Group.Batch check where
  codes := codes
  values := codes.map decode
  valid := by
    apply List.all_eq_true.mpr
    intro b hb
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
    exact valid x (List.all_eq_true.mp h x hx)
  fingerprints := by
    induction codes with
    | nil => rfl
    | cons x xs ih =>
      have hh : test x = true ∧ xs.all test = true := by
        simpa only [List.all_cons, Bool.and_eq_true_iff] using h
      simp only [List.map_cons, roundtrip x hh.1, ih hh.2]

def capBatch (g : Group) (p : Nat) (hk : g.k = 5) (hp : g.pivot = row 11 p)
    (codes : List Nat) (h : codes.all (fastCap g p) = true) : Group.Batch g.capOK :=
  checkedBatch cap (fastCap g p) (fun x => cap_checked g p x hk hp)
    (fun x hx => cap_code x (of_decide_eq_true (Bool.and_eq_true_iff.mp hx).1)) codes h

def tailBatch (g : Group) (p : Nat) (hk : g.k = 5) (hp : g.pivot = row 11 p)
    (codes : List Nat) (h : codes.all (fastTail g p) = true) : Group.Batch g.tailOK :=
  checkedBatch tail (fastTail g p) (fun x => tail_checked g p x hk hp)
    (fun x hx => tail_code x (of_decide_eq_true (Bool.and_eq_true_iff.mp hx).1)) codes h

end TBoards.Splice.Packed
