/-
The CNF encoder of the frame method: a transcription of `code/frame/enc.py` (functions `atmost`,
`exactly`, class `Base` with `use_amo=True`, `case_extra` with the default flags
`use_F=use_V=use_H=True`, `use_P=use_M=use_S=False`, `debug=None`, and `dimacs`).

The Lean functions produce the same clauses, in the same order, with the same variable numbers as the
Python code, and `dimacs` produces the same text byte for byte (`scripts/compare_enc.py` compares the
SHA-256 of the two texts on many cases).

Style: total functional code over `List`, no mutable state.  Every fresh variable has a closed-form
number relative to the value `nv` of the variable counter at the start of the clause group that
allocates it, and every group comes as a pair "clauses emitted" / "number of fresh variables used":
started at counter `nv`, a group uses exactly the variables `nv + 1, ..., nv + new`.

Conventions.  Squares are `(x, y) = (column, row)`, `0 ≤ x, y < n`.  The sum diagonal of `(x, y)` is
`s = x + y` (`0 ≤ s ≤ 2n-2`).  The difference diagonal is `t = y - x` (`-(n-1) ≤ t ≤ n-1`) in the Python
code; here it is indexed by the natural number `i = t + (n-1) = y + (n-1) - x` (`0 ≤ i ≤ 2n-2`), see
`tIdx`.  A literal is a nonzero integer as in DIMACS: `v` is the variable `v ≥ 1`, `-v` its negation.
-/
module

public import Std.Sat.CNF.Basic

@[expose] public section

namespace QueenDomSat

/-- A clause: a list of DIMACS literals (nonzero integers). -/
abbrev Clause := List Int

/-! ### Cardinality constraints: the sequential counter of `enc.atmost` -/

/-- The counter variable `s[i][j]` ("at least `j+1` of `lits[0..i]` are true") of `enc.atmost`:
```
s = [[new() for _ in range(k)] for _ in range(n - 1)]
```
allocated when the variable counter is `nv`, so that `s[i][j] = nv + i*k + j + 1`
(`0 ≤ i ≤ n-2`, `0 ≤ j ≤ k-1`). -/
def seqVar (nv k i j : Nat) : Int := ((nv + i * k + j + 1 : Nat) : Int)

/-- The clauses of `enc.atmost` (main branch, `0 < k < len`) that are emitted for the literal
`l = lits[i]`, `len = len(lits)`:
```
cls.append([-lits[0], s[0][0]])
for j in range(1, k):
    cls.append([-s[0][j]])
for i in range(1, n - 1):
    cls.append([-lits[i], s[i][0]]); cls.append([-s[i - 1][0], s[i][0]])
    for j in range(1, k):
        cls.append([-lits[i], -s[i - 1][j - 1], s[i][j]]); cls.append([-s[i - 1][j], s[i][j]])
    cls.append([-lits[i], -s[i - 1][k - 1]])
cls.append([-lits[n - 1], -s[n - 2][k - 1]])
```
(first branch: `i = 0`; second branch: `1 ≤ i ≤ n-2`; third branch: `i = n-1`). -/
def atmostRow (nv k len : Nat) (l : Int) (i : Nat) : List Clause :=
  if i = 0 then
    [-l, seqVar nv k 0 0] :: (List.range' 1 (k - 1)).map fun j => [-seqVar nv k 0 j]
  else if i + 1 < len then
    [-l, seqVar nv k i 0] :: [-seqVar nv k (i - 1) 0, seqVar nv k i 0] ::
      (((List.range' 1 (k - 1)).flatMap fun j =>
          [[-l, -seqVar nv k (i - 1) (j - 1), seqVar nv k i j], [-seqVar nv k (i - 1) j, seqVar nv k i j]])
        ++ [[-l, -seqVar nv k (i - 1) (k - 1)]])
  else
    [[-l, -seqVar nv k (i - 1) (k - 1)]]

/-- The rows `atmostRow nv k len l i` of all literals `l = lits[i]`, in order. -/
def atmostRows (nv k len : Nat) (lits : List Int) : List Clause :=
  lits.zipIdx.flatMap fun p => atmostRow nv k len p.1 p.2

/-- The clauses of the main branch (`0 < k < len(lits)`) of `enc.atmost`, with counter variables
`seqVar nv k i j`. -/
def atmostSeq (lits : List Int) (k nv : Nat) : List Clause :=
  atmostRows nv k lits.length lits

/-- The clauses appended by `enc.atmost(lits, k, new, cls)` ("`sum(lits) <= k`; lits may contain repeated
literals (each occurrence counts)") when the variable counter is `nv`:
```
n = len(lits)
if k < 0:
    cls.append([]); return
if k >= n:
    return
if k == 0:
    for l in lits:
        cls.append([-l])
    return
```
and otherwise the sequential counter `atmostSeq`.  The bound `k` is an integer, as in Python. -/
def atmostCls (lits : List Int) (k : Int) (nv : Nat) : List Clause :=
  if k < 0 then [[]]
  else if (lits.length : Int) ≤ k then []
  else if k = 0 then lits.map fun l => [-l]
  else atmostSeq lits k.toNat nv

/-- The number of fresh variables allocated by `enc.atmost(lits, k, new, cls)` with `len = len(lits)`:
`(len - 1) * k` in the main branch `0 < k < len`, none in the three early returns. -/
def atmostNew (len : Nat) (k : Int) : Nat :=
  if 0 < k ∧ k < (len : Int) then (len - 1) * k.toNat else 0

/-- The clauses appended by `enc.exactly(lits, k, new, cls)`:
```
atmost(lits, k, new, cls)
atmost([-l for l in lits], len(lits) - k, new, cls)
``` -/
def exactlyCls (lits : List Int) (k : Int) (nv : Nat) : List Clause :=
  atmostCls lits k nv ++
    atmostCls (lits.map fun l => -l) ((lits.length : Int) - k) (nv + atmostNew lits.length k)

/-- The number of fresh variables allocated by `enc.exactly(lits, k, new, cls)`, `len = len(lits)`. -/
def exactlyNew (len : Nat) (k : Int) : Nat :=
  atmostNew len k + atmostNew len ((len : Int) - k)

/-! ### The variables of `Base`

```
self.q = [[self.new() for y in range(n)] for x in range(n)]
self.oR = [self.new() for y in range(n)]
self.oC = [self.new() for x in range(n)]
self.oT = {t: self.new() for t in range(-(n - 1), n)}
self.oS = {s: self.new() for s in range(0, 2 * n - 1)}
``` -/

/-- `q[x][y]`: a queen on the square `(x, y)`. -/
def qv (n x y : Nat) : Nat := x * n + y + 1

/-- `oR[y]`: the row `y` is occupied. -/
def oRv (n y : Nat) : Nat := n * n + y + 1

/-- `oC[x]`: the column `x` is occupied. -/
def oCv (n x : Nat) : Nat := n * n + n + x + 1

/-- `oT[t]` with `i = t + (n-1)`: the difference diagonal `t = y - x` is occupied (`0 ≤ i ≤ 2n-2`). -/
def oTv (n i : Nat) : Nat := n * n + 2 * n + i + 1

/-- `oS[s]`: the sum diagonal `s = x + y` is occupied (`0 ≤ s ≤ 2n-2`; this is
`n*n + 2*n + (2*n-1) + s + 1` for `n ≥ 1`). -/
def oSv (n s : Nat) : Nat := n * n + 4 * n + s

/-- The index `i = t + (n-1)` of the difference diagonal `t = y - x` through the square `(x, y)`. -/
def tIdx (n x y : Nat) : Nat := y + (n - 1) - x

/-- The number of variables `q, oR, oC, oT, oS`: `n*n + n + n + (2n-1) + (2n-1)`. -/
def baseVars (n : Nat) : Nat := n * n + 2 * n + 2 * (2 * n - 1)

/-! ### The lines (`fam`)

```
fam = {('R', y): [q[x][y] for x in range(n)] for y in range(n)}
fam.update({('C', x): [q[x][y] for y in range(n)] for x in range(n)})
fam.update({('T', t): [q[x][x + t] for x in range(n) if 0 <= x + t < n] for t in self.oT})
fam.update({('S', s): [q[x][s - x] for x in range(n) if 0 <= s - x < n] for s in self.oS})
```
A line is represented by the pair `(o, qs)` of its "occupied" variable and the list of the queen
variables of its squares; the dictionary order is rows, columns, difference diagonals (`t`
increasing), sum diagonals (`s` increasing). -/

/-- The queen variables of the row `y`. -/
def lineR (n y : Nat) : List Nat := (List.range n).map fun x => qv n x y

/-- The queen variables of the column `x`. -/
def lineC (n x : Nat) : List Nat := (List.range n).map fun y => qv n x y

/-- The queen variables of the difference diagonal `t = i - (n-1)`: the squares `(x, x + t)` with
`0 ≤ x + t < n`, i.e. `(x, x + i - (n-1))` with `n - 1 ≤ x + i` and `x + i - (n-1) < n`. -/
def lineT (n i : Nat) : List Nat :=
  ((List.range n).filter fun x => decide (n - 1 ≤ x + i ∧ x + i - (n - 1) < n)).map
    fun x => qv n x (x + i - (n - 1))

/-- The queen variables of the sum diagonal `s`: the squares `(x, s - x)` with `0 ≤ s - x < n`. -/
def lineS (n s : Nat) : List Nat :=
  ((List.range n).filter fun x => decide (x ≤ s ∧ s - x < n)).map fun x => qv n x (s - x)

/-- The rows, with their variables `oR[y]`. -/
def famR (n : Nat) : List (Nat × List Nat) := (List.range n).map fun y => (oRv n y, lineR n y)

/-- The columns, with their variables `oC[x]`. -/
def famC (n : Nat) : List (Nat × List Nat) := (List.range n).map fun x => (oCv n x, lineC n x)

/-- The difference diagonals, with their variables `oT[t]`. -/
def famT (n : Nat) : List (Nat × List Nat) :=
  (List.range (2 * n - 1)).map fun i => (oTv n i, lineT n i)

/-- The sum diagonals, with their variables `oS[s]`. -/
def famS (n : Nat) : List (Nat × List Nat) :=
  (List.range (2 * n - 1)).map fun s => (oSv n s, lineS n s)

/-- `fam.items()`. -/
def fam (n : Nat) : List (Nat × List Nat) := famR n ++ (famC n ++ (famT n ++ famS n))

/-! ### The clause groups of `Base` -/

/-- DEF for one line with occupied-variable `o` and queen variables `qs`:
```
for v in qs:
    cls.append([-v, o])
cls.append([-o] + qs)
``` -/
def defLine (o : Nat) (qs : List Nat) : List Clause :=
  (qs.map fun (v : Nat) => [-(v : Int), (o : Int)]) ++ [(-(o : Int)) :: qs.map fun (v : Nat) => (v : Int)]

/-- DEF: `for (kind, i), qs in fam.items(): ...` -/
def defCls (n : Nat) : List Clause := (fam n).flatMap fun p => defLine p.1 p.2

/-- DOM:
```
for x in range(n):
    for y in range(n):
        cls.append([self.oR[y], self.oC[x], self.oT[y - x], self.oS[x + y]])
``` -/
def domCls (n : Nat) : List Clause :=
  (List.range n).flatMap fun x => (List.range n).map fun y =>
    [(oRv n y : Int), (oCv n x : Int), (oTv n (tIdx n x y) : Int), (oSv n (x + y) : Int)]

/-- `self.oR` as a list of literals. -/
def oRlits (n : Nat) : List Int := (List.range n).map fun y => (oRv n y : Int)

/-- `self.oC` as a list of literals. -/
def oClits (n : Nat) : List Int := (List.range n).map fun x => (oCv n x : Int)

/-- `list(self.oT.values())`. -/
def oTlits (n : Nat) : List Int := (List.range (2 * n - 1)).map fun i => (oTv n i : Int)

/-- `list(self.oS.values())`. -/
def oSlits (n : Nat) : List Int := (List.range (2 * n - 1)).map fun s => (oSv n s : Int)

/-- The variable counter before `exactly(self.oR, k - dR, ...)`. -/
def nvCardR (n : Nat) : Nat := baseVars n

/-- The variable counter before `exactly(self.oC, k - dC, ...)`. -/
def nvCardC (n k dR : Nat) : Nat := nvCardR n + exactlyNew n ((k : Int) - dR)

/-- The variable counter before `exactly(list(self.oT.values()), k - dT, ...)`. -/
def nvCardT (n k dR dC : Nat) : Nat := nvCardC n k dR + exactlyNew n ((k : Int) - dC)

/-- The variable counter before `exactly(list(self.oS.values()), k - dS, ...)`. -/
def nvCardS (n k dR dC dT : Nat) : Nat :=
  nvCardT n k dR dC + exactlyNew (2 * n - 1) ((k : Int) - dT)

/-- The variable counter after the four cardinality constraints CARD. -/
def nvCardEnd (n k dR dC dT dS : Nat) : Nat :=
  nvCardS n k dR dC dT + exactlyNew (2 * n - 1) ((k : Int) - dS)

/-- CARD:
```
exactly(self.oR, k - dR, self.new, cls)
exactly(self.oC, k - dC, self.new, cls)
exactly(list(self.oT.values()), k - dT, self.new, cls)
exactly(list(self.oS.values()), k - dS, self.new, cls)
``` -/
def cardCls (n k dR dC dT dS : Nat) : List Clause :=
  exactlyCls (oRlits n) ((k : Int) - dR) (nvCardR n) ++
    (exactlyCls (oClits n) ((k : Int) - dC) (nvCardC n k dR) ++
      (exactlyCls (oTlits n) ((k : Int) - dT) (nvCardT n k dR dC) ++
        exactlyCls (oSlits n) ((k : Int) - dS) (nvCardS n k dR dC dT)))

/-- AMO for one line with queen variables `qs`:
```
for u in range(len(qs)):
    for v in range(u + 1, len(qs)):
        cls.append([-qs[u], -qs[v]])
``` -/
def amoLine : List Nat → List Clause
  | [] => []
  | q :: qs => (qs.map fun (r : Nat) => [-(q : Int), -(r : Int)]) ++ amoLine qs

/-- AMO for all lines of one kind. -/
def amoFam (f : List (Nat × List Nat)) : List Clause := f.flatMap fun p => amoLine p.2

/-- AMO:
```
zero = [kind for kind, dd in zip('RCTS', dv) if dd == 0]
if use_amo:
    for (kind, i), qs in fam.items():
        if kind in zero:
            ...
``` -/
def amoCls (n dR dC dT dS : Nat) : List Clause :=
  (if dR = 0 then amoFam (famR n) else []) ++
    ((if dC = 0 then amoFam (famC n) else []) ++
      ((if dT = 0 then amoFam (famT n) else []) ++
        (if dS = 0 then amoFam (famS n) else [])))

/-- `[q[x][y] for x in range(n) for y in range(n)]`. -/
def qLits (n : Nat) : List Int :=
  (List.range n).flatMap fun x => (List.range n).map fun y => (qv n x y : Int)

/-- `zero` is empty: no deficit is `0`. -/
def NoZero (dR dC dT dS : Nat) : Prop := dR ≠ 0 ∧ dC ≠ 0 ∧ dT ≠ 0 ∧ dS ≠ 0

instance (dR dC dT dS : Nat) : Decidable (NoZero dR dC dT dS) := by unfold NoZero; infer_instance

/-- "exactly `k` queens", emitted only when no deficit is `0`:
```
if not (use_amo and zero):
    exactly([q[x][y] for x in range(n) for y in range(n)], k, self.new, cls)
``` -/
def queensCls (n k dR dC dT dS : Nat) : List Clause :=
  if NoZero dR dC dT dS then exactlyCls (qLits n) (k : Int) (nvCardEnd n k dR dC dT dS) else []

/-- `Base.nv`: the number of variables of the base formula. -/
def baseNv (n k dR dC dT dS : Nat) : Nat :=
  nvCardEnd n k dR dC dT dS + (if NoZero dR dC dT dS then exactlyNew (n * n) (k : Int) else 0)

/-- `Base.cls` as a list: DEF, DOM, CARD, AMO, (exactly `k` queens). -/
def baseClauses (n k dR dC dT dS : Nat) : List Clause :=
  defCls n ++ (domCls n ++ (cardCls n k dR dC dT dS ++ (amoCls n dR dC dT dS ++ queensCls n k dR dC dT dS)))

/-- `enc.Base`: the part of the formula that depends only on `(n, k, deficits)`. -/
structure Base where
  n : Nat
  k : Nat
  dR : Nat
  dC : Nat
  dT : Nat
  dS : Nat
  /-- number of variables -/
  nv : Nat
  /-- the clauses, in the order of `enc.Base.cls` -/
  cls : Array Clause

/-- `enc.Base(n, k, (dR, dC, dT, dS))` (with `use_amo=True`). -/
def mkBase (n k dR dC dT dS : Nat) : Base :=
  { n := n, k := k, dR := dR, dC := dC, dT := dT, dS := dS
    nv := baseNv n k dR dC dT dS
    cls := (baseClauses n k dR dC dT dS).toArray }

/-! ### The frame-dependent clauses (`case_extra`)

The frame is `a = ml`, `b = n-1-mr` (extreme empty columns), `c = mb`, `d = n-1-mt` (extreme empty
rows); `w = b - a`, `h = d - c`.  The Python function asserts `w ≥ 1` and `h ≥ 1`; the Lean functions
are total, and agree with the Python ones whenever these assertions hold
(`ml + mr + 2 ≤ n`, `mb + mt + 2 ≤ n`). -/

/-- FRAME:
```
for x in range(n):
    if x < a or x > b:
        cls.append([oC[x]])
for y in range(n):
    if y < c or y > d:
        cls.append([oR[y]])
cls += [[-oC[a]], [-oC[b]], [-oR[c]], [-oR[d]]]
``` -/
def frameCls (n a b c d : Nat) : List Clause :=
  (((List.range n).filter fun x => decide (x < a ∨ b < x)).map fun x => [(oCv n x : Int)]) ++
    ((((List.range n).filter fun y => decide (y < c ∨ d < y)).map fun y => [(oRv n y : Int)]) ++
      [[-(oCv n a : Int)], [-(oCv n b : Int)], [-(oRv n c : Int)], [-(oRv n d : Int)]])

/-- `nonneedy_lit(sq)`: the variable that is true iff the border square `sq` is not needy; `none`
for the corners.
```
x, y = sq
colE = x in (a, b); rowE = y in (c, d)
if colE and rowE:
    return None
return oR[y] if colE else oC[x]
``` -/
def nonneedy (n a b c d : Nat) (sq : Nat × Nat) : Option Nat :=
  if (sq.1 = a ∨ sq.1 = b) ∧ (sq.2 = c ∨ sq.2 = d) then none
  else if sq.1 = a ∨ sq.1 = b then some (oRv n sq.2)
  else some (oCv n sq.1)

/-- The squares of the set `sqs` on the difference diagonal `t = i - (n-1)`, by increasing `x`:
```
on = [(x, x + L[1]) for x in range(a, b + 1) if (x, x + L[1]) in sqs]
``` -/
def onT (n a b : Nat) (sqs : List (Nat × Nat)) (i : Nat) : List (Nat × Nat) :=
  ((List.range' a (b + 1 - a)).filter fun x =>
      decide (n - 1 ≤ x + i ∧ (x, x + i - (n - 1)) ∈ sqs)).map
    fun x => (x, x + i - (n - 1))

/-- The squares of the set `sqs` on the sum diagonal `s`, by increasing `x`:
```
on = [(x, L[1] - x) for x in range(a, b + 1) if (x, L[1] - x) in sqs]
``` -/
def onS (a b : Nat) (sqs : List (Nat × Nat)) (s : Nat) : List (Nat × Nat) :=
  ((List.range' a (b + 1 - a)).filter fun x => decide (x ≤ s ∧ (x, s - x) ∈ sqs)).map
    fun x => (x, s - x)

/-- What `waste` needs to know about one diagonal `L`: its variable `lv(L)`, the number `len(on)` of
squares of the set on it, and the `nonneedy_lit`s (those that are not `None`) of these squares, in the
order of `on`. -/
structure WLine where
  lv : Nat
  onLen : Nat
  nls : List Nat

/-- The `WLine` of a diagonal with variable `lv` and list `on`. -/
def mkWLine (n a b c d : Nat) (lv : Nat) (on : List (Nat × Nat)) : WLine :=
  { lv := lv, onLen := on.length, nls := on.filterMap (nonneedy n a b c d) }

/-- `lines_ = [('T', t) for t in oT] + [('S', s) for s in oS]` with the data of each line for the set
of squares `sqs`. -/
def wasteLineList (n a b c d : Nat) (sqs : List (Nat × Nat)) : List WLine :=
  ((List.range (2 * n - 1)).map fun i => mkWLine n a b c d (oTv n i) (onT n a b sqs i)) ++
    ((List.range (2 * n - 1)).map fun s => mkWLine n a b c d (oSv n s) (onS a b sqs s))

/-- The number of copies of `lv(L)` that `waste` appends to `lits` for a line with `len(on) = len`:
```
if weight_full:
    lits += [lv(L)] * (2 - len(on))
elif not on:
    lits.append(lv(L))
``` -/
def lineCopies (full : Bool) (len : Nat) : Nat :=
  if full then 2 - len else if len = 0 then 1 else 0

/-- The clauses `[-lv(L), -nl, e]` of one line; the `j`-th of them (`j = 0, 1`) defines the fresh
variable `e = nv + j + 1`:
```
for sq in on:
    nl = nonneedy_lit(sq)
    if nl is not None:
        e = new(); cls.append([-lv(L), -nl, e]); lits.append(e)
``` -/
def wasteLineCls (L : WLine) (nv : Nat) : List Clause :=
  L.nls.zipIdx.map fun p => [-(L.lv : Int), -(p.1 : Int), ((nv + p.2 + 1 : Nat) : Int)]

/-- The literals that one line contributes to `lits`: the copies of `lv(L)`, then its variables `e`. -/
def wasteLineLits (full : Bool) (L : WLine) (nv : Nat) : List Int :=
  List.replicate (lineCopies full L.onLen) (L.lv : Int) ++
    (List.range L.nls.length).map fun j => ((nv + j + 1 : Nat) : Int)

/-- The output of `waste` (or of a part of it), started at variable counter `nv`: the clauses appended
to `cls`, the literals appended to `lits`, and the number of fresh variables allocated (these are
`nv + 1, ..., nv + new`). -/
structure Waste where
  cls : List Clause
  lits : List Int
  new : Nat

/-- One step of the loop `for L in lines_:` of `waste`: the output of the line `L`, processed at counter
`nv`, followed by the output `r` of the remaining lines (which start at counter `nv + L.nls.length`). -/
def wasteStep (full : Bool) (L : WLine) (nv : Nat) (r : Waste) : Waste :=
  { cls := wasteLineCls L nv ++ r.cls
    lits := wasteLineLits full L nv ++ r.lits
    new := L.nls.length + r.new }

/-- The loop `for L in lines_:` of `waste`, with the variable counter passed along explicitly: the line
`L` is processed at counter `nv` and allocates `L.nls.length` variables. -/
def wasteLines (full : Bool) : List WLine → Nat → Waste
  | [], _ => { cls := [], lits := [], new := 0 }
  | L :: Ls, nv => wasteStep full L nv (wasteLines full Ls (nv + L.nls.length))

/-- The second loop of `waste`; the `j`-th square defines the fresh variable `f = nv + j + 1`:
```
for (x, y) in squares:
    nl = nonneedy_lit((x, y))
    f = new()
    cls.append([-oT[y - x], -oS[x + y], f] + ([nl] if nl is not None else []))
    lits.append(f)
``` -/
def wasteSqCls (n a b c d : Nat) (sqs : List (Nat × Nat)) (nv : Nat) : List Clause :=
  sqs.zipIdx.map fun p =>
    [-(oTv n (tIdx n p.1.1 p.1.2) : Int), -(oSv n (p.1.1 + p.1.2) : Int), ((nv + p.2 + 1 : Nat) : Int)] ++
      (nonneedy n a b c d p.1).toList.map fun (v : Nat) => (v : Int)

/-- `waste(squares, weight_full)` called when the variable counter is `nv`: "waste literals for the
incidence count between occupied diagonals and the given border squares".  First the loop over the
lines (variables `e`), then the loop over the squares (variables `f`). -/
def waste (n a b c d : Nat) (full : Bool) (sqs : List (Nat × Nat)) (nv : Nat) : Waste :=
  let W := wasteLines full (wasteLineList n a b c d sqs) nv
  { cls := W.cls ++ wasteSqCls n a b c d sqs (nv + W.new)
    lits := W.lits ++ (List.range sqs.length).map fun j => ((nv + W.new + j + 1 : Nat) : Int)
    new := W.new + sqs.length }

/-- A clause group started at variable counter `nv`: the clauses it appends and the number of fresh
variables it allocates (`nv + 1, ..., nv + new`). -/
structure Group where
  cls : List Clause
  new : Nat

/-- `atmost(waste(...) + extra, bound, new, cls)` where `W` is the result of `waste(...)` called at
counter `nv`: the clauses of `waste`, then those of `atmost` (whose counter starts at `nv + W.new`). -/
def wasteAtmost (W : Waste) (extra : List Int) (bound : Int) (nv : Nat) : Group :=
  { cls := W.cls ++ atmostCls (W.lits ++ extra) bound (nv + W.new)
    new := W.new + atmostNew (W.lits ++ extra).length bound }

/-- The border of the box:
```
Bd = [(x, y) for x in range(a, b + 1) for y in range(c, d + 1) if x in (a, b) or y in (c, d)]
``` -/
def borderSqs (a b c d : Nat) : List (Nat × Nat) :=
  (List.range' a (b + 1 - a)).flatMap fun x =>
    ((List.range' c (d + 1 - c)).filter fun y => decide (x = a ∨ x = b ∨ y = c ∨ y = d)).map
      fun y => (x, y)

/-- The vertical sides: `VS = [(x, y) for x in (a, b) for y in range(c, d + 1)]`. -/
def vsideSqs (a b c d : Nat) : List (Nat × Nat) :=
  [a, b].flatMap fun x => (List.range' c (d + 1 - c)).map fun y => (x, y)

/-- The horizontal sides: `HS = [(x, y) for y in (c, d) for x in range(a, b + 1)]`. -/
def hsideSqs (a b c d : Nat) : List (Nat × Nat) :=
  [c, d].flatMap fun y => (List.range' a (b + 1 - a)).map fun x => (x, y)

/-- The bound of (F): `8 * k - 4 * n + 4 - 2 * (dR + dC + dT + dS)`. -/
def boundF (n k dR dC dT dS : Nat) : Int :=
  8 * (k : Int) - 4 * (n : Int) + 4 - 2 * ((dR : Int) + (dC : Int) + (dT : Int) + (dS : Int))

/-- The bound `g` of (V): `4 * k - 2 * n - dT - dS - 2 * dR`. -/
def boundV (n k dR dT dS : Nat) : Int :=
  4 * (k : Int) - 2 * (n : Int) - (dT : Int) - (dS : Int) - 2 * (dR : Int)

/-- The bound `g` of (H): `4 * k - 2 * n - dT - dS - 2 * dC`. -/
def boundH (n k dC dT dS : Nat) : Int :=
  4 * (k : Int) - 2 * (n : Int) - (dT : Int) - (dS : Int) - 2 * (dC : Int)

/-- `[-u0, -v0]` with `u0, v0 = oT[c - a], oS[a + d]` (the two diagonals of a square box). -/
def sqExtra (n a c d : Nat) : List Int := [-(oTv n (tIdx n a c) : Int), -(oSv n (a + d) : Int)]

/-- (F), started at counter `nv`:
```
Bd = ...
atmost(waste(Bd, True), 8 * k - 4 * n + 4 - 2 * (dR + dC + dT + dS), new, cls)
``` -/
def groupF (n k dR dC dT dS a b c d nv : Nat) : Group :=
  wasteAtmost (waste n a b c d true (borderSqs a b c d) nv) [] (boundF n k dR dC dT dS) nv

/-- (V), started at counter `nv` (`w = b - a`, `h = d - c`):
```
if use_V and w >= h:
    VS = [(x, y) for x in (a, b) for y in range(c, d + 1)]
    g = 4 * k - 2 * n - dT - dS - 2 * dR
    if w == h:
        atmost(waste(VS, False) + [-u0, -v0], g + 2, new, cls)
    else:
        atmost(waste(VS, False), g, new, cls)
``` -/
def groupV (n k dR dT dS a b c d nv : Nat) : Group :=
  if d - c ≤ b - a then
    if b - a = d - c then
      wasteAtmost (waste n a b c d false (vsideSqs a b c d) nv) (sqExtra n a c d)
        (boundV n k dR dT dS + 2) nv
    else
      wasteAtmost (waste n a b c d false (vsideSqs a b c d) nv) [] (boundV n k dR dT dS) nv
  else { cls := [], new := 0 }

/-- (H), started at counter `nv`:
```
if use_H and h >= w:
    HS = [(x, y) for y in (c, d) for x in range(a, b + 1)]
    g = 4 * k - 2 * n - dT - dS - 2 * dC
    if w == h:
        atmost(waste(HS, False) + [-u0, -v0], g + 2, new, cls)
    else:
        atmost(waste(HS, False), g, new, cls)
``` -/
def groupH (n k dC dT dS a b c d nv : Nat) : Group :=
  if b - a ≤ d - c then
    if b - a = d - c then
      wasteAtmost (waste n a b c d false (hsideSqs a b c d) nv) (sqExtra n a c d)
        (boundH n k dC dT dS + 2) nv
    else
      wasteAtmost (waste n a b c d false (hsideSqs a b c d) nv) [] (boundH n k dC dT dS) nv
  else { cls := [], new := 0 }

/-- All clauses of `case_extra` for the frame `(a, b, c, d)`, started at counter `nv` (`= base.nv`):
FRAME, then (F), (V), (H), each group starting where the previous one stopped. -/
def extraGroup (n k dR dC dT dS a b c d nv : Nat) : Group :=
  let F := groupF n k dR dC dT dS a b c d nv
  let V := groupV n k dR dT dS a b c d (nv + F.new)
  let H := groupH n k dC dT dS a b c d (nv + F.new + V.new)
  { cls := frameCls n a b c d ++ (F.cls ++ (V.cls ++ H.cls))
    new := F.new + V.new + H.new }

/-- `enc.case_extra(base, (ml, mr, mb, mt, dR, dC, dT, dS))` with the default flags: "frame-dependent
clauses; returns (clauses, number of variables in total)".
```
a, b, c, d = ml, n - 1 - mr, mb, n - 1 - mt
``` -/
def caseExtra (B : Base) (ml mr mb mt : Nat) : Array Clause × Nat :=
  let G := extraGroup B.n B.k B.dR B.dC B.dT B.dS ml (B.n - 1 - mr) mb (B.n - 1 - mt) B.nv
  (G.cls.toArray, B.nv + G.new)

/-! ### DIMACS text -/

/-- One clause in DIMACS: `' '.join(map(str, c)) + ' 0\n'` (the empty clause is `" 0\n"`). -/
def clauseStr (c : Clause) : String := " ".intercalate (c.map fun l => toString l) ++ " 0\n"

/-- `''.join(' '.join(map(str, c)) + ' 0\n' for c in cls)`. -/
def clausesStr (cls : List Clause) : String := String.join (cls.map clauseStr)

/-- `enc.dimacs` with `base.text` and `len(base.cls)` given (so that the text of a base formula can be
shared between its cases):
```
'p cnf %d %d\n' % (nv, len(base.cls) + len(extra)) + base.text
  + ''.join(' '.join(map(str, c)) + ' 0\n' for c in extra)
``` -/
def dimacsOfText (baseText : String) (baseSize : Nat) (extra : Array Clause) (nv : Nat) : String :=
  "p cnf " ++ toString nv ++ " " ++ toString (baseSize + extra.size) ++ "\n" ++ baseText ++
    clausesStr extra.toList

/-- `Base.text`. -/
def Base.text (B : Base) : String := clausesStr B.cls.toList

/-- `enc.dimacs(base, extra, nv)`. -/
def dimacs (B : Base) (extra : Array Clause) (nv : Nat) : String :=
  dimacsOfText B.text B.cls.size extra nv

/-! ### Conversion to `Std.Sat.CNF Nat`

`Std.Sat.CNF.Clause.ofLiterals` folds `Clause.add` over the list, which pushes each (atom, polarity)
pair onto the two arrays of the clause: the literals are kept verbatim and in order
(`Std.Sat.CNF.Clause.literals_ofLiterals : (ofLiterals l).literals = l`).  Nothing is normalised: a
repeated literal would be stored twice and a tautology `v ∨ ¬v` would be stored as it is (neither occurs
in the clauses of `enc.py`).  The LRAT checker `Std.Tactic.BVDecide.LRAT.check` refers to the clause at
position `i` of `cnf.clauses` by the identifier `i + 1`, as DIMACS/LRAT do. -/

/-- The DIMACS literal `v > 0` is the atom `v - 1` with positive polarity, `v < 0` the atom `|v| - 1`
with negative polarity (the convention of `Std.Sat.CNF.dimacs` and of the LRAT checker).  The integer
`0` is not a literal; it would be mapped to the negative literal of atom `0`. -/
def litToStd (l : Int) : Std.Sat.Literal Nat := (l.natAbs - 1, decide (0 < l))

/-- A clause as a `Std.Sat.CNF.Clause Nat`, literal by literal, in the same order. -/
def clauseToStd (c : Clause) : Std.Sat.CNF.Clause Nat :=
  Std.Sat.CNF.Clause.ofLiterals (c.map litToStd)

/-- A clause array as a `Std.Sat.CNF Nat`: clause by clause, in the same order; nothing is dropped,
deduplicated or reordered. -/
def toCNF (cls : Array Clause) : Std.Sat.CNF Nat := { clauses := cls.map clauseToStd }

/-- The formula of the case `(ml, mr, mb, mt)` with the deficits of `B`: the clauses of
`enc.dimacs(B, *enc.case_extra(B, case))`, in the order of the file. -/
def caseCNF (B : Base) (ml mr mb mt : Nat) : Std.Sat.CNF Nat :=
  toCNF (B.cls ++ (caseExtra B ml mr mb mt).1)

end QueenDomSat
