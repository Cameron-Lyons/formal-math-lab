/-
LRAT text (as written by `drat-trim -L`)  ->  gapless `IntAction`s for `Std.Tactic.BVDecide.LRAT.check`.

Everything in this file is UNTRUSTED: whatever it produces is checked afterwards by Std's verified
checker, so a bug here can only turn a valid proof into a rejected one, never the converse.

Why a normalisation is needed.  The Std checker keeps the clause database in an array and
`State.add` *pushes* each new clause at the end, ignoring the id written in the proof; clause `i` is
looked up at position `i - 1`.  So the checker implicitly numbers the clauses 1, 2, 3, ... in the
order "original clauses in CNF order, then the lemmas in proof order".  drat-trim numbers the lemmas
by their position in the *untrimmed* DRAT proof, so its ids have gaps.  The normalisation is:

  * a lemma line (in file order) gets the new id `numOrig + (number of lemma lines so far)`;
  * ids `<= numOrig` (original clauses) are kept;
  * every hint id and every deleted id is replaced by the new id of the lemma it names
    (a hint naming an id that no lemma line had is an error; such a deleted id is skipped);
  * deletion lines are kept (default) or dropped; the id in front of `d` is ignored;
  * blank lines are skipped and not counted (line numbers in messages count non-blank lines);
  * a line consisting of the single token `0` is skipped (drat-trim writes one when the last proof
    step before the empty clause is an addition);
  * everything after the first empty-clause line is ignored (the checker stops there);
  * if the input ends without an empty-clause line and the CNF itself contains an empty clause
    (id `j`), the step "empty clause, hint `j`" is appended.  drat-trim answers such a formula with
    `c trivial UNSAT` and writes an LRAT file of 0 bytes, but `LRAT.check` wants an `addEmpty` step.

The parser is a small state machine over raw bytes that can be fed the file in chunks of any size
(the proofs are hundreds of MB, and can be piped in from `zstd -dc`).
-/
import Std.Tactic.BVDecide.LRAT.Actions

namespace QueenDomCheck
open Std.Sat
open Std.Tactic.BVDecide.LRAT (IntAction)

/-- Counters describing a proof.  Informational only. -/
structure Stats where
  /-- non-empty lines read -/
  lines : Nat := 0
  /-- addition lines (including the empty clause) -/
  lemmas : Nat := 0
  /-- lemmas with at least one negative hint, i.e. RAT steps -/
  ratLemmas : Nat := 0
  /-- non-empty lemmas without any hint -/
  noHintLemmas : Nat := 0
  /-- total number of hint ids (RUP and RAT) -/
  hints : Nat := 0
  /-- total number of literals in lemmas -/
  lemmaLits : Nat := 0
  /-- largest variable occurring in a lemma -/
  maxVar : Nat := 0
  maxLemmaLen : Nat := 0
  maxHints : Nat := 0
  delLines : Nat := 0
  delIds : Nat := 0
  /-- deleted ids that are neither an original clause nor a lemma of the file (skipped) -/
  delIdsUnknown : Nat := 0
  /-- lines consisting of a single `0` (skipped) -/
  strayZeroLines : Nat := 0
  /-- file id of the first / last lemma -/
  firstId : Nat := 0
  lastId : Nat := 0
  /-- lemma lines whose file id is not larger than the previous one -/
  nonMonotoneIds : Nat := 0
  /-- lines after the empty clause (ignored) -/
  linesAfterEmpty : Nat := 0
  /-- 1 if the final step was synthesised from an empty clause of the CNF (see `Parser.finish`) -/
  synthesisedEmpty : Nat := 0
  deriving Inhabited

/-- The id renumbering and the output buffer. -/
structure Normaliser where
  /-- number of clauses of the CNF: ids `1..numOrig` are the original clauses -/
  numOrig : Nat
  /-- keep deletion steps? -/
  keepDel : Bool := true
  /-- id of an empty clause of the CNF, 0 if it has none -/
  emptyOrig : Nat := 0
  /-- `idMap[o - numOrig - 1]` is the new id of the lemma whose file id is `o` (0: no such lemma).
  drat-trim's ids are the positions in the untrimmed DRAT proof, so this dense table has one slot
  (8 bytes) per lemma of the DRAT proof; see `maxIdSpan`. -/
  idMap : Array Nat := #[]
  /-- the id the next lemma will get -/
  nextId : Nat
  /-- normalised steps produced so far and not yet taken by the caller -/
  out : Array IntAction := #[]
  /-- the empty clause has been read -/
  done : Bool := false
  err : Option String := none
  stats : Stats := {}
  deriving Inhabited

namespace Normaliser

/-- Largest accepted `file id - numOrig`: bounds the dense id table (8 bytes per slot, so 1 GB). -/
def maxIdSpan : Nat := 2 ^ 27

def new (numOrig : Nat) (keepDel : Bool) (emptyOrig : Nat := 0) : Normaliser :=
  { numOrig, keepDel, emptyOrig, nextId := numOrig + 1 }

/-- an error in the line that has just been completed (it is already counted in `stats.lines`) -/
def fail (n : Normaliser) (msg : String) : Normaliser :=
  { n with err := some s!"LRAT line {n.stats.lines}: {msg}" }

/-- an error found by the lexer in the line being read (not yet counted) -/
def failLex (n : Normaliser) (msg : String) : Normaliser :=
  { n with err := some s!"LRAT line {n.stats.lines + 1}: {msg}" }

/-- new id of the clause with file id `old`; 0 if unknown -/
@[inline] def lookup (n : Normaliser) (old : Nat) : Nat :=
  if old ≤ n.numOrig then old else n.idMap.getD (old - n.numOrig - 1) 0

/-- record that the lemma with file id `old` (`> numOrig`, not yet used) gets the id `n.nextId` -/
private def bind (n : Normaliser) (old : Nat) : Normaliser :=
  let idx := old - n.numOrig - 1
  let new := n.nextId
  if idx < n.idMap.size then
    { n with idMap := n.idMap.set! idx new, nextId := new + 1 }
  else
    let rec pad (m : Array Nat) (k : Nat) : Array Nat :=
      match k with
      | 0 => m
      | k + 1 => pad (m.push 0) k
    { n with idMap := (pad n.idMap (idx - n.idMap.size)).push new, nextId := new + 1 }

/--
Translate the positive ids `toks[j..e)` and append them to `acc`.  Stops early at the first token that
is not a known positive id and returns its index (`e` if all were translated).  This is the hot loop
of the normaliser (a proof has about 100 hints per lemma), hence the explicit recursion.
-/
private partial def mapIds (n : Normaliser) (toks : Array Int) (j e : Nat) (acc : Array Nat) :
    Array Nat × Nat :=
  if j < e then
    let t := toks[j]!
    if t ≤ 0 then (acc, j)
    else
      let new := n.lookup t.toNat
      if new == 0 then (acc, j) else mapIds n toks (j + 1) e (acc.push new)
  else (acc, j)

/-- copy the literals `toks[j..e)` to `acc` and return them with the largest variable seen -/
private partial def copyLits (toks : Array Int) (j e : Nat) (acc : Array Int) (maxVar : Nat) :
    Array Int × Nat :=
  if j < e then
    let l := toks[j]!
    copyLits toks (j + 1) e (acc.push l) (max maxVar l.natAbs)
  else (acc, maxVar)

/-- `id d id* 0` -/
private def delLine (n : Normaliser) (toks : Array Int) : Normaliser := Id.run do
  let sz := toks.size
  if sz < 2 || toks[sz - 1]! != 0 then return n.fail "deletion line does not end with 0"
  let mut ids : Array Nat := Array.emptyWithCapacity (if n.keepDel then sz - 2 else 0)
  let mut unknown := 0
  for j in [1:sz - 1] do
    let t := toks[j]!
    if t ≤ 0 then return n.fail s!"bad id {t} in deletion line"
    let new := n.lookup t.toNat
    if new == 0 then unknown := unknown + 1
    else if n.keepDel then ids := ids.push new
  let st := n.stats
  let st := { st with delLines := st.delLines + 1, delIds := st.delIds + (sz - 2),
                      delIdsUnknown := st.delIdsUnknown + unknown }
  if n.keepDel && ids.size > 0 then
    return { n with out := n.out.push (.del ids), stats := st }
  else
    return { n with stats := st }

/-- `id lit* 0 hint* 0`, where a negative hint `-c` starts the RAT candidate `c` -/
private def addLine (n : Normaliser) (toks : Array Int) : Normaliser := Id.run do
  let sz := toks.size
  let old := toks[0]!.toNat
  if toks[0]! ≤ 0 then return n.fail "clause id must be positive"
  if old ≤ n.numOrig then
    return n.fail s!"lemma id {old} is the id of an original clause (the CNF has {n.numOrig})"
  if old - n.numOrig > maxIdSpan then
    return n.fail s!"lemma id {old} is too large for the dense id table (limit numOrig + {maxIdSpan})"
  if n.lookup old != 0 then return n.fail s!"lemma id {old} is used twice"
  -- the clause is toks[1..z)
  let mut z := 1
  while z < sz && toks[z]! != 0 do z := z + 1
  if z + 1 ≥ sz || toks[sz - 1]! != 0 then return n.fail "addition line: expected `lits 0 hints 0`"
  let (clause, maxVar) := copyLits toks 1 z (Array.emptyWithCapacity (z - 1)) n.stats.maxVar
  -- the hints are toks[z+1 .. sz-1)
  let numHints := sz - 2 - z
  let e := sz - 1
  -- the RUP hints: the positive ids up to the first negative one
  let (rup, j) := mapIds n toks (z + 1) e (Array.emptyWithCapacity numHints)
  -- the RAT part (absent in all our proofs): groups `-candidate hint*`
  let mut rat : Array (Nat × Array Nat) := #[]
  let mut j := j
  while j < e do
    let t := toks[j]!
    if t == 0 then return n.fail "0 inside the hints"
    let cand := n.lookup t.natAbs
    if cand == 0 then return n.fail s!"hint {t} names a clause that is not in the proof"
    -- `mapIds` only stops at a token that is not a known positive id, so `t` is negative here
    if t > 0 then return n.fail s!"internal error at hint {t}"
    let (candHints, j') := mapIds n toks (j + 1) e #[]
    rat := rat.push (cand, candHints)
    j := j'
  let new := n.nextId
  let st := n.stats
  let st := { st with
    lemmas := st.lemmas + 1
    ratLemmas := st.ratLemmas + (if rat.isEmpty then 0 else 1)
    noHintLemmas := st.noHintLemmas + (if numHints == 0 && !clause.isEmpty then 1 else 0)
    hints := st.hints + numHints
    lemmaLits := st.lemmaLits + clause.size
    maxVar := maxVar
    maxLemmaLen := max st.maxLemmaLen clause.size
    maxHints := max st.maxHints numHints
    firstId := if st.lemmas == 0 then old else st.firstId
    lastId := old
    nonMonotoneIds := st.nonMonotoneIds + (if st.lemmas != 0 && old ≤ st.lastId then 1 else 0) }
  let n := { n with stats := st }
  -- the same case distinction as Std's own text parser (`LRAT.Parser.Text.parseRat`)
  if clause.isEmpty then
    if !rat.isEmpty then return n.fail "RAT hints on the empty clause"
    let n := n.bind old
    return { n with out := n.out.push (.addEmpty new rup), done := true }
  let pivot : Literal Nat := (clause[0]!.natAbs, clause[0]! > 0)
  let step : IntAction :=
    if rat.isEmpty && !rup.isEmpty then .addRup new clause rup
    else .addRat new clause pivot rup rat
  let n := n.bind old
  return { n with out := n.out.push step }

/-- Process one complete line: `toks` are its numbers, `isDel` says that a `d` followed the first. -/
def endLine (n : Normaliser) (toks : Array Int) (isDel : Bool) : Normaliser :=
  if toks.isEmpty && !isDel then n                      -- blank line
  else
    let n := { n with stats.lines := n.stats.lines + 1 }
    if n.done then { n with stats.linesAfterEmpty := n.stats.linesAfterEmpty + 1 }
    else if isDel then n.delLine toks
    else if toks.size == 1 && toks[0]! == 0 then
      { n with stats.strayZeroLines := n.stats.strayZeroLines + 1 }
    else n.addLine toks

end Normaliser

/-- The normaliser together with the lexer registers that survive a chunk boundary. -/
structure Parser where
  norm : Normaliser
  /-- numbers of the current, still incomplete line -/
  toks : Array Int := #[]
  /-- value of the number being read -/
  cur : Nat := 0
  /-- at least one digit of the current number has been read -/
  inNum : Bool := false
  /-- a `-` has been read for the current number -/
  neg : Bool := false
  /-- the current line is a deletion line -/
  isDel : Bool := false
  deriving Inhabited

namespace Parser

/-- `emptyOrig`: id of an empty clause of the CNF (0 if it has none), see `finish`. -/
def new (numOrig : Nat) (keepDel : Bool := true) (emptyOrig : Nat := 0) : Parser :=
  { norm := .new numOrig keepDel emptyOrig }

@[inline] private def mkInt (cur : Nat) (neg : Bool) : Int :=
  if neg then -(Int.ofNat cur) else Int.ofNat cur

/--
The lexer loop over one chunk.  The registers are passed as separate arguments so that the compiled
loop keeps them in machine registers; they are packed into a `Parser` only at the end of the chunk.
-/
private partial def lexLoop (buf : ByteArray) (i : Nat) (cur : Nat) (inNum neg isDel : Bool)
    (toks : Array Int) (n : Normaliser) : Parser :=
  if h : i < buf.size then
    let c := buf[i]
    if 48 ≤ c && c ≤ 57 then                                  -- digit
      lexLoop buf (i + 1) (cur * 10 + (c - 48).toNat) true neg isDel toks n
    else if c == 32 || c == 9 || c == 13 then                 -- separator
      if inNum then lexLoop buf (i + 1) 0 false false isDel (toks.push (mkInt cur neg)) n
      else if neg then { norm := n.failLex "`-` without digits" }
      else lexLoop buf (i + 1) 0 false false isDel toks n
    else if c == 10 then                                      -- end of line
      if neg && !inNum then { norm := n.failLex "`-` without digits" }
      else
        let toks := if inNum then toks.push (mkInt cur neg) else toks
        let n := n.endLine toks isDel
        if n.err.isSome then { norm := n }
        else lexLoop buf (i + 1) 0 false false false (toks.shrink 0) n
    else if c == 45 then                                      -- '-'
      if inNum || neg then { norm := n.failLex "misplaced `-`" }
      else lexLoop buf (i + 1) 0 false true isDel toks n
    else if c == 100 then                                     -- 'd'
      if inNum || neg || isDel || toks.size != 1 then { norm := n.failLex "misplaced `d`" }
      else lexLoop buf (i + 1) 0 false false true toks n
    else { norm := n.failLex s!"unexpected byte {c}" }
  else
    { norm := n, toks, cur, inNum, neg, isDel }

/-- Feed the next chunk of the file.  On error `p.norm.err` is set (and stays set). -/
def feed (p : Parser) (buf : ByteArray) : Parser :=
  if p.norm.err.isSome then p
  else lexLoop buf 0 p.cur p.inNum p.neg p.isDel p.toks p.norm

/--
End of input: process a last line that is not terminated by a newline; then, if the proof has no
empty-clause step but the CNF contains an empty clause, append the step that derives the empty
clause from it (drat-trim writes an empty LRAT file for such a formula).
-/
def finish (p : Parser) : Parser :=
  if p.norm.err.isSome then p
  else
    let p := if p.inNum || p.neg || p.isDel || !p.toks.isEmpty then p.feed (ByteArray.empty.push 10) else p
    let n := p.norm
    if n.err.isSome || n.done || n.emptyOrig == 0 then p
    else
      { p with norm := { n with out := n.out.push (.addEmpty n.nextId #[n.emptyOrig]), done := true,
                                stats.synthesisedEmpty := 1 } }

/-- Take the steps produced so far out of the parser (used for streaming). -/
def drain (p : Parser) : Array IntAction × Parser :=
  let out := p.norm.out
  (out, { p with norm.out := #[] })

end Parser
end QueenDomCheck
