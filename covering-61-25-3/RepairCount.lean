import Std

/-!
A choice of retained groups leaves a table of missing triples. The test below
keeps a choice whenever the following necessary conditions permit a completion.

* Each time a pair meets it can cover at most 23 missing thirds. Each time
  a person attends they can supply at most 24 required pair meetings.
* If a person attends two groups, the companions exclusive to opposite groups
  cannot form a missing triple with that person.
* If a person attends once, all their missing neighbors must fit in that group.
  Everyone with lower bound one who attends more often uses an extra seat.
  We try every possible number of these exceptions in each interchangeable class.
  The singletons that share a missing triple force the same group. We try every
  placement of their forced sets, then repeat the seat test with those sets known.

A person is represented by one bit of a 61-bit set. A group position is one bit
of a separate 27-bit set. The two group tables contain unions for their respective
halves, so a lookup gives the people who meet a given pair in the retained groups.
-/

namespace Covering61.RepairSearch

private def choices {α : Type} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | _+1, [] => []
  | n+1, x::xs => (choices n xs).map (x :: ·) ++ choices (n+1) xs

private def bitsOf (xs : List Nat) : Nat := xs.foldl (fun b x => b ||| (1 <<< x)) 0

/-- A word has one bit per person. This is the parallel byte-sum popcount on 64 bits. -/
private def countPeople (w : UInt64) : Nat :=
  let a : UInt64 := w - ((w >>> (1 : UInt64)) &&& (0x5555555555555555 : UInt64))
  let b : UInt64 := (a &&& (0x3333333333333333 : UInt64)) + ((a >>> (2 : UInt64)) &&& (0x3333333333333333 : UInt64))
  let c : UInt64 := (b + (b >>> (4 : UInt64))) &&& (0x0f0f0f0f0f0f0f0f : UInt64)
  ((c * (0x0101010101010101 : UInt64)) >>> (56 : UInt64)).toNat

private def personBit (p : Nat) : UInt64 := 1 <<< p.toUInt64

/-- Entry s gives the union of the groups at the positions set in s. -/
private def unionsOf (groups : List Nat) : Array UInt64 :=
  groups.foldl (init := #[0]) fun a g => a ++ a.map (· ||| g.toUInt64)

private structure LinkTables where
  attendance : Array Nat
  first : Array UInt64
  last : Array UInt64

private def linkTables (groups : List Nat) : LinkTables :=
  let rows := groups.toArray
  let attendance := (List.range 61).map fun p =>
    (List.range rows.size).foldl (init := 0) fun s i =>
      if rows[i]!.testBit p then s ||| (1 <<< i) else s
  ⟨attendance.toArray, unionsOf (groups.take 14), unionsOf (groups.drop 14)⟩

private structure ResidualLinks where
  /-- The entry (p,q) is the set of people t for whom p,q,t still need a common group. -/
  thirds : Array UInt64
  requiredPairs : Array Nat
  neighbors : Array UInt64
  lower : Array Nat

/-- Count the required pair meetings and seats from the table of missing thirds. -/
private def makeLinks (thirdsAt : Nat → Nat → UInt64) : ResidualLinks := Id.run do
  let mut thirds := #[]
  let mut pairs := #[]
  let mut neighbors := #[]
  let mut lower := #[]
  for p in [:61] do
    let mut demand := 0
    let mut touch : UInt64 := 0
    for q in [:61] do
      let missing := thirdsAt p q
      let shared := (countPeople missing + 22) / 23
      thirds := thirds.push missing
      pairs := pairs.push shared
      touch := touch ||| missing
      demand := demand + shared
    neighbors := neighbors.push touch
    lower := lower.push ((demand + 23) / 24)
  return ⟨thirds, pairs, neighbors, lower⟩

private def residualLinks (tables : LinkTables) (deleted : Nat) : ResidualLinks :=
  makeLinks fun p q =>
    if p == q then 0 else
      let common := tables.attendance[p]! &&& tables.attendance[q]!
      let kept := common ^^^ (common &&& deleted)
      let covered := tables.first[kept &&& 16383]! ||| tables.last[kept >>> 14]!
      0x1fffffffffffffff &&& (~~~(covered ||| personBit p ||| personBit q))

/-- Remove triples already covered by a replacement whose 25 places are known. -/
private def afterForced (links : ResidualLinks) (group : UInt64) : ResidualLinks :=
  makeLinks fun p q =>
    let pair := personBit p ||| personBit q
    let missing := links.thirds[61*p+q]!
    if pair &&& group == pair then missing &&& (~~~group) else missing

/-- With the right side restricted to R, every vertex with no edge into R
    may go on the left. A left set L and a right set R admit disjoint
    subsets of size w exactly when both sizes are at least w and their
    union has size at least 2w. -/
private def hasSides (width p : Nat) (links : ResidualLinks) (eligible : UInt64) :
    Nat → UInt64 → StateM (Std.HashSet UInt64) Bool
  | 0, _ => pure false
  | fuel+1, right => do
    if (← get).contains right then return false
    modify (·.insert right)
    let mut left : UInt64 := 0
    let mut next := #[]
    let mut available : UInt64 := 0
    for q in [:61] do
      if eligible &&& personBit q != 0 then
        let smaller := right &&& (~~~links.thirds[61*p+q]!)
        if smaller == right then
          left := left ||| personBit q
        else if countPeople smaller ≥ width then
          next := next.push smaller
          available := available ||| personBit q
    if countPeople left ≥ width && countPeople (left ||| right) ≥ 2*width then return true
    if countPeople (left ||| available) < width ||
        countPeople (left ||| available ||| right) < 2*width then return false
    -- Any valid left side can be reached by imposing its members' exclusions
    -- one at a time. Every recursive call removes at least one person.
    for smaller in next do
      if ← hasSides width p links eligible fuel smaller then return true
    return false

/-- A person in exactly two new groups has two sets of at most 24 companions.
    If d companions must appear in their union, each exclusive side has at
    least d−24 people. A pair within a residual triple with p cannot cross sides. -/
private def twoGroupsPossible (links : ResidualLinks) (lower : Array Nat) (r p : Nat) : Bool := Id.run do
  let mut mandatory := links.neighbors[p]!
  let mut both := 0
  for q in [:61] do
    if q != p then
      if lower[q]! + 2 > r then mandatory := mandatory ||| personBit q
      if lower[q]! ≥ r || links.requiredPairs[61*p+q]! ≥ 2 then both := both ||| personBit q
  let width := countPeople mandatory - 24
  if width == 0 then return true
  let available := mandatory &&& (~~~both)
  if countPeople available < 2*width then return false
  return (hasSides width p links available 61 available).run' {}

private def strengthenedDegrees (links : ResidualLinks) (r : Nat) : Option (Array Nat) := Id.run do
  let mut lower := links.lower
  let mut total := lower.sum
  if total > 25*r || lower.any (· > r) then return none
  -- Every successful promotion consumes a seat. A pass without a promotion is final.
  for _ in [:25*r+1] do
    let start := total
    for p in [:61] do
      let before := lower[p]!
      for s in [before:r+1] do
        let mut demand := 0
        for q in [:61] do
          if p != q then
            demand := demand + max links.requiredPairs[61*p+q]! (s + lower[q]! - r)
        if demand ≤ 24*s && (s != 2 || twoGroupsPossible links lower r p) then break
        if s == r then return none
        lower := lower.set! p (s+1)
        total := total+1
        if total > 25*r then return none
    if start == total then return some lower
  return some lower

/-- The shared pair already occupies every forced load containing both people.
    When its uncovered thirds do not fit in one such load even after filling
    every spare seat, it must occupy at least two replacement groups. -/
private def fitLoads (r : Nat) (links : ResidualLinks) (lower : Array Nat) (singles : UInt64)
    (loads : Array UInt64) : Bool := Id.run do
  let mut pairs := links.requiredPairs
  let mut occupied := ByteArray.mk (Array.replicate (61*61) 0)
  for g in loads do
    let mut left := g
    for _ in [:countPeople g] do
      let p := (left &&& (0 - left)).log2.toNat
      left := left &&& (left-1)
      let mut right := left
      for _ in [:countPeople right] do
        let q := (right &&& (0 - right)).log2.toNat
        right := right &&& (right-1)
        let i := 61*p+q
        let used := occupied[i]! + 1
        occupied := occupied.set! i used
        let atLeast := if countPeople (g ||| links.thirds[i]!) > 25 then 2 else 1
        let d := max used.toNat atLeast
        if d > pairs[i]! then
          pairs := (pairs.set! i d).set! (61*q+p) d
  let mut need := 0
  for p in [:61] do
    let mut between := 0
    for q in [:61] do between := between + pairs[61*p+q]!
    let n := max lower[p]! ((between+23)/24)
    if singles &&& personBit p != 0 && n > 1 then return false
    need := need+n
    if need > 25*r then return false
  for g in loads do
    if countPeople g == 25 && (strengthenedDegrees (afterForced links g) (r-1)).isNone then return false
  return true

private def distributeLoads (r : Nat) (links : ResidualLinks) (lower : Array Nat) (singles : UInt64) :
    List UInt64 → Array UInt64 → Bool
  | [], loads => fitLoads r links lower singles loads
  | g :: gs, loads => Id.run do
    for j in [:loads.size] do
      let joined := g ||| loads[j]!
      if countPeople joined ≤ 25 && distributeLoads r links lower singles gs (loads.set! j joined) then
        return true
    return loads.size < r && distributeLoads r links lower singles gs (loads.push g)

private def singletonLoads (r : Nat) (links : ResidualLinks) (lower : Array Nat) (singles : UInt64) :
    Bool := Id.run do
  let mut left := singles
  let mut comps := []
  for p in [:61] do
    if left &&& personBit p != 0 then
      let mut members := personBit p
      let mut load := members
      for _ in [:61] do
        let known := members
        for q in [:61] do
          if members &&& personBit q != 0 then load := load ||| links.neighbors[q]!
        members := load &&& left
        if known == members then break
      if countPeople load > 25 then return false
      comps := load :: comps
      left := left &&& (~~~members)
  let sorted := comps.mergeSort (fun a b => countPeople a ≥ countPeople b)
  return distributeLoads r links lower singles sorted #[]

/-- A single class contains people with the same incidence in every kept group.
    Permuting these people preserves all residual triples. It suffices to select
    the number of exceptions in the class. Each exception needs one extra seat. -/
private def singletonChoices (r : Nat) (links : ResidualLinks) :
    List (List Nat) → Array Nat → UInt64 → Nat → Bool
  | [], lower, singles, _ => singletonLoads r links lower singles
  | group :: rest, lower, singles, slack => Id.run do
    let mut xs := lower
    let mut forced := singles
    if singletonChoices r links rest xs forced slack then return true
    let mut spent := 0
    for p in group do
      if spent == slack then break
      spent := spent+1
      xs := xs.set! p 2
      forced := forced ^^^ personBit p
      if singletonChoices r links rest xs forced (slack-spent) then return true
    return false

private def repairPossible (r : Nat) (tables : LinkTables) (removed : List Nat) : Bool := Id.run do
  let cut := bitsOf removed
  let links := residualLinks tables cut
  let some lower := strengthenedDegrees links r | return false
  let mut classes : Std.HashMap Nat (List Nat) := {}
  let mut singles : UInt64 := 0
  for p in [:61] do
    if lower[p]! == 1 then
      let sig := tables.attendance[p]!
      let kept := sig ^^^ (sig &&& cut)
      classes := classes.insert kept (p :: classes.getD kept [])
      singles := singles ||| personBit p
  return singletonChoices r links classes.values lower singles (25*r-lower.sum)

/-- Enumerate every removal. A real completion must pass the attendance and forced-group tests. -/
def remainingCases (groups : List Nat) (removeCount replacements : Nat) : List (List Nat) :=
  let tables := linkTables groups
  (choices removeCount (List.range groups.length)).filter (repairPossible replacements tables)

end Covering61.RepairSearch
