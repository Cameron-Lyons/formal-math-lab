import Height14.Transfer

namespace Height14.Cert

private structure Builder extends Layer where
  table : Array Nat := Array.replicate 4194304 0
  deriving Inhabited

@[inline] private def hashSlot (k : UInt64) : Nat :=
  let h := (k ^^^ (k >>> 33)) * 0xff51afd7ed558ccd
  ((h ^^^ (h >>> 33)) &&& 4194303).toNat

/-- Linear probing compares full keys, using zero as an unoccupied bucket. -/
private def probe (keys : Array UInt64) (table : Array Nat) (key : UInt64) (p : Nat) :
    Nat → Nat
  | 0 => p
  | fuel+1 =>
    let found := table[p]!
    if found == 0 || keys[found-1]! == key then p
    else probe keys table key ((p+1) &&& 4194303) fuel

private def intern (s : Builder) (key : Option UInt64) : Nat × Builder := Id.run do
  let some k := key | return (0, s)
  let p := probe s.keys s.table k (hashSlot k) 4194304
  let found := s.table[p]!
  if found != 0 then return (found, s)
  let j := s.keys.size + 1
  return (j, {s with keys := s.keys.push k, table := s.table.set! p j})

private def extend (r : Nat) (src dst : Builder) : Builder × Builder := Id.run do
  let mut edges := src.edges
  let mut dst := dst
  for i in [edges.size:src.keys.size] do
    let key := src.keys[i]!
    let (skip, d) := intern dst (Machine.step key r false)
    let (fill, d) := intern d (Machine.step key r true)
    dst := d
    edges := edges.push (skip + (fill <<< 22))
  return ({src with edges}, dst)

private def sweep (layers : Array Builder) : Array Builder := Id.run do
  let mut layers := layers
  for r in [:14] do
    let n := (r+1)%14
    let (src, ls) := layers.swapAt! r {}
    let (dst, ls) := ls.swapAt! n {}
    let (src, dst) := extend r src dst
    layers := (ls.set! r src).set! n dst
  return layers

/-- Starting at the empty key, close both decisions at each row. The independent
certificate checks the resulting graph, so round and table sizes need no
a priori exhaustiveness assumption. -/
def buildGraph (rounds : Nat) : Graph := Id.run do
  let (_, first) := intern {} (some 0)
  let mut layers := (Array.replicate 14 ({} : Builder)).set! 0 first
  for _ in [:rounds] do layers := sweep layers
  return layers.map Builder.toLayer

def graph (_ : Unit := ()) : Graph := buildGraph 9

end Height14.Cert
