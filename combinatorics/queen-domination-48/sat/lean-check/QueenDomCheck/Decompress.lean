/-
Reading a compressed certificate: `zstd -dc -- FILE`, streamed.  UNTRUSTED (whatever bytes arrive are
checked as a proof afterwards).

Two ways:

  * `ProofStream.direct`: the checker process spawns `zstd` itself, one process per certificate.
    Simple, but a `fork` of a process with several threads and hundreds of MB of live memory is
    expensive (page tables are copied and every thread takes copy-on-write faults afterwards); with
    47,580 certificates this costs more than the checking of the small ones.

  * a *decompression server* (`serve`, run by `qdcheck --decompress-server` as a child process that
    is started while the checker is still small, one per worker thread): it reads file names from
    its standard input, spawns `zstd -dc -- FILE` for each and relays the output to its standard
    output in frames

        D <number of bytes>\n<bytes>          (any number of times)
        E <exit code of zstd> <its stderr, on one line>\n

    so that many certificates travel through one pipe and the forks happen in a small process.
    `Decompressor` is the client side.
-/
namespace QueenDomCheck

/-- printable ASCII on one line -/
def oneLine (b : ByteArray) : String :=
  String.ofList (b.toList.map fun c => if c < 32 || c > 126 then ' ' else Char.ofNat c.toNat)

/-- The decompressed text of one certificate. -/
structure ProofStream where
  /-- the next chunk; the empty array at the end (and from then on) -/
  read : IO ByteArray
  /-- to be called after `read` has returned the empty array: exit code of the decompressor and its
  error output -/
  finish : IO (Nat × String)

/-- `zstd -dc -- path` as a child of this process. -/
def ProofStream.direct (zstd : String) (path : System.FilePath) (chunk : USize) : IO ProofStream := do
  let child ← IO.Process.spawn {
    cmd := zstd, args := #["-dc", "--", path.toString],
    stdin := .null, stdout := .piped, stderr := .piped }
  return {
    read := child.stdout.read chunk
    finish := do
      let err ← child.stderr.readBinToEnd
      let rc ← child.wait
      return (rc.toNat, (oneLine err).trimAscii.toString) }

/-- `s` with every control character (and the Unicode line separators) replaced by `?`.  A string that
went through `oneLineStr` cannot start a new line of the output. -/
def oneLineStr (s : String) : String :=
  s.map fun c =>
    if c.toNat < 32 || c.toNat == 127 || c.toNat == 0x85 || c.toNat == 0x2028 || c.toNat == 0x2029 then '?'
    else c

/-! ### The server -/

/-- The main loop of `qdcheck --decompress-server`: one file name per input line. -/
def serve (zstd : String) (chunk : USize) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let path := (line.dropEndWhile (· == '\n')).toString
    try
      let child ← IO.Process.spawn {
        cmd := zstd, args := #["-dc", "--", path],
        stdin := .null, stdout := .piped, stderr := .piped }
      repeat
        let buf ← child.stdout.read chunk
        if buf.isEmpty then break
        stdout.putStr s!"D {buf.size}\n"
        stdout.write buf
      let err ← child.stderr.readBinToEnd
      let rc ← child.wait
      stdout.putStr s!"E {rc} {(oneLine err).trimAscii}\n"
    catch e =>
      stdout.putStr s!"E 255 {(oneLine (toString e).toUTF8).trimAscii}\n"
    stdout.flush

/-! ### The client -/

/-- A running decompression server. -/
structure Decompressor where
  child : IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .inherit }

def Decompressor.start (cmd : String) (args : Array String) : IO Decompressor := do
  let child ← IO.Process.spawn {
    cmd, args, stdin := .piped, stdout := .piped, stderr := .inherit }
  return { child }

def Decompressor.stop (d : Decompressor) : IO Unit := do
  try d.child.kill catch _ => pure ()
  try discard <| d.child.wait catch _ => pure ()

/-- State of the request for one file. -/
structure Request where
  /-- the end frame has been read (or the conversation has broken down) -/
  done : Bool := false
  rc : Nat := 0
  msg : String := ""
  /-- the server did not answer as expected: it has to be replaced -/
  broken : Bool := false

/-- Ask the server for a file; `broken` is set in the returned state if anything goes wrong. -/
def Decompressor.request (d : Decompressor) (path : System.FilePath) : IO (IO.Ref Request × ProofStream) := do
  let st ← IO.mkRef ({} : Request)
  let fail (msg : String) : IO Unit := st.set { done := true, rc := 255, msg, broken := true }
  let name := path.toString
  if name.contains '\n' then
    st.set { done := true, rc := 255, msg := "file name contains a newline" }
  else
    try
      d.child.stdin.putStr (name ++ "\n")
      d.child.stdin.flush
    catch e => fail s!"decompression server: {e}"
  let read : IO ByteArray := do
    if (← st.get).done then return ByteArray.empty
    try
      let line ← d.child.stdout.getLine
      let line := (line.dropEndWhile (· == '\n')).toString
      if line.startsWith "D " then
        match (line.drop 2).toString.toNat? with
        | some n =>
          let buf ← d.child.stdout.read n.toUSize
          if n == 0 || buf.size != n then
            fail "decompression server: short frame"; return ByteArray.empty
          return buf
        | none => fail "decompression server: bad frame header"; return ByteArray.empty
      else if line.startsWith "E " then
        let rest := (line.drop 2).toString
        let rcStr := (rest.takeWhile Char.isDigit).toString
        match rcStr.toNat? with
        | some rc =>
          st.set { done := true, rc, msg := (rest.drop rcStr.length).toString.trimAscii.toString }
        | none => fail "decompression server: bad end frame"
        return ByteArray.empty
      else
        fail "decompression server: unexpected answer (or it has died)"; return ByteArray.empty
    catch e =>
      fail s!"decompression server: {e}"; return ByteArray.empty
  return (st, { read, finish := do let s ← st.get; return (s.rc, s.msg) })

end QueenDomCheck
