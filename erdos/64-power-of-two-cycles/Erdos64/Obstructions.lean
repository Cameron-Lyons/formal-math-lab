import Erdos64.ExtensionSoundness

namespace Erdos64

/-- Check distinctness in one pass, remembering the labels already used. -/
def distinctBits (v : Array Nat) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, used =>
    let x := v.getD n 0
    !used.testBit x && distinctBits v n (used ||| (1 <<< x))

theorem distinctBits_sound {v : Array Nat} {n used : Nat}
    (h : distinctBits v n used = true) :
    (∀ i < n, used.testBit (v.getD i 0) = false) ∧
    (∀ i < n, ∀ j < n, v.getD i 0 = v.getD j 0 → i = j) := by
  induction n generalizing used with
  | zero => exact ⟨by omega, by omega⟩
  | succ n ih =>
    simp only [distinctBits, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨avoids,inj⟩ := ih h.2
    have clearBits : ∀ i < n, used.testBit (v.getD i 0) = false ∧
        v.getD n 0 ≠ v.getD i 0 := by
      intro i hi
      have t := avoids i hi
      simpa only [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow,
        Bool.or_eq_false_iff, decide_eq_false_iff_not] using t
    constructor
    · intro i hi
      by_cases e : i = n
      · simpa only [e] using h.1
      · exact (clearBits i (by omega)).1
    · intro i hi j hj eq
      by_cases a : i = n <;> by_cases b : j = n
      · omega
      · exact False.elim ((clearBits j (by omega)).2 (a ▸ eq))
      · exact False.elim ((clearBits i (by omega)).2 (b ▸ eq.symm))
      · exact inj i (by omega) j (by omega) eq

/-- A simple a--b path of k edges is a local certificate. Adding a common
neighbor gives a cycle of k+2 edges. -/
private def validPair (rows v : Array Nat) (a b k : Nat) : Bool :=
  decide (v.getD 0 0 = a ∧ v.getD k 0 = b ∧
    (∀ i : Fin (k+1), v.getD i.val 0 < rows.size) ∧
    distinctBits v (k+1) 0 = true ∧
    (∀ i : Fin k, adjAt rows (v.getD i.val 0) (v.getD (i.val+1) 0) = true))

private theorem validPair_sound {V : Type u} {G : Graph V} {rows p : Array Nat}
    {a b k m : Nat} (h : validPair rows p a b k = true)
    (ha : m.testBit a = true) (hb : m.testBit b = true)
    (c : Copy G (rows.size+1) (extendAdj rows.size (adjAt rows) m)) : HasCycle G (k+2) := by
  obtain ⟨first,last,rg,inj,steps⟩ := of_decide_eq_true h
  apply cycleThroughFresh c (f := fun i => p.getD i 0)
  · intro i hi
    exact rg ⟨i,by omega⟩
  · intro i hi j hj eq
    exact (distinctBits_sound inj).2 i (by omega) j (by omega) eq
  · intro i hi
    exact steps ⟨i,hi⟩
  · simpa only [first] using ha
  · simpa only [last] using hb

private def foldBits {α : Type} (f : α → Nat → α) : Nat → Nat → α → α
  | 0, _, acc => acc
  | fuel+1, bits, acc =>
    if bits == 0 then acc else
    let rest := bits &&& (bits-1)
    foldBits f fuel rest (f acc (bits ^^^ rest).log2)

/-- A single depth-first traversal supplies at most one path for every target
label. Paths are stored in reverse order with the most recently visited label
first. The first component marks endpoints that still need a witness. -/
private def findPaths (nbrs : Array Nat) : Nat → Nat → Nat → List Nat →
    Nat × Array (List Nat) → Nat × Array (List Nat)
  | fuel, v, avail, prev, hits =>
    let path := v :: prev
    let found := if (fuel == 12 || fuel == 8 || fuel == 0) && hits.1.testBit v then
      (hits.1 ^^^ (1 <<< v), hits.2.setIfInBounds v path)
      else hits
    match fuel with
    | 0 => found
    | left+1 =>
      if found.1 == 0 then found else
      foldBits (fun acc w => findPaths nbrs left w (avail ^^^ (1 <<< w)) path acc)
        nbrs.size (avail &&& nbrs.getD v 0) found

private def allowFromWitness (rows : Array Nat) (a b : Nat) (rev : List Nat) : Bool :=
  if rev.isEmpty then true else
  let p := rev.reverse.toArray
  !((p.size == 3 && validPair rows p a b 2) ||
    (p.size == 7 && validPair rows p a b 6) ||
    (p.size == 15 && validPair rows p a b 14))

private def packAllowed (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | t+1 => (if f t then 1 <<< t else 0) + packAllowed f t

private theorem packAllowed_lt (f : Nat → Bool) (n : Nat) : packAllowed f n < 2^n := by
  induction n with
  | zero => simp [packAllowed]
  | succ n ih =>
    cases h : f n <;> simp only [packAllowed, h, Bool.false_eq_true,
      ↓reduceIte, Nat.zero_add, Nat.one_shiftLeft, Nat.pow_succ] <;> omega

private theorem packAllowed_bit (f : Nat → Bool) {n j : Nat} (hj : j < n) :
    (packAllowed f n).testBit j = f j := by
  induction n with
  | zero => omega
  | succ n ih =>
    have lower := packAllowed_lt f n
    by_cases e : j = n
    · subst j
      cases h : f n <;> simp [packAllowed, h, Nat.one_shiftLeft,
        Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow lower]
    · have lt : j < n := by omega
      cases h : f n <;> simp [packAllowed, h, Nat.one_shiftLeft,
        Nat.testBit_two_pow_add_gt lt, ih lt]

/-- Symmetric bit masks for the lower-triangular board, one per vertex. -/
def neighborMasks (rows : Array Nat) : Array Nat :=
  Array.ofFn fun i : Fin rows.size => packAllowed (adjAt rows i.val) rows.size

theorem neighborMasks_bit {rows : Array Nat} {i j : Nat} (hi : i < rows.size)
    (hj : j < rows.size) :
    ((neighborMasks rows).getD i 0).testBit j = adjAt rows i j := by
  simp only [neighborMasks, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hi,
    ↓reduceDIte, Option.getD_some, packAllowed_bit _ hj]

private def allowRow (rows nbrs : Array Nat) (a : Nat) : Nat :=
  let maxMask := (1 <<< rows.size)-1
  let others := maxMask ^^^ (1 <<< a)
  let paths := (findPaths nbrs 14 a others [] (others, Array.replicate rows.size [])).2
  packAllowed (fun b => a != b && allowFromWitness rows a b (paths.getD b [])) rows.size

/-- A one in row i, column j marks the ordered pair as available when a
prospective neighbor set is chosen. Witness paths are sought once per source. -/
def allowedRows (rows nbrs : Array Nat) : Array (Thunk Nat) :=
  Array.ofFn fun i : Fin rows.size => Thunk.mk fun _ => allowRow rows nbrs i.val

def allowedAt (cached : Array (Thunk Nat)) (i : Nat) : Nat :=
  (cached.getD i (Thunk.pure 0)).get

theorem allowedRows_sound {V : Type u} {G : Graph V} {rows nbrs : Array Nat}
    {i j m : Nat} (hi : i < rows.size) (hj : j < rows.size) (hne : i ≠ j)
    (hmi : m.testBit i = true) (hmj : m.testBit j = true)
    (hn : ¬ (HasCycle G 4 ∨ HasCycle G 8 ∨ HasCycle G 16))
    (c : Copy G (rows.size+1) (extendAdj rows.size (adjAt rows) m)) :
    (allowedAt (allowedRows rows nbrs) i).testBit j = true := by
  simp only [allowedAt, allowedRows, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hi,
    ↓reduceDIte, Option.getD_some, Thunk.get, allowRow, packAllowed_bit _ hj, bne_iff_ne.mpr hne,
    Bool.true_and]
  unfold allowFromWitness
  split
  · rfl
  · simp only [Bool.not_eq_true', Bool.or_eq_false_iff, Bool.and_eq_false_iff]
    constructor
    · constructor
      · right; apply Bool.eq_false_iff.mpr; intro h
        exact hn (Or.inl (validPair_sound h hmi hmj c))
      · right; apply Bool.eq_false_iff.mpr; intro h
        exact hn (Or.inr (Or.inl (validPair_sound h hmi hmj c)))
    · right; apply Bool.eq_false_iff.mpr; intro h
      exact hn (Or.inr (Or.inr (validPair_sound h hmi hmj c)))

end Erdos64
