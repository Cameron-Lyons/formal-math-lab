import Ramsey556.Cert16.Cover
import Ramsey556.Cert16.Iso

namespace Ramsey556.Cert16

/-- Packed chunks store 32 triangular graph codes, each in 128 bits. -/
structure Table where
  size : Nat
  chunks : Array Nat

def Table.get (t : Table) (i : Nat) : Nat :=
  (t.chunks[i/32]! / (2^(128*(i%32)))) % (2^128)

def Table.graphs (t : Table) : List Nat := (List.range t.size).map t.get

def RowGood (n g : Nat) (dest : Table) : Prop :=
  ∀ m, m < 2^n → threshold (n+1) ≤ edgeCount n g + popcount n m →
    Safe n g m → ∃ h ∈ dest.graphs, ExtendsTo n g m h

/-- A canonical destination and an explicit permutation for one neighbor mask. -/
structure Move where
  mask : Nat
  index : Nat
  graph : Nat
  perm : Nat

def maskSet : List Move → Nat
  | [] => 0
  | e::es =>
    let s := maskSet es
    let b := 2^e.mask
    if s < b then b+s else s

private theorem maskSet_mem {es : List Move} {m : Nat} (h : (maskSet es).testBit m = true) :
    ∃ e ∈ es, e.mask = m := by
  induction es with
  | nil => simp [maskSet] at h
  | cons e es ih =>
    simp only [maskSet] at h
    by_cases lt : maskSet es < 2^e.mask
    · rw [ite_eq_left lt] at h
      have key : 2^e.mask + maskSet es = (2^e.mask ||| maskSet es) := by
        simpa only [Nat.mul_one] using Nat.two_pow_add_eq_or_of_lt lt 1
      rw [key, Nat.testBit_or, Bool.or_eq_true] at h
      rcases h with he | ht
      · refine ⟨e, by simp, ?_⟩
        apply Classical.byContradiction
        intro ne
        rw [Nat.testBit_two_pow_of_ne ne] at he
        contradiction
      · obtain ⟨a, hm, ha⟩ := ih ht
        exact ⟨a, List.mem_cons_of_mem e hm, ha⟩
    · rw [ite_eq_right lt] at h
      obtain ⟨a, hm, ha⟩ := ih h
      exact ⟨a, List.mem_cons_of_mem e hm, ha⟩

/-- Fields `graph`, `matrix` and `accepted` cache intermediate natural numbers.
The Boolean checks verify each cache before using it in the search. -/
structure Row where
  graph : Nat
  paths : List Nat
  matrix : Nat
  moves : List Move
  accepted : Nat

def rowCheck (n : Nat) (base dest : Table) (idx : Nat) (r : Row) : Bool :=
  base.get idx == r.graph &&
  conflicts n r.graph r.paths == r.matrix &&
  r.moves.all (fun e => e.index < dest.size && dest.get e.index == e.graph &&
    isoOK n r.graph e.mask e.graph e.perm) &&
  maskSet r.moves == r.accepted &&
  covered r.matrix r.accepted n 0 (threshold (n+1) - edgeCount n r.graph)

theorem row_sound {n idx : Nat} {base dest : Table} (r : Row)
    (checked : rowCheck n base dest idx r = true) : RowGood n (base.get idx) dest := by
  simp only [rowCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at checked
  obtain ⟨⟨⟨⟨hbase, matrix⟩, moves⟩, masks⟩, cover⟩ := checked
  rw [hbase]
  intro m hm hd safe
  rw [← matrix, ← masks] at cover
  obtain ⟨e, mem, rfl⟩ := maskSet_mem (covered_sound r.paths safe hm hd cover)
  obtain ⟨⟨small, same⟩, perm⟩ := moves e mem
  exact ⟨_, List.mem_map.mpr ⟨_,List.mem_range.mpr small,same⟩,isoOK_sound perm⟩

def checkChunk (n : Nat) (base dest : Table) (offset : Nat) : List Row → Bool
  | [] => true
  | r::rs => rowCheck n base dest offset r && checkChunk n base dest (offset+1) rs

theorem chunk_sound (n : Nat) (base dest : Table) (offset : Nat) (rs : List Row)
    (checked : checkChunk n base dest offset rs = true) :
    ∀ i, offset ≤ i → i < offset+rs.length → RowGood n (base.get i) dest := by
  induction rs generalizing offset with
  | nil => intro i lo hi; simp at hi; omega
  | cons r rs ih =>
    simp only [checkChunk, Bool.and_eq_true] at checked
    intro i lo hi
    by_cases eq : i = offset
    · subst i; exact row_sound r checked.1
    · simp only [List.length_cons] at hi
      exact ih (offset+1) checked.2 _ (by omega) (by omega)

end Ramsey556.Cert16
