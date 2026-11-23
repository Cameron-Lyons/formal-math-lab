import FixedLength
import Initial
import LineCheck
import SlopeChoices
import Wedge
import Mathlib.Tactic.Eval
import Mathlib.Tactic.FinCases

namespace Erdos677
open Finset

/-- The rational slope and its modular inverse are proposals. This checker
validates them before testing every line in the resulting determinant range. -/
private def checkSlab (k u v L : ℕ) (c : SlopeChoice) : Bool :=
  let a : ℤ := c.p
  let b : ℤ := c.q
  let l : ℤ := L
  let e : ℤ := c.E
  decide (0 < c.q ∧ (a * c.z ≡ 1 [ZMOD b]) ∧
    (v : ℤ)*l^2*(max 0 (a*l-e))^k ≤ (u : ℤ)*(l^2-35)*(b*l)^k ∧
    (u : ℤ)*l^2*(b*l)^k ≤ (v : ℤ)*(l^2-35)*(a*l+e)^k) &&
  (List.range (4*c.E+1)).all fun j => checkLine k L c.p c.q c.z ((j : ℤ) - 2*c.E)

private theorem slab_sound {n m k L u v : ℕ} {c : SlopeChoice}
    (hc : checkSlab k u v L c = true) (hk : 0 < k) (hd : n+k ≤ m)
    (hv : 0 < v) (hL : 8 ≤ L)
    (hlo : L ≤ 2*n+k+1) (hhi : 2*n+k+1 < 2*L)
    (henv :
      (u:ℤ)*((L:ℤ)^2-35)*(2*(n:ℤ)+k+1)^k ≤ (v:ℤ)*(L:ℤ)^2*(2*(m:ℤ)+k+1)^k ∧
      (v:ℤ)*((L:ℤ)^2-35)*(2*(m:ℤ)+k+1)^k ≤ (u:ℤ)*(L:ℤ)^2*(2*(n:ℤ)+k+1)^k) :
    lcmInterval m k ≠ lcmInterval n k := by
  obtain ⟨valid, lines⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hq, hinv, hlow, hupp⟩ := of_decide_eq_true valid
  have hlo' : (L:ℤ) ≤ 2*(n:ℤ)+k+1 := by exact_mod_cast hlo
  have hhi' : 2*(n:ℤ)+k+1 < 2*(L:ℤ) := by exact_mod_cast hhi
  have hs : 35 < (L:ℤ)^2 := by
    have h8 : (8:ℤ) ≤ L := by exact_mod_cast hL
    nlinarith [mul_nonneg (show 0 ≤ (L:ℤ)-8 by omega) (show 0 ≤ (L:ℤ)+8 by omega)]
  have hb := determinant_bounds hk (Int.natCast_nonneg u) (by exact_mod_cast hv)
    (by omega) (Int.natCast_nonneg c.p) (by exact_mod_cast hq) (Int.natCast_nonneg c.E)
    (show 0 ≤ 2*(m:ℤ)+k+1 by omega) hs hlo' hhi' henv.1 henv.2 hlow hupp
  let h := (c.q:ℤ)*(2*(m:ℤ)+k+1) - c.p*(2*(n:ℤ)+k+1)
  have hh : -(2*(c.E:ℤ)) ≤ h ∧ h ≤ 2*c.E := hb
  let j := (h + 2*c.E).toNat
  have hj : (j:ℤ) = h + 2*c.E := Int.toNat_of_nonneg (by omega)
  have hjmem : j ∈ List.range (4*c.E+1) := List.mem_range.mpr (by omega)
  have hl := List.all_eq_true.mp lines j hjmem
  apply checkLine_sound hl hq hinv hk hd hlo' hhi'
  change (j:ℤ)-2*c.E = h
  omega

-- Guesses are evaluated during elaboration and supplied as literals. Their
-- generation is outside the proof; checkSlab verifies every field it uses.
private abbrev GuessTable := List ((ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ))

private def makeGuessTable (k cap L : ℕ) : GuessTable :=
  (List.range (cap+1)).flatMap fun u =>
    if u ∣ cap then (List.range u).filterMap fun v =>
      if 0 < v ∧ v ∣ cap ∧ u.Coprime v then
        let c := slopeChoice k u v L
        some ((u,v), (c.p,c.q,c.z,c.E))
      else none
    else []

private def guessAt (table : GuessTable) (u v : ℕ) : SlopeChoice :=
  let (p,q,z,e) := (table.lookup (u,v)).getD (0,0,0,0)
  ⟨p,q,z,e⟩

private def checkRatios (k cap L : ℕ) (table : GuessTable) : Bool :=
  (List.range (cap+1)).all fun u =>
    if u ∣ cap then (List.range u).all fun v =>
      if 0 < v ∧ v ∣ cap ∧ u.Coprime v then checkSlab k u v L (guessAt table u v) else true
    else true

private theorem slab_ne {n m k cap L : ℕ} (hk : k=5 ∨ k=6) (hd : n+k ≤ m)
    (hcap : cap = lcmInterval 0 k / k) (hcap' : 0 < cap) (hL : 8 ≤ L)
    (hlo : L ≤ 2*n+k+1) (hhi : 2*n+k+1 < 2*L)
    {table : GuessTable} (checked : checkRatios k cap L table = true) : lcmInterval m k ≠ lcmInterval n k := by
  intro heq
  obtain ⟨u,v,hv,hvu,hu',hv',hcop,env⟩ := five_six_reduced_envelope hk (by omega) heq
  rw [← hcap] at hu' hv'
  have hu := Nat.le_of_dvd hcap' hu'
  have hucheck := List.all_eq_true.mp checked u (List.mem_range.mpr (by omega))
  simp only [hu', ↓reduceIte] at hucheck
  have hvcheck := List.all_eq_true.mp hucheck v (List.mem_range.mpr hvu)
  rw [ite_eq_left (show 0 < v ∧ v ∣ cap ∧ u.Coprime v from ⟨hv,hv',hcop⟩)] at hvcheck
  exact slab_sound hvcheck (by omega) hd hv hL hlo hhi
    (env L (by positivity) (by exact_mod_cast hlo)) heq

private abbrev Tables := List (GuessTable × GuessTable)

private def makeTables : ℕ → ℕ → Tables
  | 0, _ => []
  | len+1, L => (makeGuessTable 5 12 L, makeGuessTable 6 10 L) :: makeTables len (2*L)

/-- Check slabs with successive lower endpoints L,2L,..., for both lengths. -/
private def heightCheck : Tables → ℕ → Bool
  | [], _ => true
  | (five,six)::rest, L =>
    (checkRatios 5 12 L five && checkRatios 6 10 L six) && heightCheck rest (2*L)

private theorem heightCheck_sound {n m k : ℕ} (hk : k=5 ∨ k=6) (hd : n+k ≤ m)
    {tables : Tables} {L : ℕ} (hL : 8 ≤ L) (hlo : L ≤ 2*n+k+1)
    (hhi : 2*n+k+1 < L * 2^tables.length)
    (checked : heightCheck tables L = true) : lcmInterval m k ≠ lcmInterval n k := by
  induction tables generalizing L with
  | nil => simp at hhi; omega
  | cons t rest ih =>
    obtain ⟨here, tail⟩ := Bool.and_eq_true_iff.mp checked
    obtain ⟨h5,h6⟩ := Bool.and_eq_true_iff.mp here
    by_cases h : 2*n+k+1 < 2*L
    · rcases hk with rfl | rfl
      · exact slab_ne (Or.inl rfl) hd factor_constant_five.symm (by decide) hL hlo h h5
      · exact slab_ne (Or.inr rfl) hd factor_constant_six.symm (by decide) hL hlo h h6
    · apply ih (by omega) (by omega) _ tail
      simpa only [List.length_cons, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hhi

/-- This wrapper checks the number of slabs as well as the guesses. -/
private theorem checked_chunk {base len : ℕ} (tables : Tables)
    (hlen : tables.length = len) (checked : heightCheck tables (8*2^base) = true)
    {n m k : ℕ} (hk : k=5 ∨ k=6) (hd : n+k ≤ m)
    (hlo : 8*2^base ≤ 2*n+k+1) (hhi : 2*n+k+1 < 8*2^(base+len)) :
    lcmInterval m k ≠ lcmInterval n k := by
  apply heightCheck_sound hk hd (by have := Nat.two_pow_pos base; omega) hlo _ checked
  simpa [hlen, pow_add, Nat.mul_assoc] using hhi

private def CertifiedChunk (base len : ℕ) : Prop := ∃ t : Tables,
  t.length = len ∧ heightCheck t (8 * 2^base) = true

-- The generated tables contain only untrusted integer guesses. Each chunk is
-- checked separately so that kernel evaluation can discard its working memory.
local macro "certify_chunk " base:num len:num : tactic => `(tactic|
  exact ⟨eval% makeTables $len (8 * 2 ^ $base), by decide, by decide +kernel⟩)

private theorem chunks_sound {w count n m k : ℕ} (hk : k=5 ∨ k=6)
    (hd : n+k ≤ m) (hlo : 8 ≤ 2*n+k+1) (hhi : 2*n+k+1 < 8 * 2^(w*count))
    (certs : ∀ j < count, CertifiedChunk (w*j) w) :
    lcmInterval m k ≠ lcmInterval n k := by
  induction count with
  | zero => simp at hhi; omega
  | succ count ih =>
    by_cases h : 2*n+k+1 < 8 * 2^(w*count)
    · exact ih h (fun j hj => certs j (by omega))
    · obtain ⟨t, ht, checked⟩ := certs count (by omega)
      apply checked_chunk t ht checked hk hd (by omega)
      simpa only [Nat.mul_succ] using hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem certified_twenty_digits (j : Fin 9) : CertifiedChunk (8*j.val) 8 := by
  fin_cases j
  · as_aux_lemma => certify_chunk 0 8
  · as_aux_lemma => certify_chunk 8 8
  · as_aux_lemma => certify_chunk 16 8
  · as_aux_lemma => certify_chunk 24 8
  · as_aux_lemma => certify_chunk 32 8
  · as_aux_lemma => certify_chunk 40 8
  · as_aux_lemma => certify_chunk 48 8
  · as_aux_lemma => certify_chunk 56 8
  · as_aux_lemma => certify_chunk 64 8

/-- At lengths five and six the earlier start parameter can be as large as
10²⁰. There is no restriction on the later endpoint. -/
theorem no_collision_five_six {n m k : ℕ} (hk : k=5 ∨ k=6)
    (hd : n+k ≤ m) (hn : n ≤ 10^20) : lcmInterval m k ≠ lcmInterval n k := by
  by_cases hz : n = 0
  · subst n
    exact first_block_ne (by omega) (by omega)
  · apply chunks_sound (w := 8) (count := 9) hk hd (by omega) _
      (fun j hj => certified_twenty_digits ⟨j,hj⟩)
    norm_num at hn ⊢
    omega

end Erdos677
