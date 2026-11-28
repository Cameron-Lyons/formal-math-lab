import Ramsey556.Cert16.Path

namespace Ramsey556.Cert16

/-- Store only endpoint conflicts whose eight-vertex path verifies. Each
entry has 16 possible right endpoints and the packed table has 16 rows. -/
def conflicts (n g : Nat) : List Nat → Nat
  | [] => 0
  | c :: cs =>
    let x := c % 16
    let y := (c >>> 28) % 16
    let t := conflicts n g cs
    if pathOK n g x y c then t ||| (1 <<< (16*y+x)) else t

private theorem conflicts_safe {n g m : Nat} (ps : List Nat) (hs : Safe n g m)
    {i j : Nat} (hj : j < 16) (hb : (conflicts n g ps).testBit (16*i+j) = true)
    (hi' : m.testBit i = true) (hj' : m.testBit j = true) : False := by
  induction ps with
  | nil => simp [conflicts] at hb
  | cons c cs ih =>
    simp only [conflicts] at hb
    split at hb
    · rename_i path
      rw [Nat.testBit_or, Bool.or_eq_true] at hb
      rcases hb with hb | hb
      · exact ih hb
      · have key : 16*i+j = 16*((c >>> 28) % 16) + c%16 := by
          apply Classical.byContradiction
          intro h
          rw [Nat.one_shiftLeft, Nat.testBit_two_pow_of_ne (Ne.symm h)] at hb
          contradiction
        have hx : j = c%16 := by omega
        have hy : i = (c >>> 28)%16 := by omega
        subst j
        subst i
        exact pathOK_safe path hs hj' hi'
    · exact ih hb

/-- Search only the masks that can still attain the density threshold and
that have not already selected a pair forbidden by a certified path.
`chosenBits` contains the selected vertices with indices at least `left`. -/
def covered (table accepted : Nat) : (left chosenBits need : Nat) → Bool
  | 0, chosenBits, need => 0 < need || accepted.testBit chosenBits
  | left+1, chosenBits, need =>
    if left+1 < need then true else
      covered table accepted left chosenBits need &&
      (0 < (chosenBits &&& ((table >>> (16*left)) % 65536)) ||
       covered table accepted left (chosenBits ||| (1 <<< left)) (need-1))

private theorem popcount_succ (n m : Nat) :
    popcount (n+1) m = popcount n m + (m.testBit n).toNat := by
  simp [popcount, List.range_succ, Bool.toNat]
  split <;> simp_all

private theorem covered_rec {n g m accepted : Nat} (ps : List Nat) (hs : Safe n g m)
    (left chosenBits need : Nat)
    (hc : covered (conflicts n g ps) accepted left chosenBits need = true)
    (weight : need ≤ popcount left m)
    (seen : ∀ k, chosenBits.testBit k = (decide (left ≤ k) && m.testBit k)) :
    accepted.testBit m = true := by
  induction left generalizing chosenBits need with
  | zero =>
    have eq : chosenBits = m := Nat.eq_of_testBit_eq (fun k => by simpa using seen k)
    have h : need = 0 := by simpa [popcount] using weight
    simpa [covered, eq, h] using hc
  | succ i ih =>
    have bound : popcount (i+1) m ≤ i+1 :=
      by simpa only [popcount, List.length_range] using List.length_filter_le m.testBit (List.range (i+1))
    simp only [covered, ite_eq_right (show ¬ i+1 < need by omega), Bool.and_eq_true] at hc
    by_cases chosen : m.testBit i = true
    · have zero : chosenBits &&& ((conflicts n g ps >>> (16*i)) % 65536) = 0 := by
        apply Nat.eq_of_testBit_eq
        intro j
        simp only [Nat.testBit_and, Nat.zero_testBit, Bool.and_eq_false_imp]
        intro already
        have mj : m.testBit j = true := by
          cases e : m.testBit j <;> simp_all
        change ((conflicts n g ps >>> (16*i)) % (2^16)).testBit j = false
        simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
        by_cases h : j < 16
        · simp only [h, decide_true, Bool.true_and]
          cases bit : (conflicts n g ps).testBit (16*i+j) with
          | false => rfl
          | true => exact (conflicts_safe ps hs h bit chosen mj).elim
        · simp [h]
      have follow := hc.2
      simp [zero] at follow
      apply ih _ _ follow
      · rw [popcount_succ, chosen] at weight
        simp at weight
        omega
      · intro k
        rw [Nat.testBit_or, seen, Nat.one_shiftLeft]
        by_cases eq : i=k
        · subst k
          simp [chosen]
        · rw [Nat.testBit_two_pow_of_ne eq]
          have same : i+1 ≤ k ↔ i ≤ k := by omega
          simp [same]
    · apply ih _ _ hc.1
      · simpa [popcount_succ, Bool.eq_false_iff.mpr chosen] using weight
      · intro k
        rw [seen]
        by_cases eq : i=k
        · subst k
          simp [Bool.eq_false_iff.mpr chosen]
        · have same : i+1 ≤ k ↔ i ≤ k := by omega
          simp [same]

theorem covered_sound {n g m accepted : Nat} (ps : List Nat) (hs : Safe n g m)
    (hm : m < 2^n) (hd : threshold (n+1) ≤ edgeCount n g + popcount n m)
    (h : covered (conflicts n g ps) accepted n 0 (threshold (n+1)-edgeCount n g) = true) :
    accepted.testBit m = true := by
  apply covered_rec ps hs _ _ _ h (by omega)
  intro k
  by_cases hk : n ≤ k
  · have bound := Nat.pow_le_pow_right (by decide : 0 < 2) hk
    simp [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm bound)]
  · simp [hk]

end Ramsey556.Cert16
