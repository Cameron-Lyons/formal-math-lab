module

public import SixGroups

@[expose] public section

namespace Erdos708Slots.FiniteCheck
open IntervalSix

def allBig : List ℕ := [11,13,17,19,23,29,31,37,41,43,47,53,59,61,67]
def possibleShared : List ℕ := [11,13,17,19,23]

private theorem primes_valid : (∀ p ∈ allBig, p.Prime ∧ 11 ≤ p) ∧
    (∀ p ∈ possibleShared, p.Prime ∧ 11 ≤ p) := by decide

/-- An original is immediately handled if it fits two spare sites, or has a
prime which cannot divide three distinct originals in the window length. -/
def pruneElem (M a : ℕ) : Bool :=
  ((List.range (M/8)).any fun i => let v := i+1
    a % v == 0 && 7*(a/v) ≤ M) ||
  (allBig.any fun p => M < 3*p && a % p == 0)

/-- For the remaining originals, eliminate any prime that occurs only once or twice.
After element pruning, every remaining prime at least eleven is at most 23. -/
def pruneSet (_M : ℕ) (xs : List ℕ) : Bool :=
  possibleShared.any fun p =>
    let n := xs.countP fun a => a % p == 0
    1 ≤ n && n ≤ 2

theorem pruneElem_sound {L M a : ℕ} (A : Finset ℕ) (hc : A.card=6)
    (hm : ∀ a ∈ A, 2≤a ∧ a≤M) (_h69 : M≤69) (ha : a∈A) (h : pruneElem M a) :
    Cover L M 8 (∏ a∈A,a) := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · obtain ⟨i,hi,hv⟩ := List.any_eq_true.mp h
    let v := i+1
    have htest : a%v=0 ∧ 7*(a/v)≤M := by simpa [v] using hv
    have hdiv := Nat.dvd_of_mod_eq_zero htest.1
    have hp : 0<a := by have := (hm a ha).1; omega
    have hvpos : 0<v := by dsimp [v]; omega
    have hvcap : 8*v≤M := by have := List.mem_range.mp hi; dsimp [v]; omega
    have hup := Nat.div_pos (Nat.le_of_dvd hp hdiv) hvpos
    exact splitCover A hc hm ha ⟨a/v,v,hup,hvpos,(Nat.div_mul_cancel hdiv).symm,htest.2,hvcap⟩
  · obtain ⟨p,hp,hv⟩ := List.any_eq_true.mp h
    obtain ⟨h3,hd⟩ : M<3*p ∧ a%p=0 := by simpa using hv
    obtain ⟨hpp,h11⟩ := primes_valid.1 p hp
    apply rarePrimeCover A hc hm hpp (by omega) (by omega) ⟨a,Finset.mem_filter.mpr ⟨ha,Nat.dvd_of_mod_eq_zero hd⟩⟩
    have hsub : A.filter (p∣·) ⊆ {p,2*p} := by
      intro b hb
      obtain ⟨hb',hdiv⟩ := Finset.mem_filter.mp hb
      obtain ⟨hl,hr⟩ := hm b hb'
      have hdvd := Nat.div_mul_cancel hdiv
      have hpos := Nat.div_pos (Nat.le_of_dvd (by omega) hdiv) hpp.pos
      have hlt : b/p<3 := (Nat.div_lt_iff_lt_mul hpp.pos).mpr (hr.trans_lt h3)
      rcases (by omega : b/p=1 ∨ b/p=2) with h1 | h2
      · rw [h1,one_mul] at hdvd; simp [← hdvd]
      · rw [h2] at hdvd; simp [← hdvd]
    exact (Finset.card_le_card hsub).trans (by simpa only [Finset.card_singleton] using Finset.card_insert_le p {2*p})

theorem pruneSet_sound {L M : ℕ} (A : Finset ℕ) (hc : A.card=6)
    (hm : ∀ a ∈ A, 2≤a ∧ a≤M) (h69 : M≤69)
    (xs : List ℕ) (hx : xs.toFinset=A) (h : pruneSet M xs) :
    Cover L M 8 (∏ a∈A,a) := by
  obtain ⟨p,hp,hv⟩ := List.any_eq_true.mp h
  obtain ⟨h1,h2⟩ : 1 ≤ xs.countP (fun a => a%p==0) ∧ xs.countP (fun a => a%p==0) ≤ 2 := by simpa using hv
  obtain ⟨hpp,h11⟩ := primes_valid.2 p hp
  let ys := xs.filter (fun a => a%p==0)
  have hlen : 1≤ys.length ∧ ys.length≤2 := by simpa [ys,List.countP_eq_length_filter] using And.intro h1 h2
  have heq : ys.toFinset=A.filter (p∣·) := by
    ext a
    simp [ys,←hx,Nat.dvd_iff_mod_eq_zero]
  apply rarePrimeCover A hc hm hpp (by omega) (by omega)
  · rw [←heq]
    obtain ⟨a,ha⟩ := List.length_pos_iff_exists_mem.mp hlen.1
    exact ⟨a,List.mem_toFinset.mpr ha⟩
  · rw [←heq]
    exact ys.toFinset_card_le.trans hlen.2

end Erdos708Slots.FiniteCheck
