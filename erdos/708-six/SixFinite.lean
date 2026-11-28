module

public import SixResidues
public import SixPrune
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Data.Nat.Factors

@[expose] public section

namespace Erdos708Slots
namespace FiniteCheck

/-- Independent target factors can reuse sites if their least common multiple suffices. -/
theorem merge {L M i j a b : ℕ} (ha : Cover L M i a) (hb : Cover L M j b) :
    Cover L M (i+j) (Nat.lcm a b) := by
  obtain ⟨S, hS, hs, hsp⟩ := ha
  obtain ⟨T, hT, ht, htp⟩ := hb
  refine ⟨S ∪ T, Finset.union_subset hS hT,
    (Finset.card_union_le _ _).trans (Nat.add_le_add hs ht), ?_⟩
  exact Nat.lcm_dvd (hsp.trans (Finset.prod_dvd_prod_of_subset _ _ id Finset.subset_union_left))
    (htp.trans (Finset.prod_dvd_prod_of_subset _ _ id Finset.subset_union_right))

/-- A list of independently covered groups. The LCM accounts exactly for any sites
used by more than one group. -/
def groupProd (gs : List (List ℕ)) : ℕ := (gs.map List.prod).foldr Nat.lcm 1
def groupSize (gs : List (List ℕ)) : ℕ := (gs.map List.length).sum

theorem groups_sound {L M : ℕ} (gs : List (List ℕ))
    (h : gs.all (slotOK M 0 1)) : Cover L M (groupSize gs) (groupProd gs) := by
  have emp : Cover L M 0 1 := ⟨∅, by simp, by simp, by simp⟩
  induction gs with
  | nil => simpa [groupSize, groupProd] using emp
  | cons g gs ih =>
    obtain ⟨hg, hrs⟩ := by simpa using h
    have hhead := slotOK_sound g emp hg
    simpa [groupProd, groupSize] using merge hhead (ih (List.all_eq_true.mpr hrs))


def validGroups (M P : ℕ) (gs : List (List ℕ)) : Bool :=
  groupSize gs ≤ 8 && gs.all (slotOK M 0 1) && groupProd gs % P == 0

private theorem validGroups_sound {L M P : ℕ} {gs : List (List ℕ)}
    (h : validGroups M P gs) : Cover L M 8 P := by
  simp only [validGroups, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact (groups_sound gs h.1.2).mono h.1.1 (Nat.dvd_of_mod_eq_zero h.2)

def residueOK (M P : ℕ) : Bool :=
  (M == 18 && P == 9*10*12*15*16*18) || (M == 20 && P == 10*12*15*16*18*20)

private theorem residueOK_sound {L M P : ℕ} (h : residueOK M P) : Cover L M 8 P := by
  simp only [residueOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact residue18 L
  · exact residue20 L

/-- Build a row from the last factor to the first. At step j the prefix product
will be r/d, so the required gcd test is already known. A factor of one skips
an unused slot. -/
def greedyRow (M : ℕ) (ds : List ℕ) : ℕ → ℕ → List ℕ → List ℕ
  | 0, _, acc => acc
  | j+1, r, acc =>
    if r=1 then acc else
      let d := (ds.find? fun d => r%d == 0 && (j+1)*d.gcd (r/d) ≤ M).getD 1
      greedyRow M ds j (r/d) (d::acc)

/-- First try to cover the whole product with one row. If necessary give each prime
power its own row, or detach just one prime power and try every possible last
factor for the complementary row. The resulting certificate is checked by `validGroups`. -/
def witness (M P : ℕ) (xs : List ℕ) : List (List ℕ) := Id.run do
  let divisors := (List.range (M+1)).reverse.filter fun d => 1 < d && P%d == 0
  let whole := greedyRow M divisors 8 P []
  if whole.prod == P then return [whole]
  let primes := xs.flatMap Nat.primeFactorsList
  let parts := primes.eraseDups.map fun p =>
    let q := p^(primes.count p)
    (q, ((List.range 8).findSome? fun i =>
      let row := greedyRow M divisors (i+1) q []
      if row.prod == q then some row else none).getD [])
  let separate := parts.map Prod.snd
  if groupSize separate ≤ 8 then return separate
  for (q, row) in parts do
    let k := 8 - row.length
    let r := P/q
    if 0 < k then
      for d in divisors ++ [1] do
        if r%d == 0 && k*d.gcd (r/d) ≤ M then
          let rest := greedyRow M divisors (k-1) (r/d) [d]
          if rest.prod == r then return [row,rest]
  return []

def check (M : ℕ) (xs : List ℕ) : Bool :=
  let P := xs.prod
  pruneSet M xs || residueOK M P || validGroups M P (witness M P xs)

private theorem check_sound {L M : ℕ} {xs : List ℕ} (hn : xs.Nodup)
    (h69 : M ≤ 69) (hc : xs.toFinset.card=6) (hm : ∀ a ∈ xs.toFinset, 2 ≤ a ∧ a ≤ M)
    (h : check M xs) : Cover L M 8 (∏ a ∈ xs.toFinset,a) := by
  have hp : (∏ a ∈ xs.toFinset,a) = xs.prod := by simpa using List.prod_toFinset id hn
  simp only [check, Bool.or_eq_true] at h
  rcases h with (h|h)|h
  · exact pruneSet_sound _ hc hm h69 xs rfl h
  · rw [hp]; exact residueOK_sound h
  · rw [hp]; exact validGroups_sound h

def hardList (M : ℕ) : List ℕ :=
  (List.range M).filter fun a => 2 ≤ a && !(pruneElem M a)

def windowCheck (M : ℕ) : Bool :=
  pruneElem M M || ((hardList M).sublistsLen 5).all fun ds => check M (M :: ds)

theorem windowCheck_sound {L M : ℕ} (A : Finset ℕ) (hc : A.card=6) (hM : M ∈ A)
    (hm : ∀ a ∈ A, 2 ≤ a ∧ a ≤ M) (h69 : M ≤ 69) (h : windowCheck M) :
    Cover L M 8 (∏ a ∈ A,a) := by
  by_cases he : ∃ a ∈ A, pruneElem M a = true
  · obtain ⟨a,ha,hd⟩ := he
    exact pruneElem_sound A hc hm h69 ha hd
  have hne (a : ℕ) (ha : a ∈ A) : pruneElem M a = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    exact he ⟨a,ha,h⟩
  let ds := (hardList M).filter (· ∈ A)
  have hdset : ds.toFinset = A.erase M := by
    ext d
    simp only [ds,hardList,List.mem_toFinset,List.mem_filter,List.mem_range,
      Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,Finset.mem_erase]
    constructor
    · rintro ⟨⟨hlt,_⟩,ha⟩
      exact ⟨by omega,ha⟩
    · rintro ⟨hnm,ha⟩
      obtain ⟨hl,hu⟩ := hm d ha
      exact ⟨⟨by omega,hl,hne d ha⟩,ha⟩
  have hnod : ds.Nodup := (List.nodup_range.filter _).filter _
  have hlen : ds.length = 5 := by
    rw [← List.toFinset_card_of_nodup hnod, hdset, Finset.card_erase_of_mem hM,hc]
  have hmem : ds ∈ (hardList M).sublistsLen 5 :=
    List.mem_sublistsLen.mpr ⟨List.filter_sublist,hlen⟩
  have hcons : (M::ds).toFinset = A := by rw [List.toFinset_cons,hdset,Finset.insert_erase hM]
  have hall : ((hardList M).sublistsLen 5).all (fun l => check M (M::l)) :=
    by simpa only [windowCheck,hne M hM,Bool.false_or] using h
  have hnot : M ∉ ds := by
    intro hmem
    have := List.mem_toFinset.mpr hmem
    rw [hdset] at this
    exact Finset.notMem_erase _ _ this
  rw [← hcons] at hc hm ⊢
  exact check_sound (List.nodup_cons.mpr ⟨hnot,hnod⟩) h69 hc hm (List.all_eq_true.mp hall ds hmem)

-- Exhaustive small-window check using the preceding sound procedures.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem allWindows : ∀ m : Fin 70, windowCheck m := by
  intro m
  fin_cases m <;> decide +kernel

theorem finiteUpper {L M : ℕ} (A : Finset ℕ) (hc : A.card=6) (hM : M ∈ A)
    (hm : ∀ a ∈ A, 2 ≤ a ∧ a ≤ M) (hlt : M < 70) : Cover L M 8 (∏ a ∈ A,a) :=
  windowCheck_sound A hc hM hm (by omega) (allWindows ⟨M,hlt⟩)

end FiniteCheck
end Erdos708Slots
