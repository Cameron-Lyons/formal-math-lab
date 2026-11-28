import Height14.Transfer
import Height14.Formula

namespace Height14.Cert

/-- The score pass keeps one live array and the earlier array needed for the
period check. The Boolean accumulates the scalar bounds at whole columns. -/
structure ScoreTrace where
  current : Array Nat
  earlier : Array Nat
  ok : Bool

def traceScores (g : Graph) : Nat → ScoreTrace
  | 0 =>
    let a := initial g
    ⟨a, #[], decide (a.getD 0 0 ≤ formula 0 + 1)⟩
  | t+1 =>
    let p := traceScores g t
    let a := back g (phase (t+1)) p.current
    ⟨a, if t + 1 = 560 then a else p.earlier,
      p.ok && (t.succ % 14 != 0 || decide (a.getD 0 0 ≤ formula ((t+1)/14) + 1))⟩

def allBelow (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n+1 => p n && allBelow p n

theorem allBelow_spec {p : Nat → Bool} {n : Nat} (h : allBelow p n = true)
    {i : Nat} (hi : i < n) : p i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [allBelow, Bool.and_eq_true] at h
    by_cases he : i = n
    · simpa [he] using h.1
    · exact ih h.2 (by omega)

def checkScores (g : Graph) : Bool :=
  let q := traceScores g 644
  q.ok && allBelow (fun i => decide (q.current.getD i 0 ≤ shift 52 (q.earlier.getD i 0))) q.current.size

theorem trace_current (g : Graph) (t : Nat) : (traceScores g t).current = vals g t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [traceScores, vals, ih]

theorem trace_earlier (g : Graph) (t : Nat) (ht : 560 ≤ t) :
    (traceScores g t).earlier = vals g 560 := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases he : t + 1 = 560
    · simp only [traceScores, he, ↓reduceIte, trace_current]
      rw [← he, vals]
    · simp only [traceScores, he, ↓reduceIte]
      exact ih (by omega)

theorem trace_base (g : Graph) (t n : Nat) (ht : (traceScores g t).ok = true)
    (hn : 14*n ≤ t) : (vals g (14*n)).getD 0 0 ≤ formula n + 1 := by
  induction t with
  | zero =>
    obtain rfl : n = 0 := by omega
    simpa [traceScores, vals] using ht
  | succ t ih =>
    simp only [traceScores, Bool.and_eq_true] at ht
    by_cases h : 14*n ≤ t
    · exact ih ht.1 h
    · have he : t + 1 = 14*n := by omega
      have hm : (t+1)%14 = 0 := by omega
      have hd : (t+1)/14 = n := by omega
      have hk := ht.2
      simp [hm, hd, trace_current] at hk
      rw [← he, vals]
      simpa using hk

theorem check_base {g : Graph} (hg : checkScores g = true) {n : Nat} (hn : n ≤ 46) :
    (vals g (14*n)).getD 0 0 ≤ formula n + 1 := by
  simp only [checkScores, Bool.and_eq_true] at hg
  exact trace_base g 644 n hg.1 (by omega)

theorem check_period {g : Graph} (hg : checkScores g = true) (i : Nat) :
    (vals g (14*46)).getD i 0 ≤ shift 52 ((vals g (14*40)).getD i 0) := by
  let q := traceScores g 644
  simp only [checkScores, Bool.and_eq_true] at hg
  have hm := hg.2
  by_cases hi : i < q.current.size
  · have h := allBelow_spec hm hi
    simpa only [decide_eq_true_eq, trace_current, trace_earlier g 644 (by decide)] using h
  · have hz : ¬i < (vals g (14*46)).size := by simpa only [q, trace_current] using hi
    simp [Array.getD, hz]

end Height14.Cert
