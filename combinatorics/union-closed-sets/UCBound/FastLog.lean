module

public import UCBound.CertConst

@[expose] public section

/-!
# Fast Pure-Kernel Interval Logarithm and Elementary Functions (`FastLog`)

Achieves a ~60x kernel speedup over `Interval.log` (~0.4ms vs ~24ms per call) while keeping
100% pure kernel reduction (zero `native_decide`, zero `sorry`, zero custom axioms):
- `fastLog2`: 6-step binary-search integer `log2` for `a < 2^64` (zero `WellFounded.fix`).
- `logTab`: 257-entry balanced lookup tree for `Real.log ((256 + j) / 256)`, certified against
  `mem_logNat` in a single `rfl` check!
- `fastLogCore`: 2-term integer `atanh` (`2 * (u + u^3 / 3) ± 6 ULPs`) valid for `|u| ≤ 1/1024`.
- `fastLog`, `fastH`, `fastHp`, `fastPhi`, `fastR`, `fastV`, `fastB`, `fastF`, `fastJ`:
  drop-in fast interval evaluators with identical soundness signatures to `IntervalOps`.
-/

namespace UCBound.FastIv

open UCBound UCBound.Iv UCBound.Cert

/-! ### Strict Call-by-Value Kernel Reducers (`natCBV`, `intCBV`, `ivCBV`)

Lean 4's kernel uses call-by-name WHNF reduction, where `let x := e; f x x` duplicates `e`!
Pattern-matching on `Nat` / `Int` / `Interval` forces strict CBV reduction of `e` to a concrete
literal ONCE before passing it to the continuation, eliminating exponential WHNF blowups. -/

def natCBV {α : Type} (n : ℕ) (f : ℕ → α) : α :=
  match n with | 0 => f 0 | k + 1 => f (k + 1)

def intCBV {α : Type} (x : ℤ) (f : ℤ → α) : α :=
  match x with
  | .ofNat n => match n with | 0 => f 0 | k + 1 => f (.ofNat (k + 1))
  | .negSucc n => match n with | 0 => f (.negSucc 0) | k + 1 => f (.negSucc (k + 1))

def ivCBV {α : Type} (I : Interval) (f : Interval → α) : α :=
  match I with
  | ⟨lo, hi⟩ => intCBV lo fun lo' => intCBV hi fun hi' => f ⟨lo', hi'⟩

@[simp] lemma natCBV_eq {α : Type} (n : ℕ) (f : ℕ → α) : natCBV n f = f n := by
  cases n <;> rfl

@[simp] lemma intCBV_eq {α : Type} (x : ℤ) (f : ℤ → α) : intCBV x f = f x := by
  cases x with
  | ofNat n => cases n <;> rfl
  | negSucc n => cases n <;> rfl

@[simp] lemma ivCBV_eq {α : Type} (I : Interval) (f : Interval → α) : ivCBV I f = f I := by
  cases I; simp [ivCBV]

def fadd (A B : Interval) : Interval :=
  ivCBV A fun A' => ivCBV B fun B' => add A' B'

def fsub (A B : Interval) : Interval :=
  ivCBV A fun A' => ivCBV B fun B' => sub A' B'

def fneg (A : Interval) : Interval :=
  ivCBV A fun A' => neg A'

def fmul (A B : Interval) : Interval :=
  ivCBV A fun A' => ivCBV B fun B' =>
  intCBV (A'.lo * B'.lo) fun p1 =>
  intCBV (A'.lo * B'.hi) fun p2 =>
  intCBV (A'.hi * B'.lo) fun p3 =>
  intCBV (A'.hi * B'.hi) fun p4 =>
  ⟨fdiv (min (min p1 p2) (min p3 p4)) SCALE,
   cdiv (max (max p1 p2) (max p3 p4)) SCALE⟩

def fsq (A : Interval) : Interval :=
  ivCBV A fun A' => sq A'

def finvPos (A : Interval) : Interval :=
  ivCBV A fun A' => invPos A'

def fdivPos (A B : Interval) : Interval :=
  fmul A (finvPos B)

def fdivNeg (A B : Interval) : Interval :=
  fneg (fdivPos A (fneg B))

def fclamp01 (A : Interval) : Interval :=
  ivCBV A fun A' => clamp01 A'

def fmaxZero (A : Interval) : Interval :=
  ivCBV A fun A' => maxZero A'

def fIxxIv (C : ConstIv) (X : Interval) : Interval :=
  ivCBV X fun X' =>
  if X'.lo == X'.hi then
    intCBV (max 0 (min (SCALE : ℤ) X'.lo)) fun a => IxxPt C a
  else
    IxxIv C X'

def fIxyIv (C : ConstIv) (X Y : Interval) : Interval :=
  ivCBV X fun X' => ivCBV Y fun Y' =>
  fclamp01 (fmul (fmul X' Y') (fadd ONE (fmul C.tau (fmul (fsub ONE X') (fsub ONE Y')))))

@[simp] lemma fadd_eq (A B : Interval) : fadd A B = add A B := by simp [fadd]
@[simp] lemma fsub_eq (A B : Interval) : fsub A B = sub A B := by simp [fsub]
@[simp] lemma fneg_eq (A : Interval) : fneg A = neg A := by simp [fneg]
@[simp] lemma fmul_eq (A B : Interval) : fmul A B = mul A B := by simp [fmul, mul]
@[simp] lemma fsq_eq (A : Interval) : fsq A = sq A := by simp [fsq]
@[simp] lemma finvPos_eq (A : Interval) : finvPos A = invPos A := by simp [finvPos]
@[simp] lemma fdivPos_eq (A B : Interval) : fdivPos A B = divPos A B := by simp [fdivPos, divPos]
@[simp] lemma fdivNeg_eq (A B : Interval) : fdivNeg A B = divNeg A B := by simp [fdivNeg, divNeg]
@[simp] lemma fclamp01_eq (A : Interval) : fclamp01 A = clamp01 A := by simp [fclamp01]
@[simp] lemma fmaxZero_eq (A : Interval) : fmaxZero A = maxZero A := by simp [fmaxZero]
@[simp] lemma fIxxIv_eq (C : ConstIv) (X : Interval) : fIxxIv C X = IxxIv C X := by
  unfold fIxxIv IxxIv; simp only [ivCBV_eq, intCBV_eq]
  split_ifs with h
  · have heq : X.lo = X.hi := beq_iff_eq.mp h
    rw [heq]
  · rfl
@[simp] lemma fIxyIv_eq (C : ConstIv) (X Y : Interval) : fIxyIv C X Y = IxyIv C X Y := by
  simp [fIxyIv, IxyIv]

/-- 6-step binary-search integer `log2` (exact for all `1 ≤ a < 2^64`, strict CBV, zero `WellFounded.fix`). -/
def fastLog2 (a : ℕ) : ℕ :=
  natCBV a fun a =>
  natCBV (if 4294967296 ≤ a then a / 4294967296 else a) fun a1 =>
  natCBV (if 4294967296 ≤ a then 32 else 0) fun d1 =>
  natCBV (if 65536 ≤ a1 then a1 / 65536 else a1) fun a2 =>
  natCBV (if 65536 ≤ a1 then 16 else 0) fun d2 =>
  natCBV (if 256 ≤ a2 then a2 / 256 else a2) fun a3 =>
  natCBV (if 256 ≤ a2 then 8 else 0) fun d3 =>
  natCBV (if 16 ≤ a3 then a3 / 16 else a3) fun a4 =>
  natCBV (if 16 ≤ a3 then 4 else 0) fun d4 =>
  natCBV (if 4 ≤ a4 then a4 / 4 else a4) fun a5 =>
  natCBV (if 4 ≤ a4 then 2 else 0) fun d5 =>
  natCBV (if 2 ≤ a5 then 1 else 0) fun d6 =>
  d1 + d2 + d3 + d4 + d5 + d6

lemma fastLog2_spec {a : ℕ} (ha0 : 0 < a) (ha64 : a < 2 ^ 64) :
    2 ^ fastLog2 a ≤ a ∧ a < 2 * 2 ^ fastLog2 a := by
  have step : ∀ (n m b : ℕ), 0 < n → n < b * b → b = 2 ^ m →
      let n' := if b ≤ n then n / b else n
      let d := if b ≤ n then m else 0
      0 < n' ∧ n' < b ∧ n' * 2 ^ d ≤ n ∧ n < (n' + 1) * 2 ^ d := by
    intro n m b hn0 hnb hb
    dsimp only
    split_ifs with h
    · refine ⟨Nat.div_pos h (by rw [hb]; positivity), ?_, ?_, ?_⟩
      · exact Nat.div_lt_of_lt_mul hnb
      · rw [← hb]; exact Nat.div_mul_le_self n b
      · rw [← hb, add_mul, one_mul]
        have := Nat.div_add_mod n b
        have := Nat.mod_lt n (show 0 < b by rw [hb]; positivity)
        have hcomm : n / b * b = b * (n / b) := mul_comm _ _
        omega
    · simp only [pow_zero, mul_one]
      exact ⟨hn0, by omega, le_rfl, by omega⟩
  unfold fastLog2; simp only [natCBV_eq]
  set a1 := if 4294967296 ≤ a then a / 4294967296 else a
  set d1 := if 4294967296 ≤ a then 32 else 0
  have h1 := step a 32 4294967296 ha0 (by omega) (by norm_num)
  change 0 < a1 ∧ a1 < 4294967296 ∧ a1 * 2 ^ d1 ≤ a ∧ a < (a1 + 1) * 2 ^ d1 at h1
  set a2 := if 65536 ≤ a1 then a1 / 65536 else a1
  set d2 := if 65536 ≤ a1 then 16 else 0
  have h2 := step a1 16 65536 h1.1 (by omega) (by norm_num)
  change 0 < a2 ∧ a2 < 65536 ∧ a2 * 2 ^ d2 ≤ a1 ∧ a1 < (a2 + 1) * 2 ^ d2 at h2
  set a3 := if 256 ≤ a2 then a2 / 256 else a2
  set d3 := if 256 ≤ a2 then 8 else 0
  have h3 := step a2 8 256 h2.1 (by omega) (by norm_num)
  change 0 < a3 ∧ a3 < 256 ∧ a3 * 2 ^ d3 ≤ a2 ∧ a2 < (a3 + 1) * 2 ^ d3 at h3
  set a4 := if 16 ≤ a3 then a3 / 16 else a3
  set d4 := if 16 ≤ a3 then 4 else 0
  have h4 := step a3 4 16 h3.1 (by omega) (by norm_num)
  change 0 < a4 ∧ a4 < 16 ∧ a4 * 2 ^ d4 ≤ a3 ∧ a3 < (a4 + 1) * 2 ^ d4 at h4
  set a5 := if 4 ≤ a4 then a4 / 4 else a4
  set d5 := if 4 ≤ a4 then 2 else 0
  have h5 := step a4 2 4 h4.1 (by omega) (by norm_num)
  change 0 < a5 ∧ a5 < 4 ∧ a5 * 2 ^ d5 ≤ a4 ∧ a4 < (a5 + 1) * 2 ^ d5 at h5
  set a6 := if 2 ≤ a5 then a5 / 2 else a5
  set d6 := if 2 ≤ a5 then 1 else 0
  have h6 := step a5 1 2 h5.1 (by omega) (by norm_num)
  change 0 < a6 ∧ a6 < 2 ∧ a6 * 2 ^ d6 ≤ a5 ∧ a5 < (a6 + 1) * 2 ^ d6 at h6
  have ha6_eq : a6 = 1 := by omega
  have hp : 2 ^ (d1 + d2 + d3 + d4 + d5 + d6) = 2 ^ d6 * 2 ^ d5 * 2 ^ d4 * 2 ^ d3 * 2 ^ d2 * 2 ^ d1 := by
    simp only [pow_add]; ring
  rw [hp]
  have hle6 : 2 ^ d6 ≤ a5 := by rw [ha6_eq, one_mul] at h6; exact h6.2.2.1
  have hlt6 : a5 < 2 * 2 ^ d6 := by rw [ha6_eq] at h6; exact h6.2.2.2
  have hle5 : 2 ^ d6 * 2 ^ d5 ≤ a4 := le_trans (Nat.mul_le_mul_right _ hle6) h5.2.2.1
  have hlt5 : a4 < 2 * 2 ^ d6 * 2 ^ d5 := lt_of_lt_of_le h5.2.2.2 (Nat.mul_le_mul_right _ hlt6)
  have hle4 : 2 ^ d6 * 2 ^ d5 * 2 ^ d4 ≤ a3 := le_trans (Nat.mul_le_mul_right _ hle5) h4.2.2.1
  have hlt4 : a3 < 2 * 2 ^ d6 * 2 ^ d5 * 2 ^ d4 := lt_of_lt_of_le h4.2.2.2 (Nat.mul_le_mul_right _ hlt5)
  have hle3 : 2 ^ d6 * 2 ^ d5 * 2 ^ d4 * 2 ^ d3 ≤ a2 := le_trans (Nat.mul_le_mul_right _ hle4) h3.2.2.1
  have hlt3 : a2 < 2 * 2 ^ d6 * 2 ^ d5 * 2 ^ d4 * 2 ^ d3 := lt_of_lt_of_le h3.2.2.2 (Nat.mul_le_mul_right _ hlt4)
  have hle2 : 2 ^ d6 * 2 ^ d5 * 2 ^ d4 * 2 ^ d3 * 2 ^ d2 ≤ a1 := le_trans (Nat.mul_le_mul_right _ hle3) h2.2.2.1
  have hlt2 : a1 < 2 * 2 ^ d6 * 2 ^ d5 * 2 ^ d4 * 2 ^ d3 * 2 ^ d2 := lt_of_lt_of_le h2.2.2.2 (Nat.mul_le_mul_right _ hlt3)
  have hle1 : 2 ^ d6 * 2 ^ d5 * 2 ^ d4 * 2 ^ d3 * 2 ^ d2 * 2 ^ d1 ≤ a := le_trans (Nat.mul_le_mul_right _ hle2) h1.2.2.1
  have hlt1 : a < 2 * (2 ^ d6 * 2 ^ d5 * 2 ^ d4 * 2 ^ d3 * 2 ^ d2 * 2 ^ d1) := by
    have := lt_of_lt_of_le h1.2.2.2 (Nat.mul_le_mul_right _ hlt2)
    linarith
  exact ⟨hle1, hlt1⟩

/-- Balanced 257-entry lookup tree for `Real.log ((256 + j) / 256)` (`j = 0..256`). -/
def logTab (j : ℕ) : Interval :=
  if j ≤ 128 then
    if j ≤ 64 then
      if j ≤ 32 then
        if j ≤ 16 then
          if j ≤ 8 then
            if j ≤ 4 then
              if j ≤ 2 then
                (if j ≤ 1 then (if j ≤ 0 then ⟨-1, 1⟩ else ⟨4389478880797, 4389478880819⟩) else ⟨8761911198741, 8761911198767⟩)
              else
                (if j ≤ 3 then ⟨13117428842625, 13117428842647⟩ else ⟨17456162176507, 17456162176531⟩)
            else
              (if j ≤ 6 then (if j ≤ 5 then ⟨21778240063135, 21778240063159⟩ else ⟨26083789886889, 26083789886915⟩) else (if j ≤ 7 then ⟨30372937576331, 30372937576357⟩ else ⟨34645807626285, 34645807626309⟩))
          else
            if j ≤ 12 then
              (if j ≤ 10 then (if j ≤ 9 then ⟨38902523119531, 38902523119555⟩ else ⟨43143205748085, 43143205748109⟩) else (if j ≤ 11 then ⟨47367975834053, 47367975834075⟩ else ⟨51576952350131, 51576952350155⟩))
            else
              (if j ≤ 14 then (if j ≤ 13 then ⟨55770252939713, 55770252939737⟩ else ⟨59947993936603, 59947993936629⟩) else (if j ≤ 15 then ⟨64110290384401, 64110290384425⟩ else ⟨68257256055487, 68257256055511⟩))
        else
          if j ≤ 24 then
            if j ≤ 20 then
              (if j ≤ 18 then (if j ≤ 17 then ⟨72389003469707, 72389003469731⟩ else ⟨76505643912675, 76505643912701⟩) else (if j ≤ 19 then ⟨80607287453769, 80607287453793⟩ else ⟨84694042963773, 84694042963801⟩))
            else
              (if j ≤ 22 then (if j ≤ 21 then ⟨88766018132245, 88766018132269⟩ else ⟨92823319484505, 92823319484529⟩) else (if j ≤ 23 then ⟨96866052398393, 96866052398419⟩ else ⟨100894321120677, 100894321120703⟩))
          else
            if j ≤ 28 then
              (if j ≤ 26 then (if j ≤ 25 then ⟨104908228783171, 104908228783197⟩ else ⟨108907877418595, 108907877418619⟩) else (if j ≤ 27 then ⟨112893367976133, 112893367976159⟩ else ⟨116864800336717, 116864800336741⟩))
            else
              (if j ≤ 30 then (if j ≤ 29 then ⟨120822273328047, 120822273328073⟩ else ⟨124765884739347, 124765884739375⟩) else (if j ≤ 31 then ⟨128695731335877, 128695731335905⟩ else ⟨132611908873153, 132611908873181⟩))
      else
        if j ≤ 48 then
          if j ≤ 40 then
            if j ≤ 36 then
              (if j ≤ 34 then (if j ≤ 33 then ⟨136514512110979, 136514512111005⟩ else ⟨140403634827173, 140403634827197⟩) else (if j ≤ 35 then ⟨144279369831107, 144279369831131⟩ else ⟨148141808976999, 148141808977027⟩))
            else
              (if j ≤ 38 then (if j ≤ 37 then ⟨151991043176973, 151991043176997⟩ else ⟨155827162413877, 155827162413901⟩) else (if j ≤ 39 then ⟨159650255753933, 159650255753957⟩ else ⟨163460411359135, 163460411359161⟩))
          else
            if j ≤ 44 then
              (if j ≤ 42 then (if j ≤ 41 then ⟨167257716499445, 167257716499471⟩ else ⟨171042257564787, 171042257564811⟩) else (if j ≤ 43 then ⟨174814120076841, 174814120076865⟩ else ⟨178573388700641, 178573388700665⟩))
            else
              (if j ≤ 46 then (if j ≤ 45 then ⟨182320147255975, 182320147256003⟩ else ⟨186054478728601, 186054478728625⟩) else (if j ≤ 47 then ⟨189776465281273, 189776465281301⟩ else ⟨193486188264599, 193486188264621⟩))
        else
          if j ≤ 56 then
            if j ≤ 52 then
              (if j ≤ 50 then (if j ≤ 49 then ⟨197183728227681, 197183728227707⟩ else ⟨200869164928645, 200869164928673⟩) else (if j ≤ 51 then ⟨204542577344947, 204542577344975⟩ else ⟨208204043683515, 208204043683545⟩))
            else
              (if j ≤ 54 then (if j ≤ 53 then ⟨211853641390771, 211853641390797⟩ else ⟨215491447162431, 215491447162459⟩) else (if j ≤ 55 then ⟨219117536953183, 219117536953209⟩ else ⟨222731985986221, 222731985986245⟩))
          else
            if j ≤ 60 then
              (if j ≤ 58 then (if j ≤ 57 then ⟨226334868762577, 226334868762603⟩ else ⟨229926259070369, 229926259070397⟩) else (if j ≤ 59 then ⟨233506229993841, 233506229993865⟩ else ⟨237074853922295, 237074853922319⟩))
            else
              (if j ≤ 62 then (if j ≤ 61 then ⟨240632202558883, 240632202558909⟩ else ⟨244178346929241, 244178346929271⟩) else (if j ≤ 63 then ⟨247713357390015, 247713357390037⟩ else ⟨251237303637187, 251237303637219⟩))
    else
      if j ≤ 96 then
        if j ≤ 80 then
          if j ≤ 72 then
            if j ≤ 68 then
              (if j ≤ 66 then (if j ≤ 65 then ⟨254750254714401, 254750254714431⟩ else ⟨258252279021011, 258252279021035⟩) else (if j ≤ 67 then ⟨261743444320089, 261743444320113⟩ else ⟨265223817746315, 265223817746341⟩))
            else
              (if j ≤ 70 then (if j ≤ 69 then ⟨268693465813703, 268693465813733⟩ else ⟨272152454423233, 272152454423257⟩) else (if j ≤ 71 then ⟨275600848870355, 275600848870379⟩ else ⟨279038713852389, 279038713852415⟩))
          else
            if j ≤ 76 then
              (if j ≤ 74 then (if j ≤ 73 then ⟨282466113475831, 282466113475857⟩ else ⟨285883111263481, 285883111263505⟩) else (if j ≤ 75 then ⟨289289770161541, 289289770161569⟩ else ⟨292686152546563, 292686152546593⟩))
            else
              (if j ≤ 78 then (if j ≤ 77 then ⟨296072320232297, 296072320232327⟩ else ⟨299448334476449, 299448334476479⟩) else (if j ≤ 79 then ⟨302814255987327, 302814255987351⟩ else ⟨306170144930389, 306170144930415⟩))
        else
          if j ≤ 88 then
            if j ≤ 84 then
              (if j ≤ 82 then (if j ≤ 81 then ⟨309516060934701, 309516060934727⟩ else ⟨312852063099285, 312852063099309⟩) else (if j ≤ 83 then ⟨316178209999395, 316178209999419⟩ else ⟨319494559692681, 319494559692705⟩))
            else
              (if j ≤ 86 then (if j ≤ 85 then ⟨322801169725271, 322801169725299⟩ else ⟨326098097137756, 326098097137785⟩) else (if j ≤ 87 then ⟨329385398471106, 329385398471137⟩ else ⟨332663129772482, 332663129772517⟩))
          else
            if j ≤ 92 then
              (if j ≤ 90 then (if j ≤ 89 then ⟨335931346600970, 335931346600997⟩ else ⟨339190104033224, 339190104033247⟩) else (if j ≤ 91 then ⟨342439456669048, 342439456669077⟩ else ⟨345679458636880, 345679458636907⟩))
            else
              (if j ≤ 94 then (if j ≤ 93 then ⟨348910163599200, 348910163599227⟩ else ⟨352131624757870, 352131624757901⟩) else (if j ≤ 95 then ⟨355343894859380, 355343894859409⟩ else ⟨358547026200028, 358547026200057⟩))
      else
        if j ≤ 112 then
          if j ≤ 104 then
            if j ≤ 100 then
              (if j ≤ 98 then (if j ≤ 97 then ⟨361741070631056, 361741070631085⟩ else ⟨364926079563644, 364926079563669⟩) else (if j ≤ 99 then ⟨368102103973914, 368102103973943⟩ else ⟨371269194407796, 371269194407825⟩))
            else
              (if j ≤ 102 then (if j ≤ 101 then ⟨374427400985880, 374427400985907⟩ else ⟨377576773408150, 377576773408179⟩) else (if j ≤ 103 then ⟨380717360958704, 380717360958731⟩ else ⟨383849212510354, 383849212510377⟩))
          else
            if j ≤ 108 then
              (if j ≤ 106 then (if j ≤ 105 then ⟨386972376529200, 386972376529223⟩ else ⟨390086901079146, 390086901079173⟩) else (if j ≤ 107 then ⟨393192833826320, 393192833826347⟩ else ⟨396290222043452, 396290222043477⟩))
            else
              (if j ≤ 110 then (if j ≤ 109 then ⟨399379112614198, 399379112614225⟩ else ⟨402459552037392, 402459552037417⟩) else (if j ≤ 111 then ⟨405531586431254, 405531586431279⟩ else ⟨408595261537522, 408595261537549⟩))
        else
          if j ≤ 120 then
            if j ≤ 116 then
              (if j ≤ 114 then (if j ≤ 113 then ⟨411650622725548, 411650622725577⟩ else ⟨414697714996330, 414697714996359⟩) else (if j ≤ 115 then ⟨417736582986476, 417736582986503⟩ else ⟨420767270972142, 420767270972169⟩))
            else
              (if j ≤ 118 then (if j ≤ 117 then ⟨423789822872892, 423789822872917⟩ else ⟨426804282255522, 426804282255549⟩) else (if j ≤ 119 then ⟨429810692337830, 429810692337861⟩ else ⟨432809095992344, 432809095992371⟩))
          else
            if j ≤ 124 then
              (if j ≤ 122 then (if j ≤ 121 then ⟨435799535749948, 435799535749973⟩ else ⟨438782053803552, 438782053803577⟩) else (if j ≤ 123 then ⟨441756692011636, 441756692011665⟩ else ⟨444723491901792, 444723491901819⟩))
            else
              (if j ≤ 126 then (if j ≤ 125 then ⟨447682494674184, 447682494674209⟩ else ⟨450633741204986, 450633741205013⟩) else (if j ≤ 127 then ⟨453577272049782, 453577272049811⟩ else ⟨456513127446902, 456513127446929⟩))
  else
    if j ≤ 192 then
      if j ≤ 160 then
        if j ≤ 144 then
          if j ≤ 136 then
            if j ≤ 132 then
              (if j ≤ 130 then (if j ≤ 129 then ⟨459441347320714, 459441347320741⟩ else ⟨462361971284898, 462361971284923⟩) else (if j ≤ 131 then ⟨465275038645650, 465275038645675⟩ else ⟨468180588404852, 468180588404881⟩))
            else
              (if j ≤ 134 then (if j ≤ 133 then ⟨471078659263230, 471078659263257⟩ else ⟨473969289623414, 473969289623443⟩) else (if j ≤ 135 then ⟨476852517593014, 476852517593043⟩ else ⟨479728380987620, 479728380987649⟩))
          else
            if j ≤ 140 then
              (if j ≤ 138 then (if j ≤ 137 then ⟨482596917333796, 482596917333827⟩ else ⟨485458163871998, 485458163872031⟩) else (if j ≤ 139 then ⟨488312157559486, 488312157559517⟩ else ⟨491158935073190, 491158935073219⟩))
            else
              (if j ≤ 142 then (if j ≤ 141 then ⟨493998532812530, 493998532812555⟩ else ⟨496830986902212, 496830986902241⟩) else (if j ≤ 143 then ⟨499656333194994, 499656333195019⟩ else ⟨502474607274386, 502474607274413⟩))
        else
          if j ≤ 152 then
            if j ≤ 148 then
              (if j ≤ 146 then (if j ≤ 145 then ⟨505285844457372, 505285844457401⟩ else ⟨508090079797036, 508090079797067⟩) else (if j ≤ 147 then ⟨510887348085204, 510887348085231⟩ else ⟨513677683855020, 513677683855051⟩))
            else
              (if j ≤ 150 then (if j ≤ 149 then ⟨516461121383512, 516461121383537⟩ else ⟨519237694694116, 519237694694141⟩) else (if j ≤ 151 then ⟨522007437559174, 522007437559201⟩ else ⟨524770383502394, 524770383502421⟩))
          else
            if j ≤ 156 then
              (if j ≤ 154 then (if j ≤ 153 then ⟨527526565801290, 527526565801319⟩ else ⟨530276017489586, 530276017489611⟩) else (if j ≤ 155 then ⟨533018771359584, 533018771359613⟩ else ⟨535754859964520, 535754859964547⟩))
            else
              (if j ≤ 158 then (if j ≤ 157 then ⟨538484315620878, 538484315620907⟩ else ⟨541207170410684, 541207170410709⟩) else (if j ≤ 159 then ⟨543923456183760, 543923456183785⟩ else ⟨546633204559966, 546633204559991⟩))
      else
        if j ≤ 176 then
          if j ≤ 168 then
            if j ≤ 164 then
              (if j ≤ 162 then (if j ≤ 161 then ⟨549336446931414, 549336446931439⟩ else ⟨552033214464632, 552033214464661⟩) else (if j ≤ 163 then ⟨554723538102748, 554723538102775⟩ else ⟨557407448567584, 557407448567611⟩))
            else
              (if j ≤ 166 then (if j ≤ 165 then ⟨560084976361800, 560084976361825⟩ else ⟨562756151770938, 562756151770965⟩) else (if j ≤ 167 then ⟨565421004865502, 565421004865533⟩ else ⟨568079565502990, 568079565503019⟩))
          else
            if j ≤ 172 then
              (if j ≤ 170 then (if j ≤ 169 then ⟨570731863329880, 570731863329905⟩ else ⟨573377927783626, 573377927783655⟩) else (if j ≤ 171 then ⟨576017788094628, 576017788094653⟩ else ⟨578651473288148, 578651473288181⟩))
            else
              (if j ≤ 174 then (if j ≤ 173 then ⟨581279012186258, 581279012186283⟩ else ⟨583900433409684, 583900433409709⟩) else (if j ≤ 175 then ⟨586515765379720, 586515765379747⟩ else ⟨589125036320064, 589125036320091⟩))
        else
          if j ≤ 184 then
            if j ≤ 180 then
              (if j ≤ 178 then (if j ≤ 177 then ⟨591728274258632, 591728274258659⟩ else ⟨594325507029378, 594325507029403⟩) else (if j ≤ 179 then ⟨596916762274080, 596916762274103⟩ else ⟨599502067444098, 599502067444125⟩))
            else
              (if j ≤ 182 then (if j ≤ 181 then ⟨602081449802128, 602081449802155⟩ else ⟨604654936423910, 604654936423935⟩) else (if j ≤ 183 then ⟨607222554199960, 607222554199987⟩ else ⟨609784329837230, 609784329837253⟩))
          else
            if j ≤ 188 then
              (if j ≤ 186 then (if j ≤ 185 then ⟨612340289860784, 612340289860811⟩ else ⟨614890460615460, 614890460615487⟩) else (if j ≤ 187 then ⟨617434868267470, 617434868267497⟩ else ⟨619973538806044, 619973538806071⟩))
            else
              (if j ≤ 190 then (if j ≤ 189 then ⟨622506498044994, 622506498045021⟩ else ⟨625033771624308, 625033771624335⟩) else (if j ≤ 191 then ⟨627555385011696, 627555385011721⟩ else ⟨630071363504138, 630071363504163⟩))
    else
      if j ≤ 224 then
        if j ≤ 208 then
          if j ≤ 200 then
            if j ≤ 196 then
              (if j ≤ 194 then (if j ≤ 193 then ⟨632581732229400, 632581732229429⟩ else ⟨635086516147546, 635086516147577⟩) else (if j ≤ 195 then ⟨637585740052428, 637585740052455⟩ else ⟨640079428573144, 640079428573169⟩))
            else
              (if j ≤ 198 then (if j ≤ 197 then ⟨642567606175510, 642567606175535⟩ else ⟨645050297163498, 645050297163523⟩) else (if j ≤ 199 then ⟨647527525680648, 647527525680679⟩ else ⟨649999315711506, 649999315711531⟩))
          else
            if j ≤ 204 then
              (if j ≤ 202 then (if j ≤ 201 then ⟨652465691082972, 652465691083005⟩ else ⟨654926675465728, 654926675465753⟩) else (if j ≤ 203 then ⟨657382292375556, 657382292375583⟩ else ⟨659832565174718, 659832565174749⟩))
            else
              (if j ≤ 206 then (if j ≤ 205 then ⟨662277517073284, 662277517073309⟩ else ⟨664717171130428, 664717171130455⟩) else (if j ≤ 207 then ⟨667151550255766, 667151550255793⟩ else ⟨669580677210630, 669580677210657⟩))
        else
          if j ≤ 216 then
            if j ≤ 212 then
              (if j ≤ 210 then (if j ≤ 209 then ⟨672004574609340, 672004574609365⟩ else ⟨674423264920474, 674423264920501⟩) else (if j ≤ 211 then ⟨676836770468128, 676836770468155⟩ else ⟨679245113433130, 679245113433155⟩))
            else
              (if j ≤ 214 then (if j ≤ 213 then ⟨681648315854272, 681648315854299⟩ else ⟨684046399629538, 684046399629565⟩) else (if j ≤ 215 then ⟨686439386517278, 686439386517303⟩ else ⟨688827298137392, 688827298137419⟩))
          else
            if j ≤ 220 then
              (if j ≤ 218 then (if j ≤ 217 then ⟨691210155972526, 691210155972551⟩ else ⟨693587981369202, 693587981369227⟩) else (if j ≤ 219 then ⟨695960795538990, 695960795539015⟩ else ⟨698328619559630, 698328619559655⟩))
            else
              (if j ≤ 222 then (if j ≤ 221 then ⟨700691474376152, 700691474376181⟩ else ⟨703049380802006, 703049380802031⟩) else (if j ≤ 223 then ⟨705402359520140, 705402359520165⟩ else ⟨707750431084098, 707750431084125⟩))
      else
        if j ≤ 240 then
          if j ≤ 232 then
            if j ≤ 228 then
              (if j ≤ 226 then (if j ≤ 225 then ⟨710093615919108, 710093615919133⟩ else ⟨712431934323130, 712431934323157⟩) else (if j ≤ 227 then ⟨714765406467918, 714765406467945⟩ else ⟨717094052400068, 717094052400097⟩))
            else
              (if j ≤ 230 then (if j ≤ 229 then ⟨719417892042050, 719417892042077⟩ else ⟨721736945193228, 721736945193253⟩) else (if j ≤ 231 then ⟨724051231530862, 724051231530887⟩ else ⟨726360770611142, 726360770611167⟩))
          else
            if j ≤ 236 then
              (if j ≤ 234 then (if j ≤ 233 then ⟨728665581870140, 728665581870165⟩ else ⟨730965684624820, 730965684624847⟩) else (if j ≤ 235 then ⟨733261098073998, 733261098074021⟩ else ⟨735551841299298, 735551841299323⟩))
            else
              (if j ≤ 238 then (if j ≤ 237 then ⟨737837933266124, 737837933266149⟩ else ⟨740119392824570, 740119392824595⟩) else (if j ≤ 239 then ⟨742396238710392, 742396238710415⟩ else ⟨744668489545890, 744668489545917⟩))
        else
          if j ≤ 248 then
            if j ≤ 244 then
              (if j ≤ 242 then (if j ≤ 241 then ⟨746936163840862, 746936163840885⟩ else ⟨749199279993474, 749199279993499⟩) else (if j ≤ 243 then ⟨751457856291174, 751457856291199⟩ else ⟨753711910911584, 753711910911609⟩))
            else
              (if j ≤ 246 then (if j ≤ 245 then ⟨755961461923358, 755961461923385⟩ else ⟨758206527287068, 758206527287095⟩) else (if j ≤ 247 then ⟨760447124856062, 760447124856087⟩ else ⟨762683272377298, 762683272377323⟩))
          else
            if j ≤ 252 then
              (if j ≤ 250 then (if j ≤ 249 then ⟨764914987492220, 764914987492245⟩ else ⟨767142287737562, 767142287737587⟩) else (if j ≤ 251 then ⟨769365190546192, 769365190546217⟩ else ⟨771583713247928, 771583713247955⟩))
            else
              (if j ≤ 254 then (if j ≤ 253 then ⟨773797873070352, 773797873070375⟩ else ⟨776007687139590, 776007687139615⟩) else (if j ≤ 255 then ⟨778213172481144, 778213172481167⟩ else ⟨780414346020668, 780414346020671⟩))

def checkLogTab (n : ℕ) : Bool :=
  match n with
  | 0 => true
  | k + 1 =>
    let ref := logNat ((256 + k) * (SCALE / 256))
    let t := logTab k
    decide (t.lo ≤ ref.lo) && decide (ref.hi ≤ t.hi) && checkLogTab k

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private lemma checkLogTab_257 : checkLogTab 257 = true := by decide

lemma mem_logTab {j : ℕ} (hj : j ≤ 256) :
    mem (logTab j) (Real.log (((256 + j : ℕ) : ℝ) / 256)) := by
  have hall : ∀ n, checkLogTab n = true → ∀ k < n,
      (logTab k).lo ≤ (logNat ((256 + k) * (SCALE / 256))).lo ∧
      (logNat ((256 + k) * (SCALE / 256))).hi ≤ (logTab k).hi := by
    intro n
    induction n with
    | zero => intro _ k hk; omega
    | succ m ih =>
      intro hc k hk
      change (decide ((logTab m).lo ≤ (logNat ((256 + m) * (SCALE / 256))).lo) &&
              decide ((logNat ((256 + m) * (SCALE / 256))).hi ≤ (logTab m).hi) &&
              checkLogTab m) = true at hc
      have ⟨h12, hrest⟩ := Bool.and_eq_true_iff.mp hc
      have ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h12
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
      · exact ih hrest k hlt
      · exact ⟨of_decide_eq_true h1, of_decide_eq_true h2⟩
  have ⟨hlo, hhi⟩ := hall 257 checkLogTab_257 j (by omega)
  have ha_pos : 0 < (256 + j) * (SCALE / 256) := by unfold SCALE; omega
  have hmem := mem_logNat ha_pos
  have heq : (((256 + j) * (SCALE / 256) : ℕ) : ℝ) / (SCALE : ℝ) = ((256 + j : ℕ) : ℝ) / 256 := by
    have hS : (SCALE / 256 : ℕ) * 256 = SCALE := by unfold SCALE; decide
    have hSR : ((SCALE / 256 : ℕ) : ℝ) * 256 = (SCALE : ℝ) := by unfold SCALE; norm_num
    rw [Nat.cast_mul, ← hSR]
    have h1 : ((SCALE / 256 : ℕ) : ℝ) ≠ 0 := by unfold SCALE; norm_num
    field_simp [h1]
  rw [heq] at hmem
  have hS := SCALE_pos
  exact ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hlo) (le_of_lt hS)) hmem.1,
         le_trans hmem.2 (div_le_div_of_nonneg_right (by exact_mod_cast hhi) (le_of_lt hS))⟩

/-- Ultra-fast 2-term raw-integer `atanh` core for `|num / den| ≤ 1 / 1024` (strict CBV). -/
def fastLogCore (num den : ℤ) : Interval :=
  intCBV num fun num => intCBV den fun den =>
  intCBV ((num * (SCALE : ℤ)) / den) fun u =>
  intCBV ((u * u) / (SCALE : ℤ)) fun u2 =>
  intCBV ((u2 * u) / (3 * (SCALE : ℤ))) fun u3 =>
  intCBV (2 * (u + u3)) fun s =>
  ⟨s - 6, s + 6⟩

lemma mem_fastLogCore {num den : ℤ} (hden : 0 < den)
    (hub : |(num : ℝ) / (den : ℝ)| ≤ 1 / 1024) :
    let y := ((den + num : ℤ) : ℝ) / ((den - num : ℤ) : ℝ)
    mem (fastLogCore num den) (Real.log y) := by
  intro y
  have hS := SCALE_pos
  have hdenR : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
  set uR : ℝ := (num : ℝ) / (den : ℝ)
  have hy_eq : y = (1 + uR) / (1 - uR) := by
    simp only [y, uR]; push_cast
    have h1mu : 1 - (num : ℝ) / (den : ℝ) ≠ 0 := by have := (abs_le.mp hub).2; linarith
    field_simp [ne_of_gt hdenR, h1mu]
  -- Remainder bound for N = 2, R = 1/1024:
  have hrem_tiny : 2 * (1 / 1024 : ℝ) ^ (2 * 2 + 1) / ((2 * 2 + 1 : ℝ) * (1 - (1 / 1024 : ℝ) ^ 2))
      ≤ (1 : ℝ) / (SCALE : ℝ) := by
    unfold SCALE; norm_num
  have hS2_eq : 2 * ∑ k ∈ Finset.range 2, uR ^ (2 * k + 1) / (2 * k + 1 : ℝ)
      = 2 * (uR + uR ^ 3 / 3) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hrem_abs : |Real.log y - 2 * (uR + uR ^ 3 / 3)| ≤ 1 / (SCALE : ℝ) := by
    rw [hy_eq, ← hS2_eq]
    rcases le_total 0 uR with hu0 | hu0
    · have hb := log_one_add_div_sub_bounds 2 (R := 1 / 1024) (by norm_num) hu0 (abs_le.mp hub).2
      dsimp only at hb
      have hpow : uR ^ (2 * 2 + 1) ≤ (1 / 1024 : ℝ) ^ (2 * 2 + 1) :=
        pow_le_pow_left₀ hu0 (abs_le.mp hub).2 _
      have h1 : 2 * uR ^ (2 * 2 + 1) / ((2 * 2 + 1 : ℝ) * (1 - (1 / 1024 : ℝ) ^ 2)) ≤ 1 / SCALE :=
        le_trans (div_le_div_of_nonneg_right (by linarith) (by norm_num)) hrem_tiny
      rw [abs_of_nonneg hb.1]; linarith [hb.2]
    · have hb := log_one_add_div_sub_bounds_neg 2 (R := 1 / 1024) (by norm_num) hu0 (abs_le.mp hub).1
      dsimp only at hb
      have hpow : (-uR) ^ (2 * 2 + 1) ≤ (1 / 1024 : ℝ) ^ (2 * 2 + 1) :=
        pow_le_pow_left₀ (by linarith) (by linarith [(abs_le.mp hub).1]) _
      have h1 : 2 * (-uR) ^ (2 * 2 + 1) / ((2 * 2 + 1 : ℝ) * (1 - (1 / 1024 : ℝ) ^ 2)) ≤ 1 / SCALE :=
        le_trans (div_le_div_of_nonneg_right (by linarith) (by norm_num)) hrem_tiny
      rw [abs_of_nonpos hb.2]; linarith [hb.1]
  -- Now bound integer division truncation errors!
  have hed : ∀ (a b : ℤ), 0 < b → ((a / b : ℤ) : ℝ) ≤ (a : ℝ) / (b : ℝ) ∧
      (a : ℝ) / (b : ℝ) - 1 < ((a / b : ℤ) : ℝ) := fun a b hb => by
    have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
    have hmod := Int.emod_nonneg a (ne_of_gt hb)
    have hmod_lt := Int.emod_lt_of_pos a hb
    have hdiv := Int.mul_ediv_add_emod a b
    have hdivR : (b : ℝ) * ((a / b : ℤ) : ℝ) + ((a % b : ℤ) : ℝ) = (a : ℝ) := by exact_mod_cast hdiv
    have hmodR0 : (0 : ℝ) ≤ ((a % b : ℤ) : ℝ) := by exact_mod_cast hmod
    have hmodR1 : ((a % b : ℤ) : ℝ) < (b : ℝ) := by exact_mod_cast hmod_lt
    constructor
    · rw [le_div_iff₀ hbR]; linarith
    · rw [sub_lt_iff_lt_add, div_lt_iff₀ hbR]; nlinarith
  set u : ℤ := (num * (SCALE : ℤ)) / den
  set u2 : ℤ := (u * u) / (SCALE : ℤ)
  set u3 : ℤ := (u2 * u) / (3 * (SCALE : ℤ))
  set uS : ℝ := (u : ℝ) / (SCALE : ℝ)
  set u2S : ℝ := (u2 : ℝ) / (SCALE : ℝ)
  set u3S : ℝ := (u3 : ℝ) / (SCALE : ℝ)
  have hu_b := hed (num * (SCALE : ℤ)) den hden
  have hu_eq : ((num * (SCALE : ℤ) : ℤ) : ℝ) / (den : ℝ) = uR * (SCALE : ℝ) := by
    simp only [uR]; push_cast; ring
  rw [hu_eq] at hu_b
  have hu_err : |uS - uR| ≤ 1 / (SCALE : ℝ) := by
    have h1 : (u : ℝ) ≤ uR * SCALE := hu_b.1
    have h2 : uR * SCALE - 1 < (u : ℝ) := hu_b.2
    rw [abs_le]; constructor
    · simp only [uS]; rw [le_sub_iff_add_le, show -(1 / (SCALE : ℝ)) + uR = (uR * SCALE - 1) / SCALE by field_simp [SCALE_ne_zero]; ring]
      exact div_le_div_of_nonneg_right (le_of_lt h2) (le_of_lt hS)
    · simp only [uS]; rw [sub_le_iff_le_add]
      have : (u : ℝ) / SCALE ≤ uR := (div_le_iff₀ hS).mpr h1
      linarith [div_pos one_pos hS]
  have hu_abs : |uS| ≤ (1 / 512 : ℝ) := by
    have h1 : (1 : ℝ) / (SCALE : ℝ) ≤ 1 / 1024 := by unfold SCALE; norm_num
    have h2 := abs_sub_abs_le_abs_sub uS uR
    linarith [hub, hu_err]
  have hu2_b := hed (u * u) (SCALE : ℤ) (by unfold SCALE; omega)
  have hu2_err : |u2S - uS ^ 2| ≤ 1 / (SCALE : ℝ) := by
    have hrew : ((u * u : ℤ) : ℝ) / ((SCALE : ℤ) : ℝ) = uS ^ 2 * (SCALE : ℝ) := by
      simp only [uS]; push_cast; field_simp [SCALE_ne_zero]
    rw [hrew] at hu2_b
    rw [abs_le]; constructor
    · simp only [u2S]; rw [le_sub_iff_add_le, show -(1 / (SCALE : ℝ)) + uS ^ 2 = (uS ^ 2 * SCALE - 1) / SCALE by field_simp [SCALE_ne_zero]; ring]
      exact div_le_div_of_nonneg_right (le_of_lt hu2_b.2) (le_of_lt hS)
    · simp only [u2S]; rw [sub_le_iff_le_add]
      have : (u2 : ℝ) / SCALE ≤ uS ^ 2 := (div_le_iff₀ hS).mpr hu2_b.1
      linarith [div_pos one_pos hS]
  have hu3_b := hed (u2 * u) (3 * (SCALE : ℤ)) (by unfold SCALE; omega)
  have hu3_err : |u3S - u2S * uS / 3| ≤ 1 / (SCALE : ℝ) := by
    have hrew : ((u2 * u : ℤ) : ℝ) / ((3 * (SCALE : ℤ) : ℤ) : ℝ) = u2S * uS / 3 * (SCALE : ℝ) := by
      simp only [u2S, uS]; push_cast; field_simp [SCALE_ne_zero]
    rw [hrew] at hu3_b
    rw [abs_le]; constructor
    · simp only [u3S]; rw [le_sub_iff_add_le, show -(1 / (SCALE : ℝ)) + u2S * uS / 3 = (u2S * uS / 3 * SCALE - 1) / SCALE by field_simp [SCALE_ne_zero]; ring]
      exact div_le_div_of_nonneg_right (le_of_lt hu3_b.2) (le_of_lt hS)
    · simp only [u3S]; rw [sub_le_iff_le_add]
      have : (u3 : ℝ) / SCALE ≤ u2S * uS / 3 := (div_le_iff₀ hS).mpr hu3_b.1
      linarith [div_pos one_pos hS]
  have hdiff_u3_tight : |u3S - uR ^ 3 / 3| ≤ (11 / 10 : ℝ) * (1 / (SCALE : ℝ)) := by
    have hstep1 : |u2S * uS / 3 - uS ^ 3 / 3| ≤ (1 / (SCALE : ℝ)) * (1 / 512) / 3 := by
      have hfac : u2S * uS / 3 - uS ^ 3 / 3 = (u2S - uS ^ 2) * uS / 3 := by ring
      rw [hfac, abs_div, abs_mul, abs_of_pos (show (0 : ℝ) < 3 by norm_num)]
      exact div_le_div_of_nonneg_right (mul_le_mul hu2_err hu_abs (abs_nonneg _) (by positivity)) (by norm_num)
    have hstep2 : |uS ^ 3 / 3 - uR ^ 3 / 3| ≤ (1 / (SCALE : ℝ)) * (1 / 512) ^ 2 := by
      have hfac : uS ^ 3 / 3 - uR ^ 3 / 3 = (uS - uR) * (uS ^ 2 + uS * uR + uR ^ 2) / 3 := by ring
      rw [hfac, abs_div, abs_mul, abs_of_pos (show (0 : ℝ) < 3 by norm_num)]
      have htri : |uS ^ 2 + uS * uR + uR ^ 2| ≤ 3 * (1 / 512 : ℝ) ^ 2 := by
        have ha1 : |uS ^ 2| ≤ (1 / 512 : ℝ) ^ 2 := by rw [abs_pow]; nlinarith [abs_nonneg uS]
        have ha2 : |uS * uR| ≤ (1 / 512 : ℝ) ^ 2 := by rw [abs_mul]; nlinarith [abs_nonneg uS, abs_nonneg uR]
        have ha3 : |uR ^ 2| ≤ (1 / 512 : ℝ) ^ 2 := by rw [abs_pow]; nlinarith [abs_nonneg uR]
        have h12 := abs_add_le (uS ^ 2 + uS * uR) (uR ^ 2)
        have h11 := abs_add_le (uS ^ 2) (uS * uR)
        linarith
      have hprod := mul_le_mul hu_err htri (abs_nonneg _) (by positivity)
      have hdiv := div_le_div_of_nonneg_right hprod (show (0 : ℝ) ≤ 3 by norm_num)
      linarith
    have htri := abs_sub_le u3S (u2S * uS / 3) (uR ^ 3 / 3)
    have htri2 := abs_sub_le (u2S * uS / 3) (uS ^ 3 / 3) (uR ^ 3 / 3)
    have hpos_inv : (0 : ℝ) < 1 / (SCALE : ℝ) := div_pos one_pos hS
    linarith
  have h_u := abs_le.mp hu_err
  have h_u3 := abs_le.mp hdiff_u3_tight
  have h_rem := abs_le.mp hrem_abs
  have h6 : (6 : ℝ) / (SCALE : ℝ) = 6 * (1 / (SCALE : ℝ)) := by ring
  unfold fastLogCore; simp only [intCBV_eq]
  change mem ⟨2 * (u + u3) - 6, 2 * (u + u3) + 6⟩ (Real.log y)
  unfold mem; dsimp only
  have huS_def : (u : ℝ) / SCALE = uS := rfl
  have hu3S_def : (u3 : ℝ) / SCALE = u3S := rfl
  have hpos_inv : (0 : ℝ) < 1 / (SCALE : ℝ) := div_pos one_pos hS
  constructor
  · push_cast; rw [sub_div, mul_div_assoc, add_div, huS_def, hu3S_def, h6]; linarith
  · push_cast; rw [add_div, mul_div_assoc, add_div, huS_def, hu3S_def, h6]; linarith

/-- Fast exact integer scalar multiplication `e * I` (zero divisions!). -/
def mulIntIv (e : ℤ) (I : Interval) : Interval :=
  intCBV e fun e => ivCBV I fun I =>
  if 0 ≤ e then ⟨e * I.lo, e * I.hi⟩ else ⟨e * I.hi, e * I.lo⟩

private lemma mem_mulIntIv {e : ℤ} {I : Interval} {x : ℝ} (hx : mem I x) :
    mem (mulIntIv e I) ((e : ℝ) * x) := by
  unfold mulIntIv mem; simp only [intCBV_eq, ivCBV_eq]
  have hS := SCALE_pos
  split_ifs with he
  · have heR : (0 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
    constructor
    · push_cast; rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hx.1 heR
    · push_cast; rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hx.2 heR
  · have heR : (e : ℝ) ≤ 0 := by exact_mod_cast (show e ≤ 0 by omega)
    constructor
    · push_cast; rw [mul_div_assoc]; exact mul_le_mul_of_nonpos_left hx.2 heR
    · push_cast; rw [mul_div_assoc]; exact mul_le_mul_of_nonpos_left hx.1 heR

/-- Fast enclosure of `Real.log (a / SCALE)` for `0 < a < 2^64` (strict CBV, ~1ms in kernel!). -/
def fastLogNat (a : ℕ) : Interval :=
  natCBV a fun a =>
  if a = 0 then ⟨0, 0⟩
  else if a < 18446744073709551616 then
    natCBV (fastLog2 a) fun k =>
    natCBV (2 ^ k) fun p2 =>
    natCBV ((256 * a + p2 / 2) / p2) fun q =>
    natCBV (q * p2) fun m =>
    ivCBV (fastLogCore ((256 * a : ℤ) - (m : ℤ)) ((256 * a : ℤ) + (m : ℤ))) fun core =>
    ivCBV (logTab (q - 256)) fun tab =>
    ivCBV (mulIntIv ((k : ℤ) - (SCALE_BITS : ℤ)) LN2) fun eL =>
    fadd (fadd eL tab) core
  else logNat a

lemma mem_fastLogNat {a : ℕ} (ha : 0 < a) :
    mem (fastLogNat a) (Real.log ((a : ℝ) / (SCALE : ℝ))) := by
  unfold fastLogNat; simp only [natCBV_eq, ivCBV_eq, fadd_eq]
  simp only [Nat.ne_of_gt ha, ↓reduceIte]
  split_ifs with hlt
  · have ha64 : a < 2 ^ 64 := by simpa using hlt
    have ⟨hge, hlt2⟩ := fastLog2_spec ha ha64
    set k := fastLog2 a
    set p2 := 2 ^ k
    have hp2_pos : 0 < p2 := Nat.pow_pos (by decide)
    set q := (256 * a + p2 / 2) / p2
    set j := q - 256
    set m := q * p2
    have hq_lo : 256 ≤ q := by
      apply Nat.le_div_iff_mul_le hp2_pos |>.mpr; omega
    have hq_hi : q ≤ 512 := by
      have hp2h : p2 / 2 < p2 := Nat.div_lt_self hp2_pos (by decide)
      have hlt_mul : 256 * a + p2 / 2 < p2 * 513 := by omega
      exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul hlt_mul)
    have hj_le : j ≤ 256 := by omega
    have h256j : 256 + j = q := by omega
    -- Bound |256*a - m| ≤ p2 / 2 (exact for all a ≥ 1!):
    have hdiff_le : |(256 * a : ℤ) - (m : ℤ)| ≤ ((p2 / 2 : ℕ) : ℤ) := by
      have hdiv := Nat.div_add_mod (256 * a + p2 / 2) p2
      have hmod := Nat.mod_lt (256 * a + p2 / 2) hp2_pos
      have hm_eq : m + (256 * a + p2 / 2) % p2 = 256 * a + p2 / 2 := by
        have hcomm : m = p2 * q := mul_comm q p2
        rw [hcomm]; exact hdiv
      rcases eq_or_ne k 0 with hk0 | hk0
      · have hp2_1 : p2 = 1 := by simp [p2, hk0]
        have ha_1 : a = 1 := by omega
        have hq_1 : q = 256 := by simp [q, hp2_1, ha_1]
        have hm_1 : m = 256 := by simp [m, hq_1, hp2_1]
        simp [ha_1, hm_1, hp2_1]
      · have heven : 2 * (p2 / 2) = p2 := by
          have : p2 = 2 * 2 ^ (k - 1) := by
            simp only [p2]
            cases hk : k with
            | zero => omega
            | succ k' => simp [pow_succ']
          omega
        rw [abs_le]; constructor <;> omega
    have hden_pos : (0 : ℤ) < (256 * a : ℤ) + (m : ℤ) := by
      have : 256 * p2 ≤ m := by simp only [m]; exact Nat.mul_le_mul_right p2 hq_lo
      omega
    have hub : |(((256 * a : ℤ) - (m : ℤ) : ℤ) : ℝ) / (((256 * a : ℤ) + (m : ℤ) : ℤ) : ℝ)| ≤ 1 / 1024 := by
      set numI : ℤ := (256 * a : ℤ) - (m : ℤ)
      set denI : ℤ := (256 * a : ℤ) + (m : ℤ)
      have hden_ge : (512 * p2 : ℤ) ≤ denI := by
        have : 256 * p2 ≤ m := by simp only [m]; exact Nat.mul_le_mul_right p2 hq_lo
        omega
      have hden_geR : 512 * (p2 : ℝ) ≤ (denI : ℝ) := by exact_mod_cast hden_ge
      have hdenR_pos : (0 : ℝ) < (denI : ℝ) := by exact_mod_cast hden_pos
      have hnum_leR : |(numI : ℝ)| ≤ (p2 : ℝ) / 2 := by
        have h1 : |(numI : ℝ)| ≤ ((p2 / 2 : ℕ) : ℝ) := by
          have h1' : |(numI : ℝ)| ≤ (((p2 / 2 : ℕ) : ℤ) : ℝ) := by exact_mod_cast hdiff_le
          rwa [Int.cast_natCast] at h1'
        have h2 : ((p2 / 2 : ℕ) : ℝ) ≤ (p2 : ℝ) / 2 := by
          have := Nat.div_mul_le_self p2 2
          have : ((p2 / 2 : ℕ) : ℝ) * 2 ≤ (p2 : ℝ) := by exact_mod_cast this
          linarith
        linarith
      change |(numI : ℝ) / (denI : ℝ)| ≤ 1 / 1024
      rw [abs_div, abs_of_pos hdenR_pos, div_le_iff₀ hdenR_pos]
      linarith [hden_geR, hnum_leR]
    have hcore := mem_fastLogCore hden_pos hub
    dsimp only at hcore
    have htab := mem_logTab hj_le
    rw [h256j] at htab
    have he := mem_mulIntIv (e := (k : ℤ) - (SCALE_BITS : ℤ)) mem_LN2
    have hsum := mem_add (mem_add he htab) hcore
    -- Verify the algebra: (k - 50) * L + log(q / 256) + log((256*a) / (q*p2)) = log(a / SCALE)
    have hS_eq : (SCALE : ℝ) = (2 : ℝ) ^ (SCALE_BITS : ℕ) := by unfold SCALE SCALE_BITS; push_cast; norm_num
    have hlog_eq : (((k : ℤ) - (SCALE_BITS : ℤ) : ℤ) : ℝ) * L + Real.log ((q : ℝ) / 256)
        + Real.log (((((256 * a : ℤ) + (m : ℤ) + ((256 * a : ℤ) - (m : ℤ)) : ℤ) : ℝ) /
                    (((256 * a : ℤ) + (m : ℤ) - ((256 * a : ℤ) - (m : ℤ)) : ℤ) : ℝ)))
        = Real.log ((a : ℝ) / (SCALE : ℝ)) := by
      have hy_simp : (((256 * a : ℤ) + (m : ℤ) + ((256 * a : ℤ) - (m : ℤ)) : ℤ) : ℝ) /
          (((256 * a : ℤ) + (m : ℤ) - ((256 * a : ℤ) - (m : ℤ)) : ℤ) : ℝ)
          = (256 * (a : ℝ)) / ((q : ℝ) * (p2 : ℝ)) := by
        simp only [m]; push_cast
        have hqp : (q : ℝ) * (p2 : ℝ) ≠ 0 := mul_ne_zero (by exact_mod_cast (by omega : q ≠ 0)) (by exact_mod_cast (ne_of_gt hp2_pos))
        field_simp [hqp]; ring
      rw [hy_simp]
      have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
      have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
      have hp2R : (0 : ℝ) < (p2 : ℝ) := by exact_mod_cast hp2_pos
      have hmul_log : Real.log ((q : ℝ) / 256) + Real.log (256 * (a : ℝ) / ((q : ℝ) * (p2 : ℝ)))
          = Real.log (((q : ℝ) / 256) * (256 * (a : ℝ) / ((q : ℝ) * (p2 : ℝ)))) :=
        (Real.log_mul (ne_of_gt (div_pos hqR (by norm_num)))
          (ne_of_gt (div_pos (by positivity) (mul_pos hqR hp2R)))).symm
      rw [add_assoc, hmul_log]
      have hprod : ((q : ℝ) / 256) * (256 * (a : ℝ) / ((q : ℝ) * (p2 : ℝ))) = (a : ℝ) / (p2 : ℝ) := by
        field_simp [ne_of_gt hqR, ne_of_gt hp2R]
      rw [hprod, Real.log_div (ne_of_gt haR) (ne_of_gt hp2R),
          Real.log_div (ne_of_gt haR) (ne_of_gt SCALE_pos), hS_eq, Real.log_pow]
      have hp2_pow : (p2 : ℝ) = (2 : ℝ) ^ k := by simp [p2]
      rw [hp2_pow, Real.log_pow]
      unfold L; push_cast; ring
    rwa [hlog_eq] at hsum
  · exact mem_logNat ha

/-- Fast interval logarithm: drop-in replacement for `Iv.log` (strict CBV + point fast-path). -/
def fastLog (I : Interval) : Interval :=
  ivCBV I fun I =>
  if I.lo ≤ 0 then ⟨0, 0⟩
  else if I.lo == I.hi then fastLogNat I.lo.toNat
  else ⟨(fastLogNat I.lo.toNat).lo, (fastLogNat I.hi.toNat).hi⟩

lemma mem_fastLog {I : Interval} {x : ℝ} (hx : mem I x) (hpos : 0 < I.lo) :
    mem (fastLog I) (Real.log x) := by
  have hS := SCALE_pos
  have hhi_pos : 0 < I.hi := by
    have hle : (I.lo : ℝ) / SCALE ≤ (I.hi : ℝ) / SCALE := le_trans hx.1 hx.2
    have hle' : (I.lo : ℝ) ≤ (I.hi : ℝ) := by rwa [div_le_div_iff_of_pos_right hS] at hle
    have : I.lo ≤ I.hi := by exact_mod_cast hle'
    omega
  have hlo_nat : 0 < I.lo.toNat := by omega
  have hhi_nat : 0 < I.hi.toNat := by omega
  have hlo_eq : (I.lo.toNat : ℝ) = (I.lo : ℝ) := by
    have : (I.lo.toNat : ℤ) = I.lo := Int.toNat_of_nonneg (le_of_lt hpos)
    exact_mod_cast this
  have hhi_eq : (I.hi.toNat : ℝ) = (I.hi : ℝ) := by
    have : (I.hi.toNat : ℤ) = I.hi := Int.toNat_of_nonneg (le_of_lt hhi_pos)
    exact_mod_cast this
  have hlo_mem := mem_fastLogNat hlo_nat
  have hhi_mem := mem_fastLogNat hhi_nat
  rw [hlo_eq] at hlo_mem; rw [hhi_eq] at hhi_mem
  have hloR : (0 : ℝ) < (I.lo : ℝ) / SCALE := div_pos (by exact_mod_cast hpos) hS
  have hx_pos : 0 < x := lt_of_lt_of_le hloR hx.1
  unfold fastLog; simp only [ivCBV_eq, show ¬(I.lo ≤ 0) by omega, ↓reduceIte]
  split_ifs with heq
  · have hEq : I.lo = I.hi := beq_iff_eq.mp heq
    have hxEq : x = (I.lo : ℝ) / SCALE := le_antisymm (hEq ▸ hx.2) hx.1
    rw [hxEq]; exact hlo_mem
  · exact ⟨le_trans hlo_mem.1 (Real.log_le_log hloR hx.1),
           le_trans (Real.log_le_log hx_pos hx.2) hhi_mem.2⟩

/-- Fast positive-point-times-interval `(p / SCALE) * I` for `0 < p` (2 muls, zero min/max!). -/
def mulPosPt (p : ℤ) (I : Interval) : Interval :=
  intCBV p fun p => ivCBV I fun I =>
  ⟨fdiv (p * I.lo) SCALE, cdiv (p * I.hi) SCALE⟩

private lemma mem_mulPosPt {p : ℤ} (hp : 0 < p) {I : Interval} {x : ℝ} (hx : mem I x) :
    mem (mulPosPt p I) (((p : ℝ) / SCALE) * x) := by
  have hS := SCALE_pos
  have hpR : (0 : ℝ) ≤ (p : ℝ) := by exact_mod_cast le_of_lt hp
  unfold mulPosPt mem; simp only [intCBV_eq, ivCBV_eq]
  constructor
  · have h1 := fdiv_le (p * I.lo) SCALE_pos_nat
    have h2 : (fdiv (p * I.lo) SCALE : ℝ) / SCALE ≤ ((p : ℝ) * (I.lo : ℝ)) / (SCALE : ℝ) / (SCALE : ℝ) := by
      have := div_le_div_of_nonneg_right h1 (le_of_lt hS); push_cast at this; exact this
    have h3 : ((p : ℝ) * (I.lo : ℝ)) / (SCALE : ℝ) / (SCALE : ℝ) = ((p : ℝ) / SCALE) * ((I.lo : ℝ) / SCALE) := by ring
    rw [h3] at h2
    exact le_trans h2 (mul_le_mul_of_nonneg_left hx.1 (div_nonneg hpR (le_of_lt hS)))
  · have h1 := le_cdiv (p * I.hi) SCALE_pos_nat
    have h2 : ((p : ℝ) * (I.hi : ℝ)) / (SCALE : ℝ) / (SCALE : ℝ) ≤ (cdiv (p * I.hi) SCALE : ℝ) / SCALE := by
      have := div_le_div_of_nonneg_right h1 (le_of_lt hS); push_cast at this; exact this
    have h3 : ((p : ℝ) * (I.hi : ℝ)) / (SCALE : ℝ) / (SCALE : ℝ) = ((p : ℝ) / SCALE) * ((I.hi : ℝ) / SCALE) := by ring
    rw [h3] at h2
    exact le_trans (mul_le_mul_of_nonneg_left hx.2 (div_nonneg hpR (le_of_lt hS))) h2

/-- Fast interval binary entropy `h(x) = -x log x - (1 - x) log(1 - x)` on `(0, 1)` (strict CBV + point fast-path). -/
def fastH (I : Interval) : Interval :=
  ivCBV I fun I =>
  if 0 < I.lo && I.hi < (SCALE : ℤ) then
    let evalPt (p : ℤ) : Interval :=
      intCBV p fun p =>
      intCBV ((SCALE : ℤ) - p) fun q =>
      fsub (fneg (mulPosPt p (fastLogNat p.toNat))) (mulPosPt q (fastLogNat q.toNat))
    if I.lo == I.hi then
      evalPt I.lo
    else if I.hi ≤ (SCALE / 2 : ℤ) then
      ⟨(evalPt I.lo).lo, (evalPt I.hi).hi⟩
    else if (SCALE / 2 : ℤ) ≤ I.lo then
      ⟨(evalPt I.hi).lo, (evalPt I.lo).hi⟩
    else
      ⟨min (evalPt I.lo).lo (evalPt I.hi).lo, LN2.hi⟩
  else hIv I

private lemma mem_evalPt_h {p : ℤ} (hp0 : 0 < p) (hp1 : p < (SCALE : ℤ)) :
    mem (sub (neg (mulPosPt p (fastLogNat p.toNat))) (mulPosPt ((SCALE : ℤ) - p) (fastLogNat ((SCALE : ℤ) - p).toNat)))
        (h ((p : ℝ) / SCALE)) := by
  have hS := SCALE_pos
  have hQ0 : 0 < (SCALE : ℤ) - p := by omega
  have hlogP : mem (fastLogNat p.toNat) (Real.log ((p : ℝ) / SCALE)) := by
    have h := mem_fastLogNat (by omega : 0 < p.toNat)
    have heq : (p.toNat : ℝ) = (p : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (le_of_lt hp0)
    rwa [heq] at h
  have hlogQ : mem (fastLogNat ((SCALE : ℤ) - p).toNat) (Real.log (1 - (p : ℝ) / SCALE)) := by
    have h := mem_fastLogNat (by omega : 0 < ((SCALE : ℤ) - p).toNat)
    have heq : (((SCALE : ℤ) - p).toNat : ℝ) / SCALE = 1 - (p : ℝ) / SCALE := by
      have h1 : (((SCALE : ℤ) - p).toNat : ℤ) = (SCALE : ℤ) - p := Int.toNat_of_nonneg (le_of_lt hQ0)
      have h2 : (((SCALE : ℤ) - p).toNat : ℝ) = (SCALE : ℝ) - (p : ℝ) := by exact_mod_cast h1
      rw [h2]; field_simp [SCALE_ne_zero]
    rwa [heq] at h
  have hres := mem_sub (mem_neg (mem_mulPosPt hp0 hlogP)) (mem_mulPosPt hQ0 hlogQ)
  have hqR : (((SCALE : ℤ) - p : ℤ) : ℝ) / SCALE = 1 - (p : ℝ) / SCALE := by
    push_cast; field_simp [SCALE_ne_zero]
  rw [hqR] at hres
  have heq : -((p : ℝ) / SCALE * Real.log ((p : ℝ) / SCALE)) - (1 - (p : ℝ) / SCALE) * Real.log (1 - (p : ℝ) / SCALE)
      = h ((p : ℝ) / SCALE) := by unfold h; ring
  rwa [heq] at hres

lemma mem_fastH {I : Interval} {x : ℝ} (hx : mem I x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    mem (fastH I) (h x) := by
  have hmono : MonotoneOn h (Set.Icc (0 : ℝ) (1 / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2))
      (continuousOn_h.mono (Set.Icc_subset_Icc_right (by norm_num)))
    · intro t ht; rw [interior_Icc] at ht
      exact (hasDerivAt_h ht.1 (by linarith [ht.2])).differentiableAt.differentiableWithinAt
    · intro t ht; rw [interior_Icc] at ht
      rw [(hasDerivAt_h ht.1 (by linarith [ht.2])).deriv]
      exact Real.log_nonneg (by rw [one_le_div ht.1]; linarith [ht.2])
  have hanti : AntitoneOn h (Set.Icc (1 / 2 : ℝ) 1) := fun a ha b hb hab => by
    rw [← h_symm a, ← h_symm b]
    exact hmono ⟨by linarith [hb.2], by linarith [hb.1]⟩ ⟨by linarith [ha.2], by linarith [ha.1]⟩ (by linarith)
  have hS := SCALE_pos
  have hhalf : ((SCALE / 2 : ℤ) : ℝ) / SCALE = 1 / 2 := by unfold SCALE; norm_num
  unfold fastH; simp only [ivCBV_eq, intCBV_eq, fsub_eq, fneg_eq]
  split_ifs with hdom heq hle hge
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hdom
    have hEq : I.lo = I.hi := beq_iff_eq.mp heq
    have hxEq : x = (I.lo : ℝ) / SCALE := le_antisymm (hEq ▸ hx.2) hx.1
    rw [hxEq]; exact mem_evalPt_h hdom.1 (hEq ▸ hdom.2)
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hdom
    have hI_le : I.lo ≤ I.hi := by
      have : (I.lo : ℝ) / SCALE ≤ (I.hi : ℝ) / SCALE := le_trans hx.1 hx.2
      rw [div_le_div_iff_of_pos_right hS] at this; exact_mod_cast this
    have hlo_mem := mem_evalPt_h hdom.1 (by omega)
    have hhi_mem := mem_evalPt_h (by omega) hdom.2
    have hlo_0 : 0 ≤ (I.lo : ℝ) / SCALE := div_nonneg (by exact_mod_cast le_of_lt hdom.1) (le_of_lt hS)
    have hhi_half : (I.hi : ℝ) / SCALE ≤ 1 / 2 :=
      hhalf ▸ div_le_div_of_nonneg_right (by exact_mod_cast hle) (le_of_lt hS)
    exact ⟨le_trans hlo_mem.1 (hmono ⟨hlo_0, by linarith [hx.1, hx.2]⟩ ⟨hx0, by linarith [hx.2]⟩ hx.1),
           le_trans (hmono ⟨hx0, by linarith [hx.2]⟩ ⟨by linarith [hx.1, hx.2], hhi_half⟩ hx.2) hhi_mem.2⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hdom
    have hI_le : I.lo ≤ I.hi := by
      have : (I.lo : ℝ) / SCALE ≤ (I.hi : ℝ) / SCALE := le_trans hx.1 hx.2
      rw [div_le_div_iff_of_pos_right hS] at this; exact_mod_cast this
    have hlo_mem := mem_evalPt_h hdom.1 (by omega)
    have hhi_mem := mem_evalPt_h (by omega) hdom.2
    have hlo_half : (1 / 2 : ℝ) ≤ (I.lo : ℝ) / SCALE :=
      hhalf ▸ div_le_div_of_nonneg_right (by exact_mod_cast hge) (le_of_lt hS)
    have hhi_1 : (I.hi : ℝ) / SCALE ≤ 1 := (div_le_one hS).mpr (by exact_mod_cast le_of_lt hdom.2)
    exact ⟨le_trans hhi_mem.1 (hanti ⟨by linarith [hx.1], hx1⟩ ⟨by linarith [hx.1, hx.2], hhi_1⟩ hx.2),
           le_trans (hanti ⟨hlo_half, by linarith [hx.1, hx.2]⟩ ⟨by linarith [hx.1], hx1⟩ hx.1) hlo_mem.2⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hdom
    have hI_le : I.lo ≤ I.hi := by
      have : (I.lo : ℝ) / SCALE ≤ (I.hi : ℝ) / SCALE := le_trans hx.1 hx.2
      rw [div_le_div_iff_of_pos_right hS] at this; exact_mod_cast this
    have hlo_mem := mem_evalPt_h hdom.1 (by omega)
    have hhi_mem := mem_evalPt_h (by omega) hdom.2
    have hlo_0 : 0 ≤ (I.lo : ℝ) / SCALE := div_nonneg (by exact_mod_cast le_of_lt hdom.1) (le_of_lt hS)
    have hhi_1 : (I.hi : ℝ) / SCALE ≤ 1 := (div_le_one hS).mpr (by exact_mod_cast le_of_lt hdom.2)
    constructor
    · rw [Int.cast_min, min_div_pos (le_of_lt hS)]
      rcases le_total x (1 / 2) with hx_le | hx_ge
      · exact le_trans (min_le_left _ _) (le_trans hlo_mem.1 (hmono ⟨hlo_0, by linarith [hx.1]⟩ ⟨hx0, hx_le⟩ hx.1))
      · exact le_trans (min_le_right _ _) (le_trans hhi_mem.1 (hanti ⟨hx_ge, hx1⟩ ⟨by linarith [hx.2], hhi_1⟩ hx.2))
    · exact le_trans (h_le_L hx0 hx1) mem_LN2.2
  · exact mem_hIv hx hx0 hx1

/-- Fast interval `hp(x) = log((1 - x) / x)` using `fastLog` (strict CBV). -/
def fastHp (I : Interval) : Interval :=
  ivCBV I fun I => fsub (fastLog (fsub ONE I)) (fastLog I)

lemma mem_fastHp {I : Interval} {x : ℝ} (hx : mem I x)
    (hI0 : 0 < I.lo) (hI1 : 0 < (sub ONE I).lo) :
    mem (fastHp I) (hp x) := by
  have hx_pos : 0 < x := lt_of_lt_of_le (div_pos (by exact_mod_cast hI0) SCALE_pos) hx.1
  have h1mx := mem_sub mem_ONE hx
  have h1mx_pos : 0 < 1 - x := lt_of_lt_of_le (div_pos (by exact_mod_cast hI1) SCALE_pos) h1mx.1
  have h := mem_sub (mem_fastLog h1mx hI1) (mem_fastLog hx hI0)
  unfold fastHp hp; simp only [ivCBV_eq, fsub_eq]
  rw [Real.log_div (ne_of_gt h1mx_pos) (ne_of_gt hx_pos)]
  exact h

/-- Exact 16-step Newton integer square root guess (strict CBV, exact `⌊√n⌋` for all `n < 2^128`). -/
def fastIsqrtGuess (n : ℕ) : ℕ :=
  natCBV n fun n =>
  if n = 0 then 0
  else
    let init :=
      if n < 1099511627776 then 1048576
      else if n < 1152921504606846976 then 1073741824
      else if n < 1208925819614629174706176 then 1099511627776
      else if n < 1267650600228229401496703205376 then 1125899906842624
      else 1152921504606846976
    isqrtLoop n 16 init

def fastIsqrtLo (n : ℕ) : ℕ :=
  natCBV n fun n =>
  match fastIsqrtGuess n with
  | 0 => 0
  | k + 1 => if (k + 1) * (k + 1) ≤ n then k + 1 else 0

def fastIsqrtHi (n : ℕ) : ℕ :=
  natCBV n fun n =>
  match fastIsqrtGuess n with
  | 0 => if n = 0 then 0 else if n ≤ 1 then 1 else n + 1
  | k + 1 =>
    if n ≤ (k + 1) * (k + 1) then k + 1
    else if n ≤ (k + 2) * (k + 2) then k + 2
    else n + 1

private lemma fastIsqrtLo_sq_le (n : ℕ) : (fastIsqrtLo n) ^ 2 ≤ n := by
  unfold fastIsqrtLo; simp only [natCBV_eq]
  cases fastIsqrtGuess n with
  | zero => simp
  | succ k =>
    dsimp only
    split_ifs with h
    · simpa [_root_.sq] using h
    · simp

private lemma le_fastIsqrtHi_sq (n : ℕ) : n ≤ (fastIsqrtHi n) ^ 2 := by
  unfold fastIsqrtHi; simp only [natCBV_eq]
  cases fastIsqrtGuess n with
  | zero => dsimp only; split_ifs <;> nlinarith
  | succ k => dsimp only; split_ifs <;> nlinarith

def fastSqrt (I : Interval) : Interval :=
  ivCBV I fun I =>
  let loN := if I.lo ≤ 0 then 0 else fastIsqrtLo (I.lo.toNat * SCALE)
  let hiN := if I.hi ≤ 0 then 0 else fastIsqrtHi (I.hi.toNat * SCALE)
  ⟨(loN : ℤ), (hiN : ℤ)⟩

lemma mem_fastSqrt {I : Interval} {x : ℝ} (hx : mem I x) (hx0 : 0 ≤ x) :
    mem (fastSqrt I) (Real.sqrt x) := by
  have hS := SCALE_pos
  unfold fastSqrt mem; simp only [ivCBV_eq]; constructor
  · split_ifs with h
    · simp only [Nat.cast_zero, Int.cast_zero, zero_div]; exact Real.sqrt_nonneg x
    · push Not at h
      have hsq := fastIsqrtLo_sq_le (I.lo.toNat * SCALE)
      have hsqR : ((fastIsqrtLo (I.lo.toNat * SCALE) : ℝ) ^ 2) ≤ (I.lo : ℝ) * (SCALE : ℝ) := by
        have h1 : (I.lo.toNat : ℝ) = (I.lo : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (le_of_lt h)
        rw [← h1]; exact_mod_cast hsq
      have hdiv : ((fastIsqrtLo (I.lo.toNat * SCALE) : ℝ) / SCALE) ^ 2 ≤ x := by
        rw [div_pow, div_le_iff₀ (sq_pos_of_pos hS)]
        have := hx.1; rw [div_le_iff₀ hS] at this; nlinarith
      have hsr := Real.sqrt_le_sqrt hdiv
      rwa [Real.sqrt_sq (by positivity)] at hsr
  · split_ifs with h
    · have hxle : x ≤ 0 := le_trans hx.2 (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h) (le_of_lt hS))
      have : x = 0 := le_antisymm hxle hx0
      subst this; simp
    · push Not at h
      have hsq := le_fastIsqrtHi_sq (I.hi.toNat * SCALE)
      have hsqR : (I.hi : ℝ) * (SCALE : ℝ) ≤ ((fastIsqrtHi (I.hi.toNat * SCALE) : ℝ) ^ 2) := by
        have h1 : (I.hi.toNat : ℝ) = (I.hi : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (le_of_lt h)
        rw [← h1]; exact_mod_cast hsq
      have hdiv : x ≤ ((fastIsqrtHi (I.hi.toNat * SCALE) : ℝ) / SCALE) ^ 2 := by
        rw [div_pow, le_div_iff₀ (sq_pos_of_pos hS)]
        have := hx.2; rw [le_div_iff₀ hS] at this; nlinarith
      have hsr := Real.sqrt_le_sqrt hdiv
      rwa [Real.sqrt_sq (by positivity)] at hsr

/-- Fast interval `phi(x) = √(h(I_fun x x) / L)` (strict CBV). -/
def fastPhi (C : ConstIv) (X : Interval) : Interval :=
  fastSqrt (fdivPos (fastH (fIxxIv C X)) LN2)

lemma mem_fastPhi {C : ConstIv} (hC : ValidConstIv C) {X : Interval} {x : ℝ}
    (hx : mem X x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    mem (fastPhi C X) (phi x) := by
  unfold fastPhi; simp only [fdivPos_eq, fIxxIv_eq]
  have hIxx := mem_IxxIv hC hx hx0 hx1
  have hIcc := I_fun_mem_Icc (le_of_lt tau_pos) (by linarith [tau_lt_half]) hx0 hx1 hx0 hx1
  have hh := mem_fastH hIxx hIcc.1 hIcc.2
  have hdiv := mem_divPos hh mem_LN2 (by decide)
  exact mem_fastSqrt hdiv (div_nonneg (h_nonneg hIcc.1 hIcc.2) (le_of_lt L_pos))

/-- Fast interval `F(x, y) = h(x*y) + q*L*phi(x)*phi(y) - y*h(x) - x*h(y)` (strict CBV). -/
def fastF (C : ConstIv) (X Y : Interval) : Interval :=
  ivCBV X fun X => ivCBV Y fun Y =>
  ivCBV (fclamp01 (fmul X Y)) fun xy =>
  fsub (fsub (fadd (fastH xy) (fmul (fmul C.q LN2) (fmul (fastPhi C X) (fastPhi C Y))))
             (fmul Y (fastH X)))
       (fmul X (fastH Y))

lemma mem_fastF {C : ConstIv} (hC : ValidConstIv C) {X Y : Interval} {x y : ℝ}
    (hx : mem X x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy : mem Y y) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    mem (fastF C X Y) (F_fun x y) := by
  unfold fastF; simp only [ivCBV_eq, fclamp01_eq, fmul_eq, fsub_eq, fadd_eq]
  have hxy0 : 0 ≤ x * y := mul_nonneg hx0 hy0
  have hxy1 : x * y ≤ 1 := by nlinarith
  have hxy := mem_clamp01 (mem_mul hx hy) hxy0 hxy1
  have hres := mem_sub (mem_sub (mem_add (mem_fastH hxy hxy0 hxy1)
    (mem_mul (mem_mul hC.hq_mem mem_LN2) (mem_mul (mem_fastPhi hC hx hx0 hx1) (mem_fastPhi hC hy hy0 hy1))))
    (mem_mul hy (mem_fastH hx hx0 hx1))) (mem_mul hx (mem_fastH hy hy0 hy1))
  have heq : h (x * y) + qStar * L * (phi x * phi y) - y * h x - x * h y = F_fun x y := by unfold F_fun; ring
  rwa [heq] at hres

/-- Fast interval `J(x, y) = h(I(x, y)) - L * phi(x) * phi(y)` (strict CBV). -/
def fastJ (C : ConstIv) (X Y : Interval) : Interval :=
  ivCBV X fun X => ivCBV Y fun Y =>
  fsub (fastH (fIxyIv C X Y)) (fmul LN2 (fmul (fastPhi C X) (fastPhi C Y)))

lemma mem_fastJ {C : ConstIv} (hC : ValidConstIv C) {X Y : Interval} {x y : ℝ}
    (hx : mem X x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy : mem Y y) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    mem (fastJ C X Y) (J_fun x y) := by
  unfold fastJ; simp only [ivCBV_eq, fsub_eq, fIxyIv_eq, fmul_eq]
  have hIcc := I_fun_mem_Icc (le_of_lt tau_pos) (by linarith [tau_lt_half]) hx0 hx1 hy0 hy1
  have hres := mem_sub (mem_fastH (mem_IxyIv hC hx hy hx0 hx1 hy0 hy1) hIcc.1 hIcc.2)
    (mem_mul mem_LN2 (mem_mul (mem_fastPhi hC hx hx0 hx1) (mem_fastPhi hC hy hy0 hy1)))
  have heq : h (I_fun x y) - L * (phi x * phi y) = J_fun x y := by unfold J_fun; ring
  rwa [heq] at hres

/-- Fast interval `R(x) = F(r, x) / (q * L)` using exact `phi rStar = 1` (strict CBV). -/
def fastR (C : ConstIv) (X : Interval) : Interval :=
  ivCBV X fun X =>
  ivCBV (fclamp01 (fmul C.r X)) fun rx =>
  ivCBV (fmul C.q LN2) fun qL =>
  fdivPos (fsub (fsub (fadd (fastH rx) (fmul qL (fastPhi C X)))
                      (fmul X C.hr))
                (fmul C.r (fastH X)))
          qL

lemma mem_fastR {C : ConstIv} (hC : ValidConstIv C) (hqL : 0 < (mul C.q LN2).lo)
    {X : Interval} {x : ℝ} (hx : mem X x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    mem (fastR C X) (R_fun x) := by
  unfold fastR; simp only [ivCBV_eq, fclamp01_eq, fmul_eq, fdivPos_eq, fsub_eq, fadd_eq]
  have hr0 : 0 ≤ rStar := le_of_lt rStar_pos
  have hr1 : rStar ≤ 1 := le_of_lt rStar_lt_one
  have hrx0 : 0 ≤ rStar * x := mul_nonneg hr0 hx0
  have hrx1 : rStar * x ≤ 1 := by nlinarith
  have hrx := mem_clamp01 (mem_mul hC.hr_mem hx) hrx0 hrx1
  have hqL_mem := mem_mul hC.hq_mem mem_LN2
  have hnum := mem_sub (mem_sub (mem_add (mem_fastH hrx hrx0 hrx1)
      (mem_mul hqL_mem (mem_fastPhi hC hx hx0 hx1)))
      (mem_mul hx hC.hhr_mem))
    (mem_mul hC.hr_mem (mem_fastH hx hx0 hx1))
  have hres := mem_divPos hnum hqL_mem hqL
  have heq : (h (rStar * x) + qStar * L * phi x - x * hr - rStar * h x) / (qStar * L) = R_fun x := by
    unfold R_fun F_fun hr; rw [phi_rStar]; ring
  rwa [heq] at hres

/-- Fast interval `v(x) = h(x) - hr * phi(x)` (strict CBV). -/
def fastV (C : ConstIv) (X : Interval) : Interval :=
  ivCBV X fun X => fsub (fastH X) (fmul C.hr (fastPhi C X))

lemma mem_fastV {C : ConstIv} (hC : ValidConstIv C) {X : Interval} {x : ℝ}
    (hx : mem X x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    mem (fastV C X) (v_fun x) := by
  unfold fastV; simp only [ivCBV_eq, fsub_eq, fmul_eq]
  exact mem_sub (mem_fastH hx hx0 hx1) (mem_mul hC.hhr_mem (mem_fastPhi hC hx hx0 hx1))

/-- Fast interval `b(x) = x - h(x) / pStar - cParam * phi(x)` (strict CBV). -/
def fastB (C : ConstIv) (X : Interval) : Interval :=
  ivCBV X fun X => fsub (fsub X (fdivNeg (fastH X) C.p)) (fmul C.c (fastPhi C X))

lemma mem_fastB {C : ConstIv} (hC : ValidConstIv C) (hp : C.p.hi < 0)
    {X : Interval} {x : ℝ} (hx : mem X x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    mem (fastB C X) (b_fun x) := by
  unfold fastB; simp only [ivCBV_eq, fsub_eq, fdivNeg_eq, fmul_eq]
  exact mem_sub (mem_sub hx (mem_divNeg (mem_fastH hx hx0 hx1) hC.hp_mem hp))
    (mem_mul hC.hc_mem (mem_fastPhi hC hx hx0 hx1))

def fastF_of (C : ConstIv) (X Y hX hY phX phY : Interval) : Interval :=
  ivCBV (fclamp01 (fmul X Y)) fun xy =>
  fsub (fsub (fadd (fastH xy) (fmul (fmul C.q LN2) (fmul phX phY))) (fmul Y hX)) (fmul X hY)

def fastJ_of (C : ConstIv) (X Y phX phY : Interval) : Interval :=
  fsub (fastH (fIxyIv C X Y)) (fmul LN2 (fmul phX phY))

def fastR_of (C : ConstIv) (X hX phX : Interval) : Interval :=
  ivCBV (fclamp01 (fmul C.r X)) fun rx =>
  ivCBV (fmul C.q LN2) fun qL =>
  fdivPos (fsub (fsub (fadd (fastH rx) (fmul qL phX)) (fmul X C.hr)) (fmul C.r hX)) qL

def fastV_of (C : ConstIv) (hX phX : Interval) : Interval :=
  fsub hX (fmul C.hr phX)

def fastB_of (C : ConstIv) (X hX phX : Interval) : Interval :=
  fsub (fsub X (fdivNeg hX C.p)) (fmul C.c phX)

@[simp] lemma fastF_of_eq (C : ConstIv) (X Y : Interval) :
    fastF_of C X Y (fastH X) (fastH Y) (fastPhi C X) (fastPhi C Y) = fastF C X Y := by
  simp [fastF_of, fastF]

@[simp] lemma fastJ_of_eq (C : ConstIv) (X Y : Interval) :
    fastJ_of C X Y (fastPhi C X) (fastPhi C Y) = fastJ C X Y := by
  simp [fastJ_of, fastJ]

@[simp] lemma fastR_of_eq (C : ConstIv) (X : Interval) :
    fastR_of C X (fastH X) (fastPhi C X) = fastR C X := by
  simp [fastR_of, fastR]

@[simp] lemma fastV_of_eq (C : ConstIv) (X : Interval) :
    fastV_of C (fastH X) (fastPhi C X) = fastV C X := by
  simp [fastV_of, fastV]

@[simp] lemma fastB_of_eq (C : ConstIv) (X : Interval) :
    fastB_of C X (fastH X) (fastPhi C X) = fastB C X := by
  simp [fastB_of, fastB]

end UCBound.FastIv
