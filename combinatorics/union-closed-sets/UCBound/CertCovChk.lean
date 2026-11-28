module

public import UCBound.Cert2DHelpers
public import UCBound.CertCovTrees

@[expose] public section

namespace UCBound.Cert2D

open UCBound UCBound.Iv UCBound.Cert UCBound.FastIv

def kapIv : Interval := ofRat 39 100
def CcovIv : Interval := ofRat 13 25
def deltaIv : Interval := ofRat 7 10000
def r1_12Iv : Interval := ofRat 1 12

def okCovLow (X : Interval) : Bool :=
  ivCBV X fun X =>
  decide (0 < X.lo) && decide (X.lo ≤ X.hi) && decide (0 < (fsub ONE X).lo) &&
  decide (0 < (fsub (fsub kapIv r1_12Iv) (fsub (fmul (fmul (ofInt 2) (fmul X (fsub ONE X))) (fastHp X)) X)).lo)

def FaIv (A X : Interval) : Interval :=
  ivCBV A fun A => ivCBV X fun X =>
  fadd (fsub (fadd (fmul kapIv (fmul X (fdivPos (fastH A) A))) (fmul deltaIv (fsub A X)))
             (fmul (fsub (fadd X kapIv) A) (fastH X)))
       (fmul CcovIv (fastR constIv X))

def FaDaIv (A X : Interval) : Interval :=
  ivCBV A fun A => ivCBV X fun X =>
  fadd (fadd (fmul kapIv (fmul X (fdivPos (fastLog (fsub ONE A)) (fsq A)))) deltaIv) (fastH X)

def FaDxIv (A X : Interval) : Interval :=
  ivCBV A fun A => ivCBV X fun X =>
  fadd (fsub (fsub (fmul kapIv (fdivPos (fastH A) A)) deltaIv)
             (fadd (fastH X) (fmul (fsub (fadd X kapIv) A) (fastHp X))))
       (fmul CcovIv (fastRP X))

def fGuardCovInt (A X : Interval) : Bool :=
  ivCBV A fun A => ivCBV X fun X =>
  decide (0 < A.lo) && decide (A.lo ≤ A.hi) && decide (0 < (fsub ONE A).lo) && decide (0 < (fsq A).lo) &&
  fGuardD1 X

def okCovInt (w : LeafW) (A X : Interval) : Bool :=
  fGuardCovInt A X && centered2DWPos FaIv FaDaIv FaDxIv w A X

def KLIv (X A : Interval) : Interval :=
  ivCBV X fun X => ivCBV A fun A =>
  fsub (fsub (fneg (fastH X)) (fmul X (fastLog A))) (fmul (fsub ONE X) (fastLog (fsub ONE A)))

def GhiIv (A X : Interval) : Interval :=
  ivCBV A fun A => ivCBV X fun X =>
  fsub (fmul kapIv (KLIv X A)) (fmul (fsub A X) (fsub (fastH A) (fastH X)))

def GhiDaIv (A X : Interval) : Interval :=
  ivCBV A fun A => ivCBV X fun X =>
  fsub (fsub (fmul kapIv (fdivPos (fsub A X) (fmul A (fsub ONE A)))) (fsub (fastH A) (fastH X)))
       (fmul (fsub A X) (fastHp A))

def GhiDxIv (A X : Interval) : Interval :=
  ivCBV A fun A => ivCBV X fun X =>
  fadd (fadd (fmul kapIv (fsub (fastHp A) (fastHp X))) (fsub (fastH A) (fastH X)))
       (fmul (fsub A X) (fastHp X))

def fGuardCovHi (A X : Interval) : Bool :=
  ivCBV A fun A => ivCBV X fun X =>
  decide (0 < A.lo) && decide (A.lo ≤ A.hi) && decide (0 < (fsub ONE A).lo) &&
  decide (0 < (fmul A (fsub ONE A)).lo) &&
  decide (0 < X.lo) && decide (X.lo ≤ X.hi) && decide (0 < (fsub ONE X).lo)

def okCovHi (w : LeafW) (A X : Interval) : Bool :=
  match w with
  | .skip => decide (SCALE - A.lo ≤ X.lo)
  | _ => fGuardCovHi A X && centered2DWPos GhiIv GhiDaIv GhiDxIv w A X

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
lemma chk_CovLow : check1D okCovLow cLowLo cLowHi treeCovLow = true := by decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
lemma chk_CovInt : check2DW okCovInt ca1 ca2 cx1 cx2 treeCovInt = true := by decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
lemma chk_CovHi : check2DW okCovHi ca3 ca4 cxh1 cxh2 treeCovHi = true := by decide +kernel

end UCBound.Cert2D
