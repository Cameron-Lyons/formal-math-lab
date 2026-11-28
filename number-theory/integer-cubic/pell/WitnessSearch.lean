module

public import SmallCubic

/-! Integer points found by enumerating roots of x³ ≡ 2 modulo |z|. -/
public section

namespace SmallCubic.WitnessSearch

/-- These solutions have distinct first coordinates, each of absolute
value greater than thirty million. -/
theorem three_large_solutions :
    Solves (-280813200) 157750309 889840366 ∧
    Solves (-71709552) 18357983 1094157121 ∧
    Solves 36307388 16351199 (-179013631) ∧
    (-280813200 : ℤ) < -71709552 ∧ (-71709552 : ℤ) < 36307388 ∧
    (30000000 : ℤ) < |(-280813200 : ℤ)| ∧ 30000000 < |(-71709552 : ℤ)| ∧
    30000000 < |(36307388 : ℤ)| := by
  simp only [solves_iff_discriminant]
  decide +kernel

end SmallCubic.WitnessSearch
