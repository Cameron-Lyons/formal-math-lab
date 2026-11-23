module

public import ArctanApprox

namespace Arxiv.«2607.05739»

/-- No integer value occurs from index 5 through 10,000, inclusive. -/
public theorem not_isIntegerValue_five_to_ten_thousand {n : ℕ}
    (hlo : 5 ≤ n) (hhi : n ≤ 10000) : ¬ IsIntegerValue n :=
  not_isIntegerValue_five_to_one_million hlo (by omega)

end Arxiv.«2607.05739»
