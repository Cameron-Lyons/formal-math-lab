module

public import Std.Tactic.BVDecide

public section

namespace SmallCubic.TwoPointIntegralTwo

private abbrev Pol (n : Nat) := List (BitVec n)
private abbrev Pair (n : Nat) := Pol n × Pol n

variable {n : Nat}

private def add : Pol n → Pol n → Pol n
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x+y) :: add xs ys

private def mul : Pol n → Pol n → Pol n
  | [], _ => []
  | x :: xs, ys => add (ys.map (x*·)) (0 :: mul xs ys)

private def plus (a b : Pair n) : Pair n := (add a.1 b.1, add a.2 b.2)

-- Products in Z/(4096)[v,w] with w²=2(v²-v)-2(1+v)w.
private def times (a b : Pair n) : Pair n :=
  let qr := mul a.2 b.2
  (add (mul a.1 b.1) (mul [0,-2,2] qr),
   add (add (mul a.1 b.2) (mul a.2 b.1)) (mul [-2,-2] qr))

private def marked (a step : BitVec n) (r q : Pol n) : Pair n :=
  (add [a,step] (mul [0,-1,1] r), q)

/-- The free coefficients of x, y, z in the integral Pell basis are stored in
ascending order. At w=0 their constant components are a + step*v + v(v-1)r,
which fixes their required values at v=0,1. -/
def IsLiftWithSteps (dx dy dz xr₀ xr₁ xr₂ xq₀ xq₁ xq₂ xq₃ yr₀ yr₁ yq₀ yq₁ yq₂
    zr₀ zr₁ zr₂ zr₃ zr₄ zq₀ zq₁ zq₂ zq₃ zq₄ zq₅ : BitVec n) : Prop :=
  let x := marked 0 dx [xr₀,xr₁,xr₂] [xq₀,xq₁,xq₂,xq₃]
  let y := marked 1 dy [yr₀,yr₁] [yq₀,yq₁,yq₂]
  let z := marked 1 dz [zr₀,zr₁,zr₂,zr₃,zr₄] [zq₀,zq₁,zq₂,zq₃,zq₄,zq₅]
  let f := plus (times x (times x x)) (times z (plus z (times y y)))
  (f.1.drop 1 ++ f.2).all (· == 0)

abbrev IsLift := @IsLiftWithSteps n (-2) 2 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- For any integral polynomial model through the fixed seed, the second
abscissa is even. The second ordinate and third coordinate remain free. -/
theorem second_abscissa_even (dx dy dz xr₀ xr₁ xr₂ xq₀ xq₁ xq₂ xq₃ yr₀ yr₁ yq₀ yq₁ yq₂
    zr₀ zr₁ zr₂ zr₃ zr₄ zq₀ zq₁ zq₂ zq₃ zq₄ zq₅ : BitVec 2) :
    IsLiftWithSteps dx dy dz xr₀ xr₁ xr₂ xq₀ xq₁ xq₂ xq₃ yr₀ yr₁ yq₀ yq₁ yq₂
      zr₀ zr₁ zr₂ zr₃ zr₄ zq₀ zq₁ zq₂ zq₃ zq₄ zq₅ → (dx &&& 1) = 0 := by
  simp only [IsLiftWithSteps, times, plus, marked, add, mul, List.map_cons, List.map_nil,
    List.drop, List.cons_append, List.nil_append, List.all_cons, List.all_nil]
  bv_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- No quartic with 2-integral coefficients in the original Pell ring can
satisfy all surface coefficient congruences modulo 4096 at the alternate mark. -/
theorem no_integral_lift (xr₀ xr₁ xr₂ xq₀ xq₁ xq₂ xq₃ yr₀ yr₁ yq₀ yq₁ yq₂
    zr₀ zr₁ zr₂ zr₃ zr₄ zq₀ zq₁ zq₂ zq₃ zq₄ zq₅ : BitVec 12) :
    ¬ IsLift xr₀ xr₁ xr₂ xq₀ xq₁ xq₂ xq₃ yr₀ yr₁ yq₀ yq₁ yq₂
      zr₀ zr₁ zr₂ zr₃ zr₄ zq₀ zq₁ zq₂ zq₃ zq₄ zq₅ := by
  simp only [IsLift, IsLiftWithSteps, times, plus, marked, add, mul, List.map_cons, List.map_nil, List.drop,
    List.cons_append, List.nil_append, List.all_cons, List.all_nil]
  bv_decide (config := {timeout := 120, maxSteps := 10000000})

/-- The preceding precision is attained, so 4096 is the first power of two
obstructing all integral coefficients in this chart. -/
theorem lift_mod_2048 :
    IsLift (1012 : BitVec 11) 264 368 584 656 952 544 1724 88 34 516 368
      492 1896 448 32 1600 1068 344 1408 0 1888 768 := by
  unfold IsLift IsLiftWithSteps
  decide +kernel

/-- The candidate second endpoint (8,7,-15) passes the same modulo-4096
test. The first three arguments are the differences from the seed (0,1,1). -/
theorem eight_endpoint_mod_4096 :
    IsLiftWithSteps (8 : BitVec 12) 6 (-16)
      1484 3248 2096 898 676 1592 1968 2900 2728 410 1740 56
      2500 3376 3152 3840 640 2108 1672 2240 3136 2080 2368 := by
  unfold IsLiftWithSteps
  decide +kernel

end SmallCubic.TwoPointIntegralTwo
