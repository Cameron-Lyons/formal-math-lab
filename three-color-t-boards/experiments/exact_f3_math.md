# Exact natural-field model over F₃

The unrestricted board count equals the exact quotient dimension of a **96-variable ideal over F₃ with 96 field cubics and 76 power-moment equations**. It needs no extension field, no substituted pivot-domain equations, no prefix restriction, and no symmetry multiplier. Its unrestricted dimension has not been computed yet.

Frozen artifacts (generated independently of the earlier `F₂` exports):
- Model JSON: [exact_f3_math_model.json](exact_f3_math_model.json), SHA256 `fe1321842be3bf5bdb8ff91cd5b9c38017d542968fe27a8d5a8952e344564cc4`.
- Polynomial input: [exact_f3_math_model.ms](exact_f3_math_model.ms), SHA256 `e9e1163bd047fdca4000333d917a26e37dbf711abebca29d27fae6d49a2c34ba`.

## Power moments characterize valid boards exactly

Represent colors directly as `0, 1, 2 ∈ F₃`, with cell domains `z³ - z = 0`. For each exponent tuple `e ∈ {0, 1, 2}⁴`, define

```
M_e = Σ_T placements ∏_(role i) z_i^(e_i),
```

with `0⁰ = 1`. When all 81 patterns occur once each,

```
M_(2,2,2,2) = 1,
M_e = 0 for every other e.
```

In `F₃`, `Σ c⁰ = 0`, `Σ c = 0`, and `Σ c² = -1`, so the product of four role sums vanishes unless every exponent is 2 (giving `(-1)⁴ = 1`). Since `M_0000 = 81 = 0` holds automatically, 80 equations remain.

In the reverse direction, color `c` has indicator `δ_c(z) = 1 - (z - c)²` over `F₃`, whose leading coefficient is `-1`. Expanding the product of four indicators and summing over all placements eliminates every moment except `M_2222` (with coefficient `(-1)⁴ = 1`), so the 80 equations force every integer pattern count to be `1 (mod 3)`. Each count is therefore at least 1, and since all 81 counts sum to 81 placements, every count must equal 1.

Equivalently, the single-coordinate evaluation matrix

```
1 1 1
0 1 2
0 1 1
```

has determinant 2 in `F₃`, so its fourth tensor power (checked to have rank 81) is an invertible moment transform. Unlike the `F₄` character model, Frobenius is the identity on `F₃`, so there is no pairing down to 40 conjugate moments.

## Signed prefix coordinates and elimination

Using the same Gray ordering of role-membership signatures as the audited prefix model (ascending cell indices inside each signature group), set

```
y_j = Σ_(k ≤ j) z_order[k],
z_order[j] = y_j - y_(j-1),   y_(-1) = 0.
```

Solving the four geometric unary equations over `F₃` eliminates:

```
y80 = 0,
y16 = y97,
y81 = -y8 + y72 + y98,
y99 = -y7 + y9 - y65 + y82.
```

The other 96 prefix coordinates stay free in ascending order. All 100 signed original-color forms are stored explicitly, and symbolic summation checks that their cumulative sums recover every free and eliminated variable.

Substituting these four equations makes the 4 unary linear moments vanish identically while keeping the 4 unary **quadratic** moments, leaving 76 nonzero moment equations (including `M_2222 - 1`).

## Why only 96 independent field cubics are needed

Over `F₃`, every linear form `L = Σ a_i y_i` obeys

```
L³ - L = Σ a_i (y_i³ - y_i).
```

Any invertible `F₃`-linear change of variables therefore preserves the field-domain ideal. Once the four unary variables are eliminated, their field equations already lie in the ideal of the remaining 96 field cubics, leaving **no extra pivot-domain constraints** (unlike the `z³ = 1` domain in the characteristic-2 model).

Moment polynomials are reduced only by those 96 field cubics, turning any positive exponent `n` into `1 + ((n - 1) mod 2)`: so `y³ = y` and `y⁴ = y²`, while `y²` stays `y²` and positive powers never collapse to 0 (since 0 is a valid value).

## Quotient dimension and scope

Quotienting by the 96 field cubics produces one copy of `F₃` for each point of `F₃⁹⁶`. Adding the moment equations keeps exactly the coordinates corresponding to valid labeled boards. The final quotient is therefore reduced, and its `F₃`-vector-space dimension equals the unrestricted labeled count `N` directly, with no extension-field degree or symmetry factor.

Every permutation of three colors is affine (`z ↦ az + b` with `a ∈ {1, 2}`, `b ∈ F₃`). Global shifts give `N = 3 * N_(apex=0)`, though no shift normalization is applied here.

## Checks and practical limits

[exact_f3_math.py](exact_f3_math.py) and [exact_f3_math_audit.json](exact_f3_math_audit.json) verify:

- Fresh Cartesian placement geometry and rank 81 for the moment transform.
- Exact linear-identity checks on the forward and inverse prefix maps.
- Direct evaluation of every kept moment against reconstructed boards on 12 arbitrary free assignments.
- All moment equations and coordinate round trips on 161 valid boards.

The export has 172 generators: 192 terms across the 96 domain cubics and 96,050 terms across the 76 moments (coefficients 1 or 2). That removes dense domain polynomials at the cost of larger moment polynomials, with no claimed runtime advantage.

The JSON stores zero polynomials with targets **already subtracted** (so `M_2222` carries constant term `2`, and `target_moment` is informational only). Monomials use 4 bits per exponent with explicit coefficients. No `F₂` elementary equations are included; the separate [native cubic augmentation](exact_f3_math_e3.md) lives outside this frozen base.

```sh
python experiments/exact_f3_math.py --check
```
