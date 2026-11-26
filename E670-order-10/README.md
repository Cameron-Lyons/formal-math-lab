# Equation 670 at order 10

No 10-element magma satisfies Equation 670 of the [Equational Theories Project](https://teorth.github.io/equational_theories/):

$$
x = y \star \bigl(x \star ((x \star y) \star y)\bigr)
$$

for all $x, y$, written in ETP notation as `x = y ◇ (x ◇ ((x ◇ y) ◇ y))`, with opposite-operation dual Equation 2937.

| Field | Summary |
| --- | --- |
| Problem | Equational Theories Project Equation 670 (dual Equation 2937), finite magma spectrum at order 10 |
| Law | `x = y ◇ (x ◇ ((x ◇ y) ◇ y))` |
| Status | Order 10 settled (no model). Orders 2, 3, 6, 7, 8 were already ruled out and models exist at 1, 4, 5, 9, 11, and all large enough orders; 10 was the smallest undecided order in the spectrum catalogue we checked. |
| Main theorem | `E670.no_model_of_order_ten` in [E670/Main.lean](E670/Main.lean) |
| Additional checks | Affine models `x * y = a*x + b*y (mod n)` verified for orders 19, 29, 31, 41, 59, 61 in [E670/Examples.lean](E670/Examples.lean) |
| Verification | `lake build` (Lean 4.36.0, stdlib only; kernel-checked reduction + 1,044 LRAT certificates replayed via `native_decide`) |
| Prior art | Checked 23 November 2026: no earlier order-10 exclusion was found (bounded search, not a claim of absolute priority). See [PRIOR_ART.md](../PRIOR_ART.md#e670-at-order-10). |

## Theorem

`E670.no_model_of_order_ten` proves that no binary operation on 10 elements satisfies

$$
y\star\bigl(x\star((x\star y)\star y)\bigr)=x
$$

for all $x, y$.

A binary operation on 10 elements is a $10\times 10$ table with entries from those same 10 elements. Row $a$, column $b$ holds $a\star b$, with no associativity or commutativity assumed. Models exist at sizes 1, 4, 5, 9, 11, and every sufficiently large size, while none exist at 2, 3, 6, 7, or 8. Order 10 was the smallest open size in the catalogue we checked.

The proof is computer-assisted. Lean's kernel proves that the elements of any 10-element model can be renamed so its table satisfies a fixed CNF formula, and Lean then checks solver certificates showing that the formula is unsatisfiable.

## Proof overview

### Rows are permutations

Fix $y$. The law writes every $x$ as $y\star(\text{something})$, so row $y$ hits all 10 elements and therefore hits each once. Every row is a permutation, so we can cancel on the left: $y\star u=y\star v$ implies $u=v$.

Set $a=x\star y$, $b=a\star y$, and $c=x\star b$. The law says $y\star c=x$. Because rows are permutations, the same four equalities work in two more directions:

* if $x\star y=a$, $a\star y=b$, and $y\star c=x$, then $x\star b=c$;
* if $x\star y=a$, $x\star b=c$, and $y\star c=x$, then $a\star y=b$.

### Naming the elements

Renaming elements preserves the law, so we can choose convenient names.

If some element has $a\star a\ne a$, call it $0$. Otherwise every element satisfies $x\star x=x$, and any element can be called $0$.

Next scan $k=0,1,2,\ldots$ in order. If $0\star k > k+1$, swap the names $k+1$ and $0\star k$. Both are larger than $k$, and all entries $0\star y$ with $y<k$ are at most $k$, so earlier columns stay fixed. Afterward,

$$
0\star y\le y+1\quad\text{for every }y.
$$

This is `exists_normal` in [E670/Normal.lean](E670/Normal.lean).

### The Boolean formula

Create 1,000 Boolean variables, one for each statement $x\star y=z$. The CNF clauses say that:

* every cell has a unique value;
* every row takes every value once;
* the law holds in all three directions listed above for all $x,y,a,b,c$;
* $0\star y\le y+1$ for every $y$;
* if $0\star 0=0$, then $x\star x=x$ for every $x$.

Lean proves that any model named as above satisfies all 309,246 clauses (`sat_formula` in [E670/Encoding.lean](E670/Encoding.lean)). It remains to show that no assignment to the 1,000 variables satisfies them.

### Case-split refutation

A single SAT run would produce a certificate too large to check, so we split the problem into 1,043 cases. Each case is a short list of equations $x\star y=z$ or disequations $x\star y\ne z$ on the first row and first column, stored in [E670/Cases.lean](E670/Cases.lean). A search script built them by fixing entries in the first row and then the first column until CaDiCaL refuted each case in a few seconds.

The case list is not trusted. Lean checks one certificate per case (showing no solution fits that case) and one covering certificate showing no solution falls outside all cases (`unsat_of_cubes` in [E670/Cubes.lean](E670/Cubes.lean)).

Certificates are not stored in the repository. During the build, the tactic `refute` runs the CaDiCaL binary bundled with Lean and passes its trimmed LRAT proofs as string literals to `Std.Tactic.BVDecide.Reflect.verifyCert`, the verified LRAT checker behind `bv_decide`. Because the checker runs by native evaluation, Lean's compiler and runtime are inside the trust boundary; the solver, the tactic, and the case list are not.

## Reproduce

Build with the pinned Lean 4.36.0 toolchain and its bundled SAT solver (no other dependencies). From this directory, run:

```sh
lake build
```

The main theorem is `E670.no_model_of_order_ten` in [E670/Main.lean](E670/Main.lean):

```lean
theorem no_model_of_order_ten :
    ¬ ∃ op : Fin 10 → Fin 10 → Fin 10, ∀ x y, op y (op x (op (op x y) y)) = x
```

The build calls CaDiCaL 1,044 times (once per case plus the covering certificate) and checks every certificate in Lean. On an 8-core machine it took 9 minutes with 4.1 GB peak memory, writing about 6.3 GB under `.lake` (mostly certificate text).

Lake builds the 110 case modules in parallel across available cores. On a machine with less RAM, cap Lean's threads:

```sh
LEAN_NUM_THREADS=2 lake build
```

The theorem depends on the standard logical axioms (`propext`, `Classical.choice`, `Quot.sound`) plus 111 native-evaluation axioms (one for each of the 110 case modules and one for the covering certificate), with no admitted lemmas. To check them, run:

```sh
printf '%s\n' 'import E670' '#print axioms E670.no_model_of_order_ten' | lake env lean --stdin
```

### Reading the Lean files

| File | Contents |
| --- | --- |
| [E670/Basic.lean](E670/Basic.lean) | The law, rows as permutations, and the law in three directions. |
| [E670/Normal.lean](E670/Normal.lean) | Element renaming. |
| [E670/Encoding.lean](E670/Encoding.lean) | The CNF formula and the proof that every normalized model satisfies it. |
| [E670/Cubes.lean](E670/Cubes.lean) | Case-split refutation and the `refute` tactic. |
| [E670/Cases.lean](E670/Cases.lean) | The 1,043 cases in 110 groups (data). |
| `E670/Part/`, [E670/Parts.lean](E670/Parts.lean) | One three-line module per group plus their summary, generated by [scripts/parts.sh](scripts/parts.sh). |
| [E670/Main.lean](E670/Main.lean) | The covering certificate and final theorem. |
| [E670/Examples.lean](E670/Examples.lean) | Models of other sizes (not used in the proof). |

The renaming, table encoding, case-split machinery, and finite surjection-is-injection lemma do not depend on Equation 670. The [Equation 677 project](../E677-E255-order-9/) imports them from `E670/Basic.lean`, `E670/Normal.lean`, `E670/Encoding.lean`, and `E670/Cubes.lean` for its own 10-element proof, and builds its part modules with `scripts/parts.sh`.

### Independent check

[scripts/check.py](scripts/check.py) generates the formula directly from the law with no shared Lean code, and splits it by the first row alone. Under the naming above, the first row is a permutation $r$ with $r(y)\le y+1$, giving 512 possible rows. The script runs CaDiCaL on each (using Python 3 and CaDiCaL from `PATH` or the Lean toolchain):

```sh
python3 scripts/check.py --jobs 4
```

Expected last line:

```text
order 10: 512 first rows, all UNSAT
```

Here `UNSAT` means no solution has that first row. To also check every refutation with [drat-trim](https://github.com/marijnheule/drat-trim), pass its path:

```sh
python3 scripts/check.py --jobs 4 --verify-with /path/to/drat-trim
```

This prints `order 10: 512 first rows, all UNSAT, all proofs verified`. With four jobs it took 21 minutes using `drat-trim` at [revision `2e3b2dc0ecf938addbd779d42877b6ed69d9a985`](https://github.com/marijnheule/drat-trim/tree/2e3b2dc0ecf938addbd779d42877b6ed69d9a985).

## Six further sizes with models

[E670/Examples.lean](E670/Examples.lean) also verifies that $x\star y=ax+by\pmod n$ satisfies Equation 670 for:

| $n$ | 19 | 29 | 31 | 41 | 59 | 61 |
| --- | --- | --- | --- | --- | --- | --- |
| $(a,b)$ | $(9,11)$ | $(3,27)$ | $(6,2)$ | $(12,37)$ | $(20,40)$ | $(6,58)$ |

These models are not new; they appear in the [survey data](https://github.com/Timeroot/equational_theories/blob/6a653268c6f6173a00e5d7e9d61ad33aca8e52c3/data/spectrum/open_survey_20260927.json) of the spectrum work below. The catalogue snapshot cited in the [audit](../PRIOR_ART.md#e670-at-order-10) still lists all six sizes as undecided.

## Related work

The law is Equation 670 of the [Equational Theories Project](https://teorth.github.io/equational_theories/). Its finite spectrum is tracked in a [spectrum catalogue](https://ohaithe.re/equational_theories/spectrum/?eq=670) on the `definability-negative` branch of [Timeroot/equational_theories](https://github.com/Timeroot/equational_theories), outside the main repository. That Lean development proves exclusions at 2, 3, 6, 7, and 8 and existence at all large enough sizes. Its [order-ten notes](https://github.com/Timeroot/equational_theories/blob/6a653268c6f6173a00e5d7e9d61ad33aca8e52c3/docs/order_ten_followup_20261007.md#what-remains-at-ten) record a 10-minute full search plus searches over 97 first rows capped at 100,000 conflicts per row. The [accompanying data](https://github.com/Timeroot/equational_theories/blob/6a653268c6f6173a00e5d7e9d61ad33aca8e52c3/data/spectrum/order_ten_followup_20261007.json) lists 61 rows refuted and 36 undecided.

Our choice of $0$, the bound $0\star y\le y+1$, and one variable per statement $x\star y=z$ follow that work. Three details differ: we write clauses directly on table entries without auxiliary variables for $(x\star y)\star y$; we give the solver more time; and we skip sorting the first row's cycles by length (which cuts 512 first rows down to 97, trading 2 to 2.5 times more solver time for a simpler renaming proof).
