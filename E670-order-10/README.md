# E670 order 10: a Lean proof of finite magma nonexistence

**Prior-art status (23 November 2026):** no earlier proof of this order-10
exclusion was located. The public spectrum catalogue for the laws of the
Equational Theories Project, maintained on a fork of the project's repository,
lists 2, 3, 6, 7 and 8 as the excluded orders for Equation 670 and leaves 10 as
its smallest undecided order. This is a bounded search finding, not a claim of
absolute priority. See the
[audit and live-source evidence](../PRIOR_ART.md#e670-at-order-10).
Related identifiers include *Equation 670*, *magma spectrum*, and the dual
law *E2937*.

**Theorem.** No binary operation on 10 elements satisfies
$$
y\star\bigl(x\star((x\star y)\star y)\bigr)=x
$$
for all $x,y$.

A binary operation on 10 elements is a $10\times10$ table whose entries are drawn from those same 10 elements. The entry in row $a$, column $b$ is $a\star b$. We assume no associativity or commutativity. Tables satisfying the law exist with 1, 4, 5, 9 and 11 elements, and with every sufficiently large number of elements; none exists with 2, 3, 6, 7 or 8. Ten was the smallest size left undecided.

The proof is computer-assisted. Lean proves that the elements of any such table can be renamed so that the table satisfies a fixed list of clauses, and checks solver certificates showing that the clauses are contradictory.

## Rows are permutations

Fix $y$. The law writes every $x$ as $y\star(\text{something})$, so row $y$ contains every element. A row of ten entries containing all ten elements contains each exactly once. Every row is therefore a permutation, and we may cancel on the left: $y\star u=y\star v$ forces $u=v$.

Name three entries $a=x\star y$, $b=a\star y$ and $c=x\star b$. The law says $y\star c=x$. Because rows are permutations, the same four equalities can be read in two more directions:

* if $x\star y=a$, $a\star y=b$ and $y\star c=x$, then $x\star b=c$;
* if $x\star y=a$, $x\star b=c$ and $y\star c=x$, then $a\star y=b$.

## Naming the elements

Renaming the elements does not affect the law, so we may choose the names.

If some element has $a\star a\ne a$, call such an element 0. Otherwise every element satisfies $x\star x=x$, and any element may be called 0.

Then go through $k=0,1,2,\ldots$ in turn. If $0\star k$ is larger than $k+1$, exchange the names $k+1$ and $0\star k$. Both are larger than $k$, and the entries $0\star y$ with $y<k$ are at most $k$, so nothing settled earlier is disturbed. Afterwards
$$
0\star y\le y+1\quad\text{for every }y.
$$
This is `exists_normal` in [E670/Normal.lean](E670/Normal.lean).

## The formula

Introduce a Boolean variable for each statement $x\star y=z$, a thousand in all. The formula consists of the clauses saying that

* every cell has exactly one value;
* every row takes every value exactly once;
* the law holds, in the three directions listed above, for all $x,y,a,b,c$;
* $0\star y\le y+1$ for every $y$;
* if $0\star0=0$ then $x\star x=x$ for every $x$.

Lean proves that the table of any model named as above satisfies all 309,246 clauses (`sat_formula` in [E670/Encoding.lean](E670/Encoding.lean)). It remains to show that no assignment of the thousand variables satisfies them.

## The refutation

A single run of a SAT solver on the formula would produce a certificate too large to check, so the work is divided into 1043 cases. A case is a short list of statements $x\star y=z$ or $x\star y\ne z$ about the first row and the first column. The cases are listed in [E670/Cases.lean](E670/Cases.lean). They were found by a search that fixes entries of the first row, then of the first column, until CaDiCaL refutes the case within a few seconds.

The list of cases is not trusted. Lean checks one certificate per case, showing that the formula has no solution in that case, and one more certificate showing that no solution of the formula lies outside all the cases (`unsat_of_cubes` in [E670/Cubes.lean](E670/Cubes.lean)).

The certificates are not stored in the repository. During the build, the tactic `refute` runs the CaDiCaL binary shipped with Lean and passes its trimmed LRAT refutations, as string literals, to `Std.Tactic.BVDecide.Reflect.verifyCert`, the verified LRAT checker behind `bv_decide`. The checker runs by native evaluation, so Lean's compiler and runtime are part of the trusted computation. The solver, the tactic and the list of cases are not.

## Reproduce

The project builds with the pinned Lean 4.36.0 toolchain and its bundled SAT solver, with no other dependencies. From this directory run

```sh
lake build
```

The endpoint is `E670.no_model_of_order_ten` in [E670/Main.lean](E670/Main.lean):

```lean
theorem no_model_of_order_ten :
    ¬ ∃ op : Fin 10 → Fin 10 → Fin 10, ∀ x y, op y (op x (op (op x y) y)) = x
```

The build runs CaDiCaL 1044 times, once per case and once for the covering certificate, and Lean checks every certificate. On an 8-core machine it took nine minutes with a peak memory use of 4.1 GB. It writes about 6.3 GB under `.lake`, almost all of it certificate text.

Lake builds the 110 case modules in parallel, as many at a time as there are cores. To build fewer at a time on a machine with little memory, limit Lean's threads:

```sh
LEAN_NUM_THREADS=2 lake build
```

The theorem depends on the standard logical axioms (`propext`, `Classical.choice`, `Quot.sound`) and 111 native-evaluation axioms, one for each of the 110 modules that check cases and one for the covering certificate; there are no admitted lemmas. To inspect them, run

```sh
printf '%s\n' 'import E670' '#print axioms E670.no_model_of_order_ten' | lake env lean --stdin
```

### Reading the Lean files

| File | Contents |
|---|---|
| [E670/Basic.lean](E670/Basic.lean) | The law; rows are permutations; the law in three directions. |
| [E670/Normal.lean](E670/Normal.lean) | Naming the elements. |
| [E670/Encoding.lean](E670/Encoding.lean) | The formula, and the proof that every model satisfies it. |
| [E670/Cubes.lean](E670/Cubes.lean) | Refutation by cases; the tactic `refute`. |
| [E670/Cases.lean](E670/Cases.lean) | The 1043 cases, in 110 groups. Data. |
| `E670/Part/`, [E670/Parts.lean](E670/Parts.lean) | One three-line module per group, and their summary. Written by [scripts/parts.sh](scripts/parts.sh). |
| [E670/Main.lean](E670/Main.lean) | The covering certificate and the theorem. |
| [E670/Examples.lean](E670/Examples.lean) | Models of other sizes; not used in the proof. |

### An independent check

[scripts/check.py](scripts/check.py) writes the formula directly from the law, sharing no code with the Lean development, and splits it in its own way: by the first row alone. In the naming above the first row is a permutation $r$ with $r(y)\le y+1$, and there are 512 of those. The script runs CaDiCaL once for each. It needs Python 3 and CaDiCaL, which it finds on `PATH` or in the Lean installation.

```sh
python3 scripts/check.py --jobs 4
```

Expected last line:

```text
order 10: 512 first rows, all UNSAT
```

Here `UNSAT` means that the formula has no solution with that first row. To also check every refutation with [drat-trim](https://github.com/marijnheule/drat-trim), pass its path:

```sh
python3 scripts/check.py --jobs 4 --verify-with /path/to/drat-trim
```

This mode reports `order 10: 512 first rows, all UNSAT, all proofs verified`. With four jobs it took 21 minutes here, using drat-trim at [revision `2e3b2dc0ecf938addbd779d42877b6ed69d9a985`](https://github.com/marijnheule/drat-trim/tree/2e3b2dc0ecf938addbd779d42877b6ed69d9a985).

## Six further sizes with models

[E670/Examples.lean](E670/Examples.lean) also checks that $x\star y=ax+by$ modulo $n$ satisfies the law for

| $n$ | 19 | 29 | 31 | 41 | 59 | 61 |
|---|---|---|---|---|---|---|
| $(a,b)$ | $(9,11)$ | $(3,27)$ | $(6,2)$ | $(12,37)$ | $(20,40)$ | $(6,58)$ |

These models are not new: they are recorded in the [survey data](https://github.com/Timeroot/equational_theories/blob/6a653268c6f6173a00e5d7e9d61ad33aca8e52c3/data/spectrum/open_survey_20260927.json) of the spectrum work described below. The catalogue snapshot cited in the [audit](../PRIOR_ART.md#e670-at-order-10) nevertheless lists all six sizes as undecided.

## Related work

The law is Equation 670 of the [Equational Theories Project](https://teorth.github.io/equational_theories/). The sizes at which it has a model are tracked in a [spectrum catalogue](https://ohaithe.re/equational_theories/spectrum/?eq=670) developed on the `definability-negative` branch of the fork [Timeroot/equational_theories](https://github.com/Timeroot/equational_theories); that work is not part of the project's main repository. Its Lean development proves the exclusions at 2, 3, 6, 7 and 8 and the existence of models at all sufficiently large sizes. Its [order-ten notes](https://github.com/Timeroot/equational_theories/blob/6a653268c6f6173a00e5d7e9d61ad33aca8e52c3/docs/order_ten_followup_20261007.md#what-remains-at-ten) record a ten-minute search of the whole problem and searches of 97 first rows, with budgets of at most 100,000 conflicts per row. The [accompanying data](https://github.com/Timeroot/equational_theories/blob/6a653268c6f6173a00e5d7e9d61ad33aca8e52c3/data/spectrum/order_ten_followup_20261007.json) lists 61 rows refuted and 36 undecided.

The choice of the element 0, the condition $0\star y\le y+1$, and the use of one variable for each statement $x\star y=z$ follow that work. Three things differ here. The clauses are written directly on the table entries, without auxiliary variables for $(x\star y)\star y$. The solver is given more time. And the first row is not normalised further: that work also sorts the cycles of the first row by length, which leaves 97 first rows where this proof has 512. Keeping all 512 costs two to two and a half times the solver's work and saves a second renaming argument.
