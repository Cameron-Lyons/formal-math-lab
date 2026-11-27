# A026019: prior-art and novelty audit

Checked **November 23, 2026** and re-audited **November 26, 2026**. The target is the exact three-term recurrence in `A026019.recurrence` for the binomially defined sequence and every `n ≥ 2`.

Georg Fischer's first-order recurrence in jOEIS already implied the recurrence on **November 6, 2026**, before this project began. One day after this folder's initial commit, Robert Israel also independently verified the exact conjecture via Maple's `simplify` command on Math StackExchange ([question 5156049](https://math.stackexchange.com/questions/5156049/mathars-recurrence-conjecture), **November 24, 2026**) and updated [OEIS A026019](https://oeis.org/A026019) (revision 30, November 24-25, 2026). Treat this folder as a checked Lean proof, not as a first mathematical proof or a new recurrence.

## OEIS and the exact statement

The search-indexed [A026019 entry](https://oeis.org/A026019) lists the recurrence as a conjecture by R. J. Mathar (June 20, 2013), along with a generating function by Mark van Hoeij (November 9, 2011). No proof is attached in that copy, though keeping the conjecture label does not prove no proof exists elsewhere.

The search-indexed [internal snapshot](https://oeis.org/A026019/internal) shows entry revision 26, dated September 6, 2025 (the site-wide footer date is separate and not the entry's revision date).

Direct requests for the live entry, internal format, JSON search result, and revision history returned HTTP 403 during this audit. As a result, we checked the search-indexed entry rather than the full current OEIS revision history.

## Earlier first-order recurrence: jOEIS

Georg Fischer switched jOEIS's implementation of A026019 from direct binomial evaluation to a first-order polynomial recurrence in [commit 06f94740c2d0d4b0815dedce8d41dd008ef0c1b8](https://github.com/archmageirvine/joeis/commit/06f94740c2d0d4b0815dedce8d41dd008ef0c1b8), dated **November 6, 2026, 22:46:25 UTC**. The [immutable source](https://github.com/archmageirvine/joeis/blob/06f94740c2d0d4b0815dedce8d41dd008ef0c1b8/src/irvine/oeis/a026/A026019.java) stores coefficient arrays

```text
p0 = [-36, 42, 216, 147, -540, -189]
p1 = [36, -18, -70, 50, 94, 28]
```

in ascending powers of `n`, meaning `p0(n)*a(n-1) + p1(n)*a(n) = 0`.

Algebraically, write $P(n) = 7n^2 + 6n + 2$. That recurrence factors as

$$
2(n+1)(2n+3)(n+2)P(n-1)a_n
= 3(3n-1)(3n-2)(n+3)P(n)a_{n-1},
$$

which is the exact consecutive-term ratio coming from our binomial closed form. To check the implication directly, set

$$
R(n) = \frac{3(3n-1)(3n-2)(n+3)P(n)}{2(n+1)(2n+3)(n+2)P(n-1)}.
$$

If `A(n)`, `B(n)`, and `C(n)` are the three coefficients of the OEIS recurrence, then

$$
A(n)R(n)R(n-1) + B(n)R(n-1) + C(n) = 0.
$$

We verified both the factorizations and the zero numerator with exact polynomial arithmetic during this audit. For every integer `n ≥ 2`, all denominators in $R(n)$ are nonzero, so jOEIS's first-order recurrence implies the three-term recurrence. This comparison is our own check of the two sources; the jOEIS repository itself does not contain that derivation.

In short, jOEIS gives earlier computational code without a written proof or proof-assistant certificate. It rules out claiming the underlying recurrence calculation is new, without showing who first proved the exact three-term identity.

## Established methods and related literature

* Petkovšek, Wilf, and Zeilberger's [*A=B*](https://sites.math.rutgers.edu/~zeilberg/AeqB.pdf), §§3.2-3.3, 5.2, and 5.6, covers rational consecutive-term ratios and turning hypergeometric identities into polynomial ones. Our proof uses that standard machinery.
* Mathar's [*P-finite Recurrences From Generating Functions with Roots of Polynomials*](https://arxiv.org/abs/2109.02112) (2021), [§5.1, equations (49)-(52)](https://arxiv.org/html/2109.02112v1#S5.SS1), derives first-order recurrences for hypergeometric coefficients. We found no mention of A026019 or its exact recurrence in the full text.
* We checked [Drube, *Raised k-Dyck Paths* (2022)](https://arxiv.org/html/2206.01194v1) and found no proof of this exact recurrence.
* The component sequences [A005809](https://oeis.org/A005809) and [A004321](https://oeis.org/A004321) already list polynomial recurrences. They give background, not a prior proof of this difference recurrence.

## Search coverage and limits

We searched by sequence ID, exact binomial formula, coefficient strings, Mathar's papers, related OEIS entries, and public GitHub repositories. Representative queries:

```text
"A026019" proof recurrence
"A026019" Mathar
"499*n^3-7*n^2-120*n-54"
"13*n-9" "37*n-24"
"A026019" Lean Isabelle Coq
```

GitHub searches for `A026019` in Lean, Isabelle, and Coq files returned no matching formalization. Searches like this can miss differently named theorems, unindexed or private repositories, books, unpublished notes, or proofs that omit the OEIS ID. We did not contact authors or search subscription databases exhaustively, so any first-formalization claim is also unverified.
