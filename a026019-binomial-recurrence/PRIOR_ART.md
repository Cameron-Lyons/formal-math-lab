# A026019: prior-art and novelty audit

Checked **November 23, 2026**. The target is the exact three-term recurrence
in `A026019.recurrence`, for the binomially defined sequence and every `n ≥ 2`.

**Assessment:** no earlier explicit proof of the exact three-term recurrence
or matching Lean formalization was located in this search. This is not a
certificate of historical priority. A first-order recurrence that implies the
target was already implemented in jOEIS before this project. Describe the
result as a checked Lean proof; do not claim a first mathematical proof or a
new recurrence.

## OEIS and the exact statement

The retrieved, search-indexed [A026019 entry](https://oeis.org/A026019) labels
the recurrence a conjecture attributed to R. J. Mathar, June 20, 2013. It also
records a generating function attributed to Mark van Hoeij, November 9, 2011.
There is no proof attached in that retrieved entry. The retained conjecture
label does not establish that no proof exists elsewhere.

The indexed [internal snapshot](https://oeis.org/A026019/internal) inspected
in the parallel search identifies entry revision 26, September 6, 2025. The
site-wide footer date must not be mistaken for the entry's revision date.

Direct requests for the live entry, internal format, JSON search result, and
revision history returned HTTP 403 during this audit. Thus the search-indexed
entry was inspected, but the complete current OEIS history was not verified.

## Earlier first-order recurrence: jOEIS

Georg Fischer's jOEIS implementation of A026019 was changed from direct
binomial evaluation to a first-order polynomial recurrence in
[commit 06f94740c2d0d4b0815dedce8d41dd008ef0c1b8](https://github.com/archmageirvine/joeis/commit/06f94740c2d0d4b0815dedce8d41dd008ef0c1b8),
dated **November 6, 2026, 22:46:25 UTC**. The
[immutable source](https://github.com/archmageirvine/joeis/blob/06f94740c2d0d4b0815dedce8d41dd008ef0c1b8/src/irvine/oeis/a026/A026019.java)
contains coefficient arrays

```text
p0 = [-36, 42, 216, 147, -540, -189]
p1 = [36, -18, -70, 50, 94, 28]
```

in ascending powers of `n`, with `p0(n)*a(n-1) + p1(n)*a(n) = 0`.

Here is our algebraic interpretation of that earlier code. Put
\(P(n)=7n^2+6n+2\). Its recurrence factors as

\[
2(n+1)(2n+3)(n+2)P(n-1)a_n
=3(3n-1)(3n-2)(n+3)P(n)a_{n-1}.
\]

This is precisely the consecutive-term ratio obtained from the binomial
closed form proved in the local project. For a direct check of the implication,
define

\[
R(n)=\frac{3(3n-1)(3n-2)(n+3)P(n)}
 {2(n+1)(2n+3)(n+2)P(n-1)}.
\]

If `A(n)`, `B(n)`, and `C(n)` are the three coefficients of the OEIS recurrence,
then

\[
A(n)R(n)R(n-1)+B(n)R(n-1)+C(n)=0.
\]

The coefficient factorizations and the identically zero numerator were checked
using exact polynomial arithmetic during this audit. For integer `n ≥ 2`, all
ratio denominators are nonzero. Thus the earlier first-order recurrence implies
our three-term recurrence. This implication is our checked comparison of the
sources, not a claim that the repository contains that derivation.

The inspected implementation provides prior computational evidence, without
an accompanying mathematical derivation or proof-assistant certificate. It
therefore prevents a claim that the underlying recurrence computation is new,
but does not establish who first proved the exact target.

## Established methods and related literature

- Petkovšek, Wilf, and Zeilberger's [*A=B*](https://sites.math.rutgers.edu/~zeilberg/AeqB.pdf),
  §§3.2–3.3, 5.2, and 5.6, treats rational consecutive-term ratios and reduction
  of hypergeometric identities to polynomial identities. Our proof uses this
  established elementary machinery.
- Mathar's [*P-finite Recurrences From Generating Functions with Roots of
  Polynomials*](https://arxiv.org/abs/2109.02112), submitted in 2021,
  [§5.1, equations (49)–(52)](https://arxiv.org/html/2109.02112v1#S5.SS1),
  derives first-order recurrences for hypergeometric coefficients. No mention
  of A026019 or its exact recurrence was located in the inspected full text.
- The neighboring-sequence reference [Drube, *Raised k-Dyck Paths*
  (2022)](https://arxiv.org/html/2206.01194v1) was checked; no exact-target proof
  was located.
- The component sequences [A005809](https://oeis.org/A005809) and
  [A004321](https://oeis.org/A004321) already have polynomial recurrences listed.
  They provide background, not by themselves a citation for a prior proof of
  the specific difference recurrence.

## Search coverage and limits

The search covered the sequence identifier, exact binomial formula, distinctive
coefficient strings, relevant Mathar literature, related OEIS entries, and
public GitHub code. Representative queries included:

```text
"A026019" proof recurrence
"A026019" Mathar
"499*n^3-7*n^2-120*n-54"
"13*n-9" "37*n-24"
"A026019" Lean Isabelle Coq
```

GitHub searches for `A026019` in Lean, Isabelle, and Coq files found no matching
formalization. Searches may miss differently named theorems, unindexed or
private repositories, books, unpublished work, or proofs without the sequence
identifier. No author correspondence or exhaustive subscription-database
search was performed. A first-formalization claim is therefore also unverified.
