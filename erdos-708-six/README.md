# Erdős Problem #708 for six integers: g(6) = 8

Pick any set $A$ of $n$ distinct integers $\ge 2$, and let $M = \max A$ be its largest element. Now take *any* block of $M$ consecutive integers. Define $g(n)$ as the smallest number $k$ such that—for every choice of $A$ and every block of $M$ consecutive integers—you can always select at most $k$ distinct numbers from the block whose product is divisible by $\prod_{a \in A} a$.

**Erdős Problem #708** asks whether $g(n) \le 2n$ for all $n$ (or asymptotically $g(n) = (2 + o(1))n$). That general question remains **open**. For $n = 6$, this Lean 4 project proves unconditionally that **$g(6) = 8$**:

* **Upper bound ($g(6) \le 8$):** 8 distinct entries from the block always suffice.
* **Lower bound ($g(6) \ge 8$):** some choices of six integers and blocks genuinely need all 8 entries.

C. Bergström proved $g(6) = 8$ on 19 November 2026 (`10.5281/zenodo.24366897`). This directory gives a Lean 4 formalization adapting Bergström's lower-bound witness and cumulative-gcd rule, built on John Tripodo's pinned Lean formalizations of $g(4) = 5$ and $g(5) = 6$.

## At a glance

| Field | Summary |
| --- | --- |
| Problem | Erdős Problem #708 (`erdosproblems.com/708`), interval products for $n = 6$ integers, $g(6) = 8$ |
| Status | Case $n = 6$ proved in Lean 4 ($g(6) = 8$). General bound $g(n) \le 2n$ is still open. |
| Main theorems | `Erdos708.isLeast_six`, `Erdos708.erdos_708.variants.g_six`, `IntervalSix.six_upper`, `IntervalSix.six_integer` in [Six.lean](Six.lean) |
| Verification | `lake exe cache get && lake build && lake env lean Six.lean` (Lean 4.36.0 + mathlib + pinned Tripodo development) |
| Prior art | Checked 23 November 2026: C. Bergström (19 November 2026, `10.5281/zenodo.24366897`) proved $g(6) = 8$. This Lean proof adapts Bergström's lower-bound witness and cumulative-gcd rule and imports John Tripodo's Lean bounds for $n = 4, 5$. |

## Why seven can fail ($g(6) \ge 8$)

**The idea.** Pack four primes $\{13, 17, 19, 23\}$ into a single center integer $h$ inside a block of length $M = 437$, so that *every other* integer in the block can contribute at most **one** prime factor (to the first power) from $\{13, 17, 19, 23\}$.

Take the six products

$$
A = \{13, 17, 19\} \cdot \{19, 23\} = \{247, 299, 323, 361, 391, 437\},
$$

whose maximum is $M = 19 \cdot 23 = 437$ and whose product is $13^2 \cdot 17^2 \cdot 19^5 \cdot 23^3$. Center a block of 437 consecutive integers at

$$
h = 2 \cdot 13 \cdot 17 \cdot 19^2 \cdot 23,
$$

so its entries are $h + j$ for $-218 \le j \le 218$.

* **No other entry carries two distinct primes from $\{13, 17, 19, 23\}$:** Since all four primes divide $h$, any $h + j$ ($j \ne 0$) divisible by two of them must have their product dividing $j$. Even the smallest pair gives $13 \cdot 17 = 221 > 218 \ge |j|$, impossible.
* **No other entry carries $19^2$ or $23^2$:** The nearest other multiples of $19^2 = 361$ lie 361 away from $h$, and since $h \bmod 23^2 = 253$, the nearest other multiples of $23^2 = 529$ lie at distance at least 253 from $h$ (both exceeding 218).

Every entry other than $h$ therefore supplies at most one factor from $\{13, 17, 19, 23\}$. Now check both options:

* **Choose $h$:** $h$ contributes $13 \cdot 17 \cdot 19^2 \cdot 23$, leaving $13, 17, 19, 19, 19, 23, 23$ still needed — 7 separate entries, for **8 entries** in total.
* **Omit $h$:** just supplying the five copies of $19$ and three copies of $23$ already forces **8 distinct entries**.

Eight entries *do* succeed at offsets $0, 13, 17, 19, 38, 57, 23, 46$. This swaps 17 and 19 in Bergström's Proposition 3 construction and uses a smaller center ([SixLower.lean](SixLower.lean), [Bergström Proposition 3](https://doi.org/10.5281/zenodo.24366897)).

## Why eight always suffice ($g(6) \le 8$)

**Proof strategy.** Split into large maximum ($M \ge 70$) and small maximum ($M < 70$). For $M \ge 70$, bootstrap from John Tripodo's Lean bounds for 4 and 5 integers ($g(4) = 5$, $g(5) = 6$): if *any* of the six integers splits into two modest factors, cover the other five in 6 entries and add two fresh multiples ($6 + 2 = 8$). If *none* splits, almost every member of $A$ must be divisible by a large prime $p > M/8$, which groups the six numbers into just three tractable configurations.

### Step 1: The splitting trick (for $M \ge 70$)

Tripodo's pinned Lean development covers any 5 integers in at most 6 entries and any 4 integers in at most 5 ([preprint](https://hexagonmath.org/pdf/2611.00694v1), [PriorBounds.lean](PriorBounds.lean)). Suppose some sixth integer splits as $a = uv$ with $7u \le M$ and $8v \le M$. Cover the other five integers in at most 6 entries. Because a block of $M$ consecutive integers holds at least $\lfloor M/u \rfloor \ge 7$ multiples of $u$ and at least $\lfloor M/v \rfloor \ge 8$ multiples of $v$, we can greedily append one unused multiple of $u$ and then one unused multiple of $v$, reaching at most $6 + 2 = 8$ entries.

### Step 2: What resists splitting ($M \ge 70$)

When $M \ge 70$, **every** integer $a \le M$ that fails to split as above must have a prime factor $p > M/8$ — with only two exceptions:

* $75$ (when $M \le 104$), and
* $125$ (when $125 \le M \le 174$).

*Why?* Any divisor $u$ of $a$ in $[8, M/7]$ immediately gives a split (with $v = a/u \le M/8$), and divisibility by $7$ also gives a split ($7(a/7) = a \le M$ and $8 \cdot 7 = 56 \le 70 \le M$). Without a prime factor $> M/8$ (and hence without any prime $\ge 7$), only the primes $2, 3, 5$ remain, and neither $8$ nor $9$ can divide $a$ (since both lie in $[8, M/7]$ for $M \ge 70$). Thus $a$ divides $60 = 10 \cdot 6$ and splits unless $25 \mid a$. If $25 \mid a$, keeping $25 \notin [8, M/7]$ forces $M < 175$, leaving only the six multiples $25, 50, 75, 100, 125, 150$ to check in [Exceptions.lean](Exceptions.lean).

### Step 3: Grouping by large primes and overlap repair

For each large prime $p > M/8$, group the elements of $A$ divisible by $p$. Each member has the form $p \cdot c$ with distinct **cofactors** $c \in \{1, \ldots, 7\}$. A finite check on these cofactors inside the interval of multiples of $p$ shows that a group of size $d \le 3$ can be covered in at most $d$ entries.

**Overlap repair:** Suppose we combine a cover of a $p$-group with a cover of the remaining elements. If the two covers are disjoint, their union's product already works. If they overlap (saving at least 1 entry from the sum of their sizes), their union covers the LCM rather than the full product; the missing factor divides the $\gcd$ of the two targets, which divides the product of the $p$-group's cofactors (since $p$ does not divide the remaining elements). Appending at most one fresh multiple per cofactor finishes the product ([SixStructure.lean](SixStructure.lean), [SixGroups.lean](SixGroups.lean)).

This leaves three exhaustive cases for $M \ge 70$:

* **Two or more large primes:** Their groups are disjoint because the product of two primes $> M/8$ exceeds $(M/8)^2 > M$ for $M \ge 70$. If a group has size 1 or 2, the remaining 5 or 4 elements take at most 6 or 5 entries by Tripodo's bounds; otherwise the six elements split into two triples. Even with overlap repair, the entry counts are at most:
  * size 1 + remaining 5: $1 + 6 - 1 + 1 = 7$,
  * size 2 + remaining 4: $2 + 5 - 1 + 2 = 8$,
  * two triples: $3 + 3 - 1 + 3 = 8$.
* **One large prime divides all six:** Take all $s = \lfloor M/p \rfloor \le 7$ consecutive multiples of $p$ in the block. Their quotients by $p$ are $s$ consecutive integers, so their product is divisible by $s!$, covering every distinct cofactor in at most $s \le 7$ entries.
* **Five share a large prime $p$ and the sixth is an exception $e \in \{75, 125\}$:** Cover the five in at most 6 entries and add one multiple of $e$. If that multiple overlaps the first 6 entries, the missing $\gcd$ divides $\gcd(7!, 375) = 15$, so appending fresh multiples of $3$ and $5$ finishes the cover in at most $6 + 1 - 1 + 2 = 8$ entries ([SixLarge.lean](SixLarge.lean)).

### Step 4: Small cases ($M < 70$)

For $M < 70$, Lean constructs factor sequences using Bergström's **cumulative-gcd rule**: append a factor $d \le M$ to a product $t$ already covered in $k$ entries whenever $(k + 1)\gcd(t, d) \le M$ (so any overlap can be repaired by picking an unused multiple of $\gcd(t, d)$). Two targets use direct greedy selection over every residue start modulo 180 or 120 ([SixFinite.lean](SixFinite.lean), [SixResidues.lean](SixResidues.lean)).

## Reproduce

With `elan` installed (pinned Lean 4.36.0), run from this directory:

```sh
lake exe cache get
lake build
lake env lean Six.lean
```

The last command prints the axioms for `Erdos708.isLeast_six` and `IntervalSix.six_integer`. The package pins [Tripodo's Lean development](https://github.com/jjtripodo-lgtm/erdos-708-g4-g5/tree/af658b33f0e94f0d11088fd5d07b12af41e1e760).

## References

* [Erdős Problems #708](https://www.erdosproblems.com/708)
* [C. Bergström (19 November 2026), Proposition 3 and Theorems 6 & 12](https://doi.org/10.5281/zenodo.24366897)
* [John Tripodo, preprint (`g(4) = 5` and `g(5) = 6` in Lean)](https://hexagonmath.org/pdf/2611.00694v1)
