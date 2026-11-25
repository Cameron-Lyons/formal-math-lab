# Erdős Problem #708 (Erdos #708) for n = 6: g(6) = 8 — Lean 4 proof

**Exact value proved in Lean 4: $g(6) = 8$.** Let $A$ be any set of **six** distinct integers $\ge 2$, and let $M = \max A$. From every block of $M$ consecutive integers, one can choose at most **8** distinct entries whose product is divisible by $\prod_{a \in A} a$ — and some sets $A$ and blocks require 8.

The general Erdős Problem #708 question — whether $g(n) \le 2n$ for all $n$ (or $g(n) = (2 + o(1))n$) — remains open. C. Bergström previously proved $g(6) = 8$ (19 November 2026); this project supplies a machine-checked Lean 4 proof building on John Tripodo's Lean formalizations of $g(4) = 5$ and $g(5) = 6$.

| Field | Summary |
| --- | --- |
| **Problem & identifiers** | **Erdős Problem #708** (`Erdos #708`, `erdosproblems.com/708`), interval products for $n = 6$ integers, exact value **$g(6) = 8$** |
| **Status** | **Case $n = 6$ completely proved in Lean 4 ($g(6) = 8$).** General bound $g(n) \le 2n$ remains open. |
| **Main Lean theorems** | `Erdos708.isLeast_six`, `Erdos708.erdos_708.variants.g_six`, `IntervalSix.six_upper`, `IntervalSix.six_integer` in [Six.lean](Six.lean) |
| **Verification** | `lake exe cache get && lake build && lake env lean Six.lean` (Lean 4.35.0-rc2 + mathlib + pinned Tripodo development) |
| **Prior-art status** | Checked **23 November 2026**: C. Bergström (19 November 2026, `10.5281/zenodo.24366897`) previously proved $g(6) = 8$. This Lean proof adapts Bergström's lower-bound witness and cumulative-gcd rule and imports John Tripodo's Lean bounds for $n = 4, 5$. See [PRIOR_ART.md](../PRIOR_ART.md#erdős-708-interval-products-for-six-integers). |

## Why seven can fail ($g(6) \ge 8$)

Take the six products $A = \{13, 17, 19\} \cdot \{19, 23\}$, whose maximum is $M = 19 \cdot 23 = 437$. Center a block of 437 consecutive integers at $h = 2 \cdot 13 \cdot 17 \cdot 19^2 \cdot 23$, so its entries are $h + j$ for $-218 \le j \le 218$.

Only $h$ can supply two different primes from $\{13, 17, 19, 23\}$: their product would divide $j$, and even the smallest pair gives $13 \cdot 17 = 221 > 218$. Away from $h$, no entry supplies $19^2$ or $23^2$ either (the nearest other multiples of $19^2 = 361$ are 361 away, and $h \bmod 23^2 = 253$ puts the nearest other multiple of $23^2$ at distance 253).

* **Choose $h$.** The remaining product still needs $13, 17, 19, 19, 19, 23, 23$, each requiring a separate additional entry: **8** entries in total.
* **Omit $h$.** The five copies of 19 and three copies of 23 already require **8** distinct entries.

Eight entries succeed at offsets $0, 13, 17, 19, 38, 57, 23, 46$. This example interchanges 17 and 19 in Bergström's Proposition 3 construction and uses a smaller center. [Lean witness](SixLower.lean) · [Bergström, Proposition 3](https://doi.org/10.5281/zenodo.24366897)

## Why eight always suffice ($g(6) \le 8$)

Tripodo's pinned Lean development covers any five integers in at most 6 entries (and any four in at most 5). If the sixth integer splits as $uv$ with $7u \le M$ and $8v \le M$, append an unused multiple of $u$ and an unused multiple of $v$; the block offers at least 7 and 8 candidates, respectively. [Tripodo's preprint](https://hexagonmath.org/pdf/2611.00694v1) · [Lean extension](PriorBounds.lean)

For $M \ge 70$, every integer that resists this split has a prime factor $p > M / 8$, except $75$ when $M \le 104$ and $125$ when $125 \le M \le 174$. Indeed, any divisor in $[8, M/7]$ supplies a split, as does divisibility by $7$; without a large prime, only prime factors $2, 3, 5$ remain and neither $8$ nor $9$ divides it, so it divides $60 = 10 \cdot 6$ and splits unless it is a multiple of $25$ (forcing $M < 175$, leaving only $25, 50, 75, 100, 125, 150$ to check). [Divisor proof](Exceptions.lean)

Group the elements of $A$ divisible by a large prime $p > M/8$. Their cofactors lie in $\{1, \ldots, 7\}$ and are distinct. A group of size $d \le 3$ needs at most $d$ entries by a finite check on these cofactors in the interval of multiples of $p$. Joining this cover to a cover for the remaining elements gives their lcm if they overlap; the missing gcd divides the product of the group's cofactors, so one fresh multiple per cofactor suffices. [Cofactor lemma](SixStructure.lean) · [Joining covers](SixGroups.lean)

* **Two or more large primes:** their groups are disjoint since their product exceeds $M$. A group of 1 or 2 leaves 5 or 4 originals (covered in 6 or 5 entries by Tripodo); otherwise there are two triples. With overlap, the counts are $1 + 6 - 1 + 1 = 7$, $2 + 5 - 1 + 2 = 8$, and $3 + 3 - 1 + 3 = 8$.
* **One large prime divides all six:** take $s = \lfloor M/p \rfloor \le 7$ consecutive multiples of $p$; their quotients have product divisible by $s!$, supplying every cofactor.
* **Five share a large prime and the sixth is the exception $e \in \{75, 125\}$:** cover the five in 6 entries and pick a multiple of $e$. If it overlaps, the missing gcd divides $\gcd(7!, 375) = 15$, and fresh multiples of 3 and 5 finish the cover. [Large-window proof](SixLarge.lean)

For $M < 70$, Lean builds factor sequences using Bergström's cumulative-gcd rule: append $d \le M$ to a product $t$ covered in $k$ entries whenever $(k + 1)\gcd(t, d) \le M$. Two targets use direct greedy selection over every residue start modulo 180 or 120. [Factor sequences](SixFinite.lean) · [Residue check](SixResidues.lean)

## Reproduce

With Elan installed (pinned Lean **4.35.0-rc2**), run from this directory:

```sh
lake exe cache get
lake build
lake env lean Six.lean
```

The last command prints the axioms for `Erdos708.isLeast_six` and `IntervalSix.six_integer`. The project pins [Tripodo's Lean development](https://github.com/jjtripodo-lgtm/erdos-708-g4-g5/tree/00fbb23c3084daa88ea420aa9c74177127d5283f).

## References

* [Erdős Problems #708](https://www.erdosproblems.com/708)
* [C. Bergström (19 November 2026), Proposition 3 and Theorems 6 & 12](https://doi.org/10.5281/zenodo.24366897)
* [John Tripodo, preprint (`g(4) = 5` and `g(5) = 6` in Lean)](https://hexagonmath.org/pdf/2611.00694v1)
* [Dated prior-art audit](../PRIOR_ART.md#erdős-708-interval-products-for-six-integers)
