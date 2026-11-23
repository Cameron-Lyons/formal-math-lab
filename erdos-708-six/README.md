# Erdős #708 for six integers

**Eight is the exact answer.** Let $A$ be six distinct integers at least two, and let $M=\max A$. From every block of $M$ consecutive integers one can choose at most eight distinct entries whose product is divisible by $\prod_{a\in A}a$. [Lean theorem](Six.lean)

## Why seven can fail

Take the six products $A=\{13,17,19\}\cdot\{19,23\}$. Their maximum is $437$. Center a block of that length at $h=2\cdot13\cdot17\cdot19^2\cdot23$. Its entries are $h+j$ for $-218\le j\le218$.

Only $h$ can supply two different primes from $\{13,17,19,23\}$. Indeed, their product would divide $j$, and even the smallest pair gives $13\cdot17=221>218$. Away from $h$, no entry supplies $19^2$ or $23^2$, either. The nearest other multiples of $19^2$ are 361 away, and $h\bmod 23^2=253$ puts the nearest multiple of $23^2$ at distance 253.

* **Choose $h$.** The product still needs $13,17,19,19,19,23,23$. Each requires a different additional entry. That makes eight.
* **Omit $h$.** The five copies of 19 and three copies of 23 already require eight different entries.

Eight work at offsets $0,13,17,19,38,57,23,46$. This example interchanges 17 and 19 in Bergström’s construction and uses a smaller center. [Lean witness](SixLower.lean) · [Bergström, Proposition 3](https://doi.org/10.5281/zenodo.24366897)

## Why eight always suffice

Tripodo covers any five originals in six entries. If the sixth is $uv$ with $7u\le M$ and $8v\le M$, append an unused multiple of $u$, then an unused multiple of $v$. The block offers at least seven and eight candidates, respectively. [Preprint](https://hexagonmath.org/pdf/2611.00694v1) · [Lean extension](PriorBounds.lean)

For $M\ge70$, every original that resists this split has a prime factor $p>M/8$, apart from $75$ when $M\le104$ and $125$ when $125\le M\le174$. To see this, any divisor in $[8,M/7]$ supplies a split, as does divisibility by $7$. Without a large prime, only prime factors $2,3,5$ remain and neither $8$ nor $9$ divides the original. It therefore divides $60=10\cdot6$ and splits, unless it is a multiple of $25$. Then $M<175$, leaving just $25,50,75,100,125,150$ to test. [Divisor proof](Exceptions.lean)

Group the originals divisible by a large prime $p$. Their cofactors lie in $\{1,\ldots,7\}$ and are distinct. A group of size $d\le3$ needs at most $d$ entries, by a finite check on these cofactors in the interval of multiples of $p$. Join this cover to one for the other originals. If they overlap, their union supplies the lcm. The missing gcd divides the product of the group's cofactors, so one fresh multiple per cofactor suffices. [Cofactor lemma](SixStructure.lean) · [Joining covers](SixGroups.lean)

* Two large primes have disjoint groups since their product exceeds $M$. A group of one or two leaves five or four originals, covered in six or five entries by Tripodo. Otherwise there are two triples. With overlap the three counts are $1+6-1+1=7$, $2+5-1+2=8$, and $3+3-1+3=8$.
* If one prime divides all six, take $s=\lfloor M/p\rfloor\le7$ consecutive multiples of $p$. Their quotients have product divisible by $s!$, which supplies every cofactor.
* Otherwise five share a prime and the sixth is the exception $e$. Cover the five in six entries and choose a multiple of $e$. If it overlaps, the missing gcd divides $\gcd(7!,375)=15$, since the five cofactors are distinct and $e\mid375$. Fresh multiples of 3 and 5 finish the cover. [Large-window proof](SixLarge.lean)

For $M<70$, Lean builds factor sequences for the remaining sets. A sequence can append $d\le M$ to a product $t$ covered in $k$ entries whenever $(k+1)\gcd(t,d)\le M$. If a multiple of $d$ is already occupied, a fresh multiple of the gcd suffices. Two targets use direct greedy selection for each start modulo 180 or 120. These checks cover every translate. [Factor sequences](SixFinite.lean) · [Residue check](SixResidues.lean)

## Reproduce

With Elan installed, run from this directory

```sh
lake exe cache get
lake build
lake env lean Six.lean
```

The last command prints the axioms for the sharp bound and the integer-interval theorem. The project pins Tripodo's Lean development. Bergström also reports the value eight and gives the cumulative-gcd rule used above. [Bergström's manuscript](https://doi.org/10.5281/zenodo.24366897)
