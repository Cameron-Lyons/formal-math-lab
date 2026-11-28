# Exact gaps for 58 through 200

Let $\delta(N)$ be the least positive value of $|1-\sum_{a\in A}1/a|$ over subsets of $\{1,\ldots,N\}$. The table gives each interval on which the computed value is constant. Its signed fraction is the displayed witness's reciprocal sum minus one. For instance,
$$
\delta(98)=\delta(99)=\delta(100)
  =\frac{13914972457}{1415221188454793086396836206400}.
$$
[Exact fractions and denominators](exact_gaps.tsv) · [Earlier table through 60](https://github.com/arhancanli/quantavane-erdos-results/blob/main/311/results/table.md)

## Computation

Write $L=\operatorname{lcm}(1,\ldots,N)$. Select a divisor $D$ of $L$ and divide the allowed denominators into two groups. Denominators in the first group divide $D$, so their contribution after multiplication by $L$ is a multiple of $M=L/D$. The second group includes every remaining denominator from 2 to $N$. Including denominator 1 yields exact equality or an error at least $1/N$, which the witnesses improve on.

The search divides the second group in half. For two subset totals $x$ and $y$ in units of $1/L$, their distance to the nearest multiple of $M$ is a lower bound on the gap numerator. A zero residue can only yield zero or a positive gap at least $M$. Below $M/2$, only the nearest multiple can work. Sorting the residues of $y$ and searching in both directions from $-x$ orders candidate distances. The first positive distance below $M/2$ that admits the required first-group contribution is the exact answer. The search checks the resulting witness with exact fractions.

To decide first-group feasibility, the search splits off a modest base divisor of $D$. It enumerates the attainable numerators over the base by bitset subset sums. The remaining first-group denominators fall into blocks according to the one prime for which their exponent exceeds the base exponent. The initial split moves any denominator exceeding the base exponent at multiple primes to the second group. For each prime, the target numerator over $D$ determines the required residue modulo the corresponding prime power in $D/\mathrm{base}$. The search tries the matching totals in each block and checks the remaining base numerator in the bitset. [Search](exact_gaps.py)

## Independent verification

For a table row $u\le N\le v$, an explicit witness at $u$ proves the upper bound on the entire interval. To prove the matching lower bound it suffices to rule out every smaller nonzero gap at $v$, since the available subsets increase with $N$.

The checker implements this decision computation separately. It uses all divisors of its chosen $D$ in the first group and splits the other denominators by alternating positions. A strict residue window around each left-half total gives all pairs capable of beating the claimed bound. For each surviving pair it tests the exact required first-group sum by removing successive prime factors of $D$. At a prime $p\mid D$, only denominators $d$ with $p\nmid D/d$ can contribute to the numerator modulo $p$. Enumerating those subsets and dividing the remaining target and scale by $p$ removes one factor. An exact bitset closes the recursion. The checker also verifies the ordering and continuity of the intervals and each signed witness using rational arithmetic. The numerical workload estimate used to choose $D$ has no role in an exclusion. [Checker](verify_exact.py)

From the repository root with Python 3.10 or later:

~~~sh
python3 research/erdos-311/verify_exact.py
python3 research/erdos-311/exact_gaps.py 98 100
~~~

The table concerns the stated finite range. Whether $-\log\delta(N)/N$ has a positive limit remains open.
