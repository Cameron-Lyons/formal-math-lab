# Graham’s rearrangement problem modulo 41

**Every subset of the 40 nonzero residues modulo 41 has an ordering with pairwise distinct nonempty partial sums.** A computer-assisted proof covers all $2^{40}$ subsets. A separate constructive proof works at every prime $p\ge5$ for sets of size $p-4$. [All-prime proof for size $p-4$](paired-triple.md) · [Erdős problem #475](https://www.erdosproblems.com/475)

## Reduction to sets of sum zero

Let $p$ be an odd prime. A nonempty zero-sum set has a valid ordering exactly when its elements can be used as the successive steps of a simple cycle in $\mathbb F_p$. The last running sum is zero, so all proper running sums must be distinct and nonzero. Starting the cycle at any vertex preserves this property.

Fix a size $2\le k\le p-3$ and suppose every zero-sum set of that size has such a cycle. Let $A$ have size $k$ and total $s\ne0$. There is an $a\in A$ such that $b=a-s$ lies outside $A\cup\{0\}$. Otherwise, on writing residues as $js$ with $1\le j\le p-1$, every $js\in A$ with $j>1$ forces $(j-1)s\in A$. This makes $A=\{s,2s,\ldots,ks\}$, so $k(k+1)/2\equiv1\pmod p$. Equivalently $(k-1)(k+2)\equiv0\pmod p$, impossible in the given size range.

Replace $a$ by $b$ to obtain a zero-sum set. Rotate its cycle to put $b$ first, then replace $b$ by $a$. Every nonempty running sum increases by the same $s$, preserving distinctness. A related replacement argument appears in an earlier draft. [Atomicium, zero-sum reduction](https://github.com/Atomicium-org/graham-rearrangement-certificates/blob/23cb1d03e718d0798ff79161bff516444e7ca335/paper/graham_rearrangement_candidate.tex#L3513-L3575)

The four endpoint sizes need no search. Empty sets and singletons are immediate. For size $p-1$, choose a generator $g$ of $\mathbb F_p^\times$ and use the steps $d,dg,\ldots,dg^{p-2}$. The running sums $d(g^j-1)/(g-1)$ are distinct for $1\le j\le p-1$. For size $p-2$ take $d$ to be the missing residue and drop the first step. The remaining running sums are a subset of the original sums translated by $-d$.

## Exhaustion at 41

Encode a set of size $k$ by its membership in the order $1,6,6^2,\ldots,6^{39}$ modulo 41. The verifier checks that these are all 40 nonzero residues. Rotating the word multiplies the set by a nonzero scalar, preserving zero total and any valid cycle. Give an included residue weight $k-40$ and an omitted one weight $k$. The total weight is zero. Starting just after a minimum of the cumulative weights gives a rotation whose prefix weights are all nonnegative. This guarantees that each orbit occurs, including words with several possible starting positions.

The C++ program generates the first 20 positions forwards and the last 20 backwards. Both walks start at height zero and use the corresponding nonnegativity test. It joins halves whose omission counts add to $40-k$ and whose omitted residues sum to zero modulo 41. The counts force the two heights to agree at the midpoint. The sum test is equivalent to zero total for the included residues because all 40 residues together sum to zero. Every selected word is produced by exactly one pair of halves.

For each word a depth-first search finds an ordering and the checker replays it, verifying the step set, final sum zero, and exactly $k$ different nonempty running sums. Across sizes 2 through 38 the run checked **766,546,584 words**. They cover **670,460,215 dilation orbits** containing **26,817,356,774 zero-sum sets**. The reduction above extends the result to all totals. [C++ cycle search and witness checks](verify_zero_sum.cpp)

The independent Python calculation counts the eligible words one position at a time by cardinality, residue sum, and number of returns to height zero. It compares every size with the C++ transcript. A word with $r$ returns (including the endpoint) has $r$ admissible starting positions among its 40 labelled cuts. Weighting that word by $40/r$ recovers the total number of zero-sum sets, even for periodic words. The checker verifies this against the roots-of-unity count $(\binom{40}{k}+40(-1)^k)/41$. It also counts the dilation orbits separately by Burnside’s lemma. [Independent count checker](verify_counts.py)

## Reproduce the full modulo-41 proof

Run from this directory with a C++20 compiler and Python 3.10 or later. OpenMP parallelizes the sizes. Omitting `-fopenmp` runs the same search on one thread.

~~~sh
c++ -std=c++20 -O3 -march=native -fopenmp verify_zero_sum.cpp -o /tmp/graham41
/tmp/graham41 --all > /tmp/graham41-counts.txt
python3 verify_counts.py /tmp/graham41-counts.txt
~~~

The final line is `All 37 transcript counts match.`

## Earlier direct verification at size 27

**Every 27-element set of nonzero residues modulo 41 can be ordered so that its 27 nonempty running sums are distinct.**

**Computer-assisted proof.** Multiplying every element by the same nonzero residue multiplies every running sum by that residue, preserving distinctness. If a set has nonzero total $s$, multiply it by $s^{-1}$ to make its total 1. Thus it suffices to check sets of total 0 or 1.

The verifier checked **all 586,986,481 such sets**. For each it found an ordering and recomputed the 27 running sums. All were distinct, and the first 26 were nonzero. Scaling back gives the claimed ordering for the original set. [Verifier](verify.cpp)

To see why the list is exhaustive, describe a set by the 13 residues it omits. The verifier chooses the first 12 omissions in increasing order. If the remaining 28 residues sum to $r$, the last omission must be $r$ for a set of total 0, or $r-1$ for a set of total 1, modulo 41. It checks each candidate larger than the twelfth omission.

### Reproduce the size-27 cross-check

Run from this directory with a C++20 compiler. OpenMP is optional.

~~~sh
c++ -std=c++20 -O3 -march=native -fopenmp verify.cpp -o /tmp/erdos475
/tmp/erdos475
~~~

The output is `586986481 sets verified`.

[Independent three-second proof using zero-sum sets](zero-sum.md) · [Erdős problem #475](https://www.erdosproblems.com/475) · [Arévalo's verification for sizes 28–40](https://fabianarevalo.com/graham-rearrangement) · [Prior-art notes](../PRIOR_ART.md#erdős-475-size-27-modulo-41)
