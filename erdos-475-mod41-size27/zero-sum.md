# An independent check using zero-sum sets

This note documents the **multiplicative-rotation verifier** — originally built to settle size $27$ modulo $41$, and then extended across all sizes modulo $41$ and $43$ as an independent cross-check of the reciprocal-sum verifier — along with a separate direct check at size $27$.

## Why zero-sum sets suffice at size 27 modulo 41

A valid ordering of a zero-sum set traces a simple closed cycle through $0$. At size $27$ modulo $41$, a sharp form of the replacement trick shows we can reduce any size-27 set to a zero-sum set of the **exact same size 27** (without ever needing to increase the size to $28$):

Let $A \subseteq \mathbb{F}_{41}^\times$ have size $27$ and nonzero total $s$. We claim there exists an element $a \in A$ such that $b = a - s$ lies outside $A \cup \{0\}$. Indeed, if no such $a$ existed, then whenever $js \in A$ (for $2 \le j \le 40$) we would be forced to have $(j - 1)s \in A$. Walking backwards along the multiples of $s$, the 27-element set $A$ would have to be the initial block $\{s, 2s, \ldots, 27s\}$. Its sum would then be
$$\sum_{j=1}^{27} js = \frac{27 \cdot 28}{2}\, s = 378s \equiv 9s \ne s \pmod{41},$$
a contradiction.

Replacing $a$ by $b = a - s$ therefore produces a zero-sum subset $B$ of size $27$. Rotating a valid cycle for $B$ so that $b$ comes first, then replacing $b$ back with $a$, adds the same constant $s$ to every nonempty running sum, preserving distinctness and giving a valid ordering of $A$. ([Related reduction in the Atomicium draft](https://github.com/Atomicium-org/graham-rearrangement-certificates/blob/23cb1d03e718d0798ff79161bff516444e7ca335/paper/graham_rearrangement_candidate.tex#L3513-L3575))

## Picking one rotation per scaling orbit

Since multiplying a subset $A \subseteq \mathbb{F}_{41}^\times$ by any nonzero scalar preserves both its zero-sum property and distinctness of partial sums, we only need to check one set from each multiplicative scaling orbit.

**Turning scaling into cyclic shifts.** Because $6$ is a primitive root modulo $41$, the powers $1, 6, 6^2, \ldots, 6^{39}$ list all $40$ nonzero residues in a circle. Representing a subset $A$ as a 40-bit cyclic word in this order turns multiplication by $6$ into a **cyclic rotation** by one position.

**Canonical rotations via nonnegative cumulative weights.** Assign each omitted residue weight $+27$ and each included residue weight $-13$. For a 27-element subset (13 omissions and 27 inclusions), the total weight around the circle is
$$13 \cdot 27 + 27 \cdot (-13) = 0.$$
Walk around the circle tracking the cumulative weight, and start the cyclic word immediately after a position where the cumulative weight attains its **minimum**. From that starting point onward, every cumulative prefix weight is **nonnegative**. Every scaling orbit therefore has a rotation with all cumulative weights nonnegative!

**Meet-in-the-middle enumeration.** The verifier ([verify_zero_sum.cpp](verify_zero_sum.cpp)) generates all such 40-position words by splitting the circle into two 20-position halves and joining halves whose weights stay nonnegative and whose total omissions number $13$ with residue sum $0 \pmod{41}$. (Since the full set $\mathbb{F}_{41}^\times$ sums to $0$, the 13 omitted residues sum to $0$ if and only if the 27 included residues sum to $0$.)

It found and verified a simple cycle in every one of the **7,337,331** cases.

### Reproduce the size-27 rotation check

Run from this directory. The run took 3.1 seconds on one Intel Core Ultra 5 325 CPU thread with GCC 16.2.1:

~~~sh
c++ -std=c++20 -O3 -march=native verify_zero_sum.cpp -o /tmp/erdos475-zero
/tmp/erdos475-zero
~~~

## Extending to all sizes modulo 41

Passing `--all` runs the exact same rotation argument across sizes $k = 2$ through $38$, using weight $+k$ for omitted residues and weight $k - 40$ for included residues (which again has total weight $(40 - k)k + k(k - 40) = 0$). The remaining four sizes require no search:
* $k = 0$ (empty set): immediate.
* $k = 1$ and $k = 39$ (a single residue, or all but one residue): cannot sum to $0 \pmod{41}$.
* $k = 40$ (the full set $\mathbb{F}_{41}^\times$): consists of 20 opposite pairs, so it has a cycle by the [opposite-pair construction](paired-triple.md#make-a-cycle-from-opposite-pairs).

The transcript can be audited against exact combinatorial counts with `verify_counts.py`:

~~~sh
/tmp/erdos475-zero --all > /tmp/graham41-counts.txt
python3 verify_counts.py /tmp/graham41-counts.txt
~~~

## Direct size-27 verification

As a third check at size $27$ modulo $41$, a separate [direct verifier](verify.cpp) bypasses the zero-sum reduction: it scales every nonzero total to $1$ and checks all **586,986,481** subsets of size $27$ with total $0$ or $1$:

~~~sh
c++ -std=c++20 -O3 -march=native -fopenmp verify.cpp -o /tmp/erdos475-direct
/tmp/erdos475-direct
~~~
