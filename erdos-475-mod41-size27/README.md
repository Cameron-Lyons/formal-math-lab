# Graham’s rearrangement problem modulo 41, 43, and 47

Given a prime $p$, take any subset $A$ of the nonzero residues modulo $p$ ($\mathbb{F}_p^\times = \{1, 2, \ldots, p-1\}$). **Graham’s rearrangement conjecture** ([Erdős problem #475](https://www.erdosproblems.com/475)) asks whether the elements of $A$ can always be placed in some order $a_1, a_2, \ldots, a_m$ so that all nonempty partial sums
$$a_1, \quad a_1 + a_2, \quad \ldots, \quad a_1 + a_2 + \cdots + a_m$$
are pairwise distinct modulo $p$.

Think of the $p$ residues as points around a circle. An ordering of $A$ is a walk starting at $0$ that steps by $a_1$, then $a_2$, and so on, visiting the partial sums as vertices. Having distinct nonempty partial sums means the walk never revisits a vertex — except that when $\sum A \equiv 0 \pmod p$, the final step closes a **simple cycle** back at $0$.

This directory proves the conjecture completely for **$p = 41$, $43$, and $47$**, and gives an elementary constructive proof at **every prime $p$** whenever $A$ omits at most four nonzero residues.

| Result | Scope | Proof method | Write-up |
| --- | --- | --- | --- |
| Complete verification at $p = 47$ | All subsets of $\mathbb{F}_{47}^\times$ | Quadratic-residue split + 15-region pigeonhole gluing + C++ half-path verifier (plus independent splice check) | [modulo-47.md](modulo-47.md) |
| Complete verification at $p = 43$ | All subsets of $\mathbb{F}_{43}^\times$ | Zero-sum & reciprocal-sum reduction + C++ meet-in-the-middle verifier (plus independent rotation check) | [modulo-43.md](modulo-43.md) |
| Complete verification at $p = 41$ | All subsets of $\mathbb{F}_{41}^\times$ | Zero-sum & reciprocal-sum reduction + C++ meet-in-the-middle verifier (plus independent rotation & size-27 checks) | [Below](#the-finite-check-at-41) · [zero-sum.md](zero-sum.md) |
| At most 4 omitted residues | Every prime $p$ | Explicit alternating decreasing-magnitude ordering (covers any opposite pairs plus 3 or 4 unpaired residues of sum zero) | [paired-quartet.md](paired-quartet.md) · [paired-triple.md](paired-triple.md) |

## Reduction to sets of sum zero

**The big idea.** Checking only zero-sum subsets cuts the search space by a factor of $p$, and it gives us a geometric superpower: a valid ordering of a zero-sum set traces a closed simple cycle starting and ending at $0$, so **we can rotate the cycle to begin with any step we like**. (Rotating to start after partial sum $v$ simply shifts every vertex of the cycle by $-v \pmod p$, which preserves distinctness.)

Now let $A \subseteq \mathbb{F}_p^\times$ have nonzero total $s \pmod p$, where $p$ is an odd prime. We turn $A$ into a zero-sum set by changing a single step:

1. **Find a step that exits $A \cup \{0\}$.** Put $X = A \cup \{0\}$. Because the full set $\mathbb{F}_p^\times$ pairs every residue with its negative, its sum is $0 \ne s$; hence $X$ is a proper subset of $\mathbb{F}_p$. Repeatedly subtracting $s$ cycles through the entire field $\mathbb{F}_p$, so this cycle must step out of $X$ at least once: there exists $a \in X$ such that $b = a - s \notin X$ (in particular, $b \ne 0$ and $b \notin A$).
2. **Swap $a$ for $b$ to hit sum zero.** Define
   $$B = (A \setminus \{a\}) \cup \{b\}.$$
   If $a \in A$, we removed $a$ and inserted $b = a - s$, so $\sum B = s - a + (a - s) = 0$ and $|B| = |A|$. If $a = 0$, then $B = A \cup \{-s\}$, so $\sum B = s + (-s) = 0$ and $|B| = |A| + 1$.
3. **Rotate and shift the cycle.** Take a valid zero-sum cycle for $B$, rotate it so $b$ is the first step, and then replace that first step $b$ by $a$. Because every nonempty partial sum includes the first step, replacing $b$ by $a = b + s$ adds the same constant $s$ to every nonempty partial sum, keeping all of them pairwise distinct.
4. **Discard a leading zero if needed.** If $a \in A$, the steps are now precisely the elements of $A$. If $a = 0$, the first partial sum is $0$; dropping that leading zero step simply removes $0$ from the list of partial sums and leaves a valid ordering of $A$.

> **Quick sanity check (mod 5).** Take $A = \{1, 2\}$, which has sum $s = 3$ and $X = \{0, 1, 2\}$. Stepping by $-s \equiv +2 \pmod 5$ gives $2 \to 4 \notin X$, so $a = 2$ and $b = 4$. The zero-sum set $B = \{1, 4\}$ has cycle $(4, 1)$ with partial sums $4, 0$. Replacing the first step $4$ by $2$ yields $(2, 1)$, whose partial sums $2, 3$ are shifted by $+3 \pmod 5$ and stay distinct.

Since $|B|$ is either $|A|$ or $|A| + 1$, the reduction also stays inside any upward-closed family of sizes $k, k+1, \ldots, p-1$. ([Earlier related replacement argument](https://github.com/Atomicium-org/graham-rearrangement-certificates/blob/23cb1d03e718d0798ff79161bff516444e7ca335/paper/graham_rearrangement_candidate.tex#L3513-L3575))

## The finite check at 41

**Exploiting scaling via the reciprocal sum.** Multiplying every element of $A$ by a nonzero scalar $c \in \mathbb{F}_{41}^\times$ multiplies every partial sum by $c$, preserving both the zero-sum property and distinctness of partial sums. To pick a single canonical representative from each scaling orbit, consider the **reciprocal sum**
$$t = \sum_{a \in A} a^{-1} \pmod{41}.$$
Scaling $A$ by $c$ scales its reciprocal sum by $c^{-1}$. Therefore, whenever $t \ne 0$, the scaled set $tA$ has reciprocal sum $t^{-1} t = 1$ (while if $t = 0$, every scaled copy also has reciprocal sum $0$). It therefore suffices to check only zero-sum sets whose reciprocal sum is **0 or 1** — shrinking the search by roughly a factor of $40$.

**Meet-in-the-middle verification.** The verifier ([verify_reciprocal.cpp](verify_reciprocal.cpp)) partitions $\mathbb{F}_{41}^\times$ into two equal halves, $\{1, \ldots, 20\}$ and $\{21, \ldots, 40\}$. It enumerates all $2^{20}$ subsets of each half and joins pairs of halves whose ordinary sums cancel to $0$ and whose reciprocal sums total $0$ or $1$. Because the two halves are disjoint and cover $\mathbb{F}_{41}^\times$, every qualifying set has a unique split.

For each qualifying set, the program searches for a valid ordering and then independently replays its running sums to confirm they are all distinct. All **1,308,242,158** sets passed, including the empty and full sets. Combined with the zero-sum reduction above, this completes the proof for $p = 41$.

### Reproduction and trust boundary

The finite check is an exhaustive C++20 computation paired with the mathematical reductions above. Run from this directory with a C++20 compiler (OpenMP is optional):

~~~sh
c++ -std=c++20 -O3 -march=native -fopenmp verify_reciprocal.cpp -o /tmp/graham41
/tmp/graham41
~~~

An independent full verification uses multiplicative rotations together with an exact per-size count audit, and the earlier size-27 computations also remain reproducible.

* [Modulo-47 proof and reproduction commands](modulo-47.md)
* [Modulo-43 verification](modulo-43.md)
* [Constructive proof for at most 4 omissions](paired-quartet.md) · [Original edge-splitting proof for at most 3 omissions](paired-triple.md)
* [Complete C++ verifier](verify_reciprocal.cpp) · [Rotation verifier](verify_zero_sum.cpp) · [Independent count checker](verify_counts.py) · [Size-27 checks](zero-sum.md)
* [Prior-art notes](../PRIOR_ART.md#erdős-475-all-sizes-modulo-41-and-three-omitted-residues-at-every-prime)
