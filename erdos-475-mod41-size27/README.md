# Graham’s rearrangement problem modulo 41 and 43

**At both 41 and 43, every subset of the nonzero residues has an ordering with distinct nonempty partial sums.** In each field it suffices to check zero-sum sets whose reciprocal sum is 0 or 1. [Modulo-43 proof and reproduction commands](modulo-43.md)

**At every prime, the conclusion holds for every set omitting at most four nonzero residues.** One alternating ordering handles any collection of opposite pairs together with three or four unpaired residues of sum zero. [Constructive proof](paired-quartet.md) · [Erdős problem #475](https://www.erdosproblems.com/475)

## Reduction to sets of sum zero

A zero-sum ordering traces a closed path starting at 0. Its nonempty partial sums are distinct exactly when the only repeated vertex is the final return to 0. We can therefore rotate such an ordering to start with any chosen step.

Now let $A$ have nonzero sum $s$ modulo an odd prime $p$. Put $X=A\cup\{0\}$. This is a proper subset of the field because the full set of nonzero residues sums to zero. Repeatedly subtracting $s$ visits the entire field, so some $a\in X$ has $b=a-s\notin X$. Form the zero-sum set

$$B=(A\setminus\{a\})\cup\{b\}.$$

Rotate a cycle for $B$ to put $b$ first, then change that step to $a$. Every nonempty partial sum increases by the same $s$, so they stay distinct. If $a=0$, discard the leading zero. This gives the desired ordering of $A$. Since $|B|$ is either $|A|$ or $|A|+1$, the reduction also works within any family of sizes $k,k+1,\ldots,p-1$. [Earlier related replacement argument](https://github.com/Atomicium-org/graham-rearrangement-certificates/blob/23cb1d03e718d0798ff79161bff516444e7ca335/paper/graham_rearrangement_candidate.tex#L3513-L3575)

## The finite check at 41

For a zero-sum set $A$, let $t=\sum_{a\in A}a^{-1}$ modulo 41. If $t\ne0$, the scaled set $tA$ has reciprocal sum $1$. Scaling preserves distinct partial sums. It therefore suffices to check the zero-sum sets whose reciprocal sum is **0 or 1**.

The verifier lists all subsets of $\{1,\ldots,20\}$ and of $\{21,\ldots,40\}$, then joins halves whose two sums meet those conditions. Each qualifying set has exactly one such split. For each set it finds an ordering and independently recomputes the running sums. All **1,308,242,158** sets passed, including the empty and full sets. The reduction above finishes the proof. [Complete C++ verifier](verify_reciprocal.cpp)

Run from this directory with a C++20 compiler. OpenMP is optional.

~~~sh
c++ -std=c++20 -O3 -march=native -fopenmp verify_reciprocal.cpp -o /tmp/graham41
/tmp/graham41
~~~

The original full check uses rotations and an independent count at each size. The earlier size-27 computations also remain reproducible. [Rotation verifier](verify_zero_sum.cpp) · [Independent count checker](verify_counts.py) · [Size-27 checks](zero-sum.md) · [Prior-art notes](../PRIOR_ART.md#erdős-475-all-sizes-modulo-41-and-three-omitted-residues-at-every-prime)
