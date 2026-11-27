# Graham's rearrangement problem for 27 residues modulo 41

**Every 27-element set of nonzero residues modulo 41 can be ordered so that its 27 nonempty running sums are distinct.**

**Computer-assisted proof.** Multiplying every element by the same nonzero residue multiplies every running sum by that residue, preserving distinctness. If a set has nonzero total $s$, multiply it by $s^{-1}$ to make its total 1. Thus it suffices to check sets of total 0 or 1.

The verifier checked **all 586,986,481 such sets**. For each it found an ordering and recomputed the 27 running sums. All were distinct, and the first 26 were nonzero. Scaling back gives the claimed ordering for the original set. [Verifier](verify.cpp)

To see why the list is exhaustive, describe a set by the 13 residues it omits. The verifier chooses the first 12 omissions in increasing order. If the remaining 28 residues sum to $r$, the last omission must be $r$ for a set of total 0, or $r-1$ for a set of total 1, modulo 41. It checks each candidate larger than the twelfth omission.

## Reproduce

Run from this directory with a C++20 compiler. OpenMP is optional.

~~~sh
c++ -std=c++20 -O3 -march=native -fopenmp verify.cpp -o /tmp/erdos475
/tmp/erdos475
~~~

The output is `586986481 sets verified`.

[Independent three-second proof using zero-sum sets](zero-sum.md) · [Erdős problem #475](https://www.erdosproblems.com/475) · [Arévalo's verification for sizes 28–40](https://fabianarevalo.com/graham-rearrangement) · [Prior-art notes](../PRIOR_ART.md#erdős-475-size-27-modulo-41)
