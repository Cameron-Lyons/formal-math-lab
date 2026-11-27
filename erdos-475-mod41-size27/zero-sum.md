# An independent check using zero-sum sets

A zero-sum ordering with distinct nonempty running sums traces a simple cycle. At size 27 modulo 41, it suffices to check that every zero-sum set has such a cycle.

Indeed, let $A$ have nonzero total $s$. Choose $a\in A$ such that $b=a-s$ lies outside $A\cup\{0\}$. Such an $a$ exists. Otherwise every $js\in A$ with $2\le j\le40$ would force $(j-1)s\in A$, giving $A=\{s,2s,\ldots,27s\}$. Its sum would be $378s=9s\ne s$ modulo 41.

Replace $a$ by $b$ to get a zero-sum set. Rotate its cycle to put $b$ first, then put $a$ back in its place. This adds $s$ to every nonempty running sum, preserving distinctness. [Related reduction in the Atomicium draft](https://github.com/Atomicium-org/graham-rearrangement-certificates/blob/23cb1d03e718d0798ff79161bff516444e7ca335/paper/graham_rearrangement_candidate.tex#L3513-L3575)

The verifier writes sets in the order $1,6,6^2,\ldots,6^{39}$, so rotation multiplies all residues by the same factor. Give each omitted residue weight $27$ and each included residue weight $-13$. The total weight is zero. Starting at a minimum cumulative weight gives a rotation in which all cumulative weights are nonnegative. The verifier lists all such words by joining two 20-position halves. It requires 13 omissions with sum zero, which is equivalent to the 27 included residues summing to zero. It found and checked a cycle in every one of the **7,337,331** cases. [Verifier](verify_zero_sum.cpp)

Run from this directory. The verification took 3.1 seconds on one Intel Core Ultra 5 325 CPU thread with GCC 16.2.1.

~~~sh
c++ -std=c++20 -O3 -march=native verify_zero_sum.cpp -o /tmp/erdos475-zero
/tmp/erdos475-zero
~~~
