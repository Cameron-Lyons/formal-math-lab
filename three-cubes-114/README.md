# Searching for three integer cubes summing to 114

For a solution of $x^3+y^3+z^3=114$, the pair sum $M=|x+y|$ must divide $z^3-114$. This project proves a limitation of a method for selecting $M$ and records finite searches. The searches found no integer triple.

## The search lemma

Take a positive integer $n$, set $M=361n^3+6$, and put $r=-19n$. Then $r^3-114=-19M$, so $114$ has a cube root modulo $M$. Every absolute norm from $\mathbb Z[\sqrt[3]{114}]$ is a cube modulo $19$, while $M\equiv6\pmod{19}$. The cubes modulo $19$ are $0,\pm1,\pm7,\pm8$. Thus arbitrarily large moduli admitting a root lie outside this norm family. Lean proves this as `ThreeCubes114.TernaryNorm.unbounded_normalized_moduli`. [Lean proof](TernaryFamily.lean) · [Norm formula](TernaryNorm.lean)

## Reproduce

Run `lake build` in this directory to check the proofs and arithmetic certificates with Lean and mathlib 4.36.0. On a fresh checkout, `lake exe cache get` downloads the mathlib build cache.

To reproduce the search over 2,504,020 selected pair sums, run `uv run TernaryOtherRoots.py --full`. The program enumerates every cube-root class for each selected $M$ in the band $3M\le |z|<51M$. Lean checks that each of the eight discriminants surviving the modular filters lies strictly between consecutive squares. [Search program](TernaryOtherRoots.py) · [Exact certificates](NormCertificates.lean)

For the published searches and the cubic-ideal method, see the [collection's prior-art notes](../PRIOR_ART.md#three-integer-cubes-summing-to-114).
