# Erdős #677 at lengths two and five

Write $M(n,k)$ for the LCM of $n+1,\ldots,n+k$. Two ordered blocks of length $k$ are disjoint when $n+k\le m$. This note covers the full proof for length two and partial results for length five; the general conjecture for arbitrary $k > 0$ is still open. See the [formal statement](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/677.lean) and [problem status](https://www.erdosproblems.com/677).

## Length two

Consecutive integers are coprime, so $M(n,2)=(n+1)(n+2)$. Both factors strictly increase with $n$, so different starts give different LCMs ([BlockLCM/Two.lean](BlockLCM/Two.lean)).

## Length five

Let $D(n)$ be the product of the five entries divided by their LCM. It depends only on $n\bmod 12$, taking the values $2,12,6,8,6,12,2,24,6,4,6,24$ for residues 0 through 11. Because the product strictly increases with $n$, equal LCMs with $n<m$ require $D(n)<D(m)$. That rules out 87 of the 144 ordered residue pairs for arbitrarily large starts ([BlockLCM/Defect.lean](BlockLCM/Defect.lean)).

For each remaining pair, write $a/b=D(n)/D(m)$ in lowest terms, set $X=n+3$ and $Y=m+3$, and let $F(x)=x(x^2-1)(x^2-4)$. Lean proves that equal LCMs are equivalent to $aF(Y)=bF(X)$. A collision with $n<m$ gives one of seven coefficient pairs and a rational point on an explicit sextic ([BlockLCM/Five.lean](BlockLCM/Five.lean)).

For a hypothetical collision, write $(bX-aY)/(Y-X)=R/S$ in lowest terms and set $H=\max(R,S)$. Two estimates give the height bound (following [Danesh and Bianchetti, §6.4](https://ijmttjournal.org/archive/IJMTT-V72I9P101)):

1. Write $X=cU$ and $Y=cV$ with $U,V$ coprime. Expanding $aF(Y)=bF(X)$ gives $c^2\mid 4(bU-aV)$. The right-hand side is positive and at most $4(b-a)U$, so $X^2\le 4(b-a)U^3$ ([BlockLCM/Scale.lean](BlockLCM/Scale.lean)).
2. Cross-multiplying gives $(R+bS)U=(R+aS)V$. Coprimality gives $U\mid R+aS$, so $U\le(1+a)H$ ([BlockLCM/Slope.lean](BlockLCM/Slope.lean)).

For all seven pairs, $4(b-a)(1+a)^3\le352$. Combining the two estimates gives $X^2\le352H^3$. If $H\le3\cdot10^{12}$, then $n\le10^{20}$, where an existing Lean theorem rules out every disjoint collision ([BlockLCM/HeightBound.lean](BlockLCM/HeightBound.lean) and [Height.lean](Height.lean)). The unrestricted length-five case is still open.

Among overlapping blocks with $n<m<n+5$, the only equalities are $(n,m)=(0,1),(4,5),(9,10),(14,15)$. The proof bounds $n$ using $n+1<17(m-n)$ and checks the remaining finite set in Lean ([BlockLCM/Location.lean](BlockLCM/Location.lean)).

## Verification

With Elan installed, run the following in the project directory:

```sh
lake exe cache get
lake build
lake env leanchecker BlockLCM
```
