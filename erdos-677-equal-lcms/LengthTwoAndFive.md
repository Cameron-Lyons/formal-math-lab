# Erdős #677 at lengths two and five

Write $M(n,k)$ for the LCM of $n+1,\ldots,n+k$. Two ordered blocks of length $k$ are disjoint when $n+k\le m$. The project proves the full length-two case and partial results for length five. The conjecture for arbitrary positive $k$ remains open. [Formal statement](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/677.lean) · [Problem status](https://www.erdosproblems.com/677)

## Length two

Consecutive integers are coprime, so $M(n,2)=(n+1)(n+2)$. Both factors strictly increase with $n$, so different starts give different LCMs. [Lean proof](BlockLCM/Two.lean)

## Length five

Let $D(n)$ be the product of the five entries divided by their LCM. It depends only on $n\bmod 12$. As the residue runs from 0 through 11, the values are $2,12,6,8,6,12,2,24,6,4,6,24$. For $n<m$, equality of LCMs requires $D(n)<D(m)$, since the product strictly increases. This excludes 87 of the 144 ordered residue pairs for arbitrarily large starts. [Defect and residue proofs](BlockLCM/Defect.lean)

For the remaining pairs, write $a/b=D(n)/D(m)$ in lowest terms, $X=n+3$, $Y=m+3$, and $F(x)=x(x^2-1)(x^2-4)$. Lean proves that equality of LCMs is equivalent to $aF(Y)=bF(X)$. A collision with $n<m$ gives one of seven coefficient pairs and a rational point on an explicit sextic. [Reduction](BlockLCM/Five.lean)

For a hypothetical collision, write $(bX-aY)/(Y-X)=R/S$ in lowest terms and let $H=\max(R,S)$. Two estimates give the height bound. [Danesh and Bianchetti, §6.4](https://ijmttjournal.org/archive/IJMTT-V72I9P101)

1. Write $X=cU$ and $Y=cV$ with $U,V$ coprime. Expanding $aF(Y)=bF(X)$ gives $c^2\mid 4(bU-aV)$. The quantity on the right is positive and at most $4(b-a)U$, so $X^2\le 4(b-a)U^3$. [Scale estimate](BlockLCM/Scale.lean)
2. Cross-multiplication gives $(R+bS)U=(R+aS)V$. Coprimality gives $U\mid R+aS$, hence $U\le(1+a)H$. [Slope estimate](BlockLCM/Slope.lean)

For every one of the seven pairs, $4(b-a)(1+a)^3\le352$. Combining the estimates gives $X^2\le352H^3$. If $H\le3\cdot10^{12}$, this forces $n\le10^{20}$, where an existing Lean theorem excludes every disjoint collision. The unrestricted length-five case remains open. [Height proof](BlockLCM/HeightBound.lean) · [Earlier-start theorem](Height.lean)

Among overlapping blocks with $n<m<n+5$, the only equalities occur at $(n,m)=(0,1),(4,5),(9,10),(14,15)$. The proof bounds $n$ using $n+1<17(m-n)$ and checks the resulting finite set in Lean. [Classification](BlockLCM/Location.lean)

## Verification

With Elan installed, run the following in the project directory.

```sh
lake exe cache get
lake build
lake env leanchecker BlockLCM
```
