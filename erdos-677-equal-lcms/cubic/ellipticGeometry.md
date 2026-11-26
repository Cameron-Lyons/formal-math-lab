# Elliptic models of the four six-term cubics

Let $F(a)=a(a-1)(a-3)$ and take $(u,v)=(2,1),(5,2),(5,1),(10,1)$ in the equation $vF(b)=uF(a)$. All absolute values below are real and all logarithms are natural. These bounds cover both signs of $a$.

## From the cubic to a rational elliptic point

For $ab\ne0$, put $t=b/a$. Dividing the plane equation by $a$ gives

$$
(vt^3-u)a^2-4(vt^2-u)a+3(vt-u)=0.
$$

Write $z=(vt^3-u)a-2(vt^2-u)$. Completing the square gives

$$
z^2=v^2t^4+3uvt^3-8uvt^2+3uvt+u^2.
$$

Define
$$
 x=\frac{2u(z+u)+3uvt}{t^2},\qquad
 y=\frac{(x^2-4u^2v^2)t-3uvx-6u^3v}{2u}.
$$
Then
$$
 E:\quad y^2=f(x)=x^3-8uvx^2+5u^2v^2x+
               9u^4v^2+9u^2v^4+32u^3v^3.
$$
Lean checks these formulas in [SixElliptic.lean](../SixElliptic.lean). The minimal models use $X=x-s$ and $Y=y$, with $s=5,27,13,27$ in the listed order. Mapping into $E(\mathbb Q)$ is enough to bound every integral plane point, even though the image coordinates can have denominators.

## Uniform real tail for $|a|\ge10^8$

Put $A=|a|$ and $\alpha=(u/v)^{1/3}$. Then $1<t<3$. For $a>0$, $F$ increases above 3 with $F(a)>0$ and $F(3a)>10F(a)$, forcing $a<b<3a$. For $a<0$, $F(b)=(u/v)F(a)<F(a)<-10^6$ forces $b<0$; there $F$ is increasing and $F(3a)/F(a)=3(3A+1)(3A+3)/((A+1)(A+3))>10$ for $A\ge10$, giving $3a<b<a$.

The quadratic relation gives
$$
 |t^3-\alpha^3|\le 4(9+10)/A+3(3+10)/A^2<80/A,
 \qquad |t-\alpha|<27/A.
$$
Substituting $(vt^3-u)a$ from that relation into the formula for $x$ gives
$$
 x=g(t)-\frac{6u(vt-u)}{at^2},\qquad
 g(t)=4uv-2u^2/t^2+3uv/t .
$$
On $1\le t\le3$, we have $|g'|\le430$ and $|6u(vt-u)/(at^2)|\le960/A$, so $|x-x_\infty|<13000/A$, where $x_\infty=g(\alpha)$.
Set $y_\infty=y(x_\infty,\alpha)$ using the displayed formula. Specializing the quartic identity to $t=\alpha$ and $z=2(v\alpha^2-u)$ (using $v\alpha^3=u$) shows that $(x_\infty,y_\infty)$ lies on $E$. Also $x_\infty=4uv-2u\beta+3\beta^2$ with $\beta=v\alpha$. Since $u/v$ is a noncube rational, $\beta$ has degree three, so $x_\infty\notin\mathbb Q$.

Rational interval arithmetic in `ellipticHeight.py` proves $7<x_\infty<36$ and $y_\infty<-9$ in all four cases. Along the segment from $x$ to $x_\infty$, $|x|<41$ and $|f'|<13000$, so $f>81-13000^2/10^8>1$. On the corresponding rectangle, $|\partial y/\partial x|<126$ and $|\partial y/\partial t|<1041$, giving $|y-y_\infty|<2\cdot10^6/A$. The two points therefore lie on the same negative-$y$ branch. Integrating along that branch gives a nonzero elliptic logarithm difference $L$ (up to a real period) with
$$
 0<|L|<13000/A
$$
for either $dx/(2y)$ or $dx/y$. Reversing both orientations preserves this bound.

## Canonical heights and the analytic bound

Write $h(p/q)=\log\max(|p|,|q|)$ for reduced coordinates and $H(P)=\lim_{j\to\infty}4^{-j}h(X(2^jP))$ for the canonical height on the minimal model, with $h(X(O))=0$. On $Y^2=X^3+cX^2+dX+e$, the two homogeneous duplication quartics are
$$
 \begin{aligned}
 D_1(p,q)&=p^4-2dp^2q^2-8epq^3+(d^2-4ce)q^4,\\
 D_2(p,q)&=4p^3q+4cp^2q^2+4dpq^3+4eq^4 .
 \end{aligned}
$$
The script bounds the coefficient sums by $2^{42}<e^{30}$. For the lower bound, it checks integer homogeneous identities $D T^7=B_1D_1+B_2D_2$ for $T=p$ and $T=q$, with a common positive integer $D$ and homogeneous cubics $B_i$ whose combined coefficient sum is at most $2^{142}<e^{100}$. Thus $\gcd(D_1,D_2)\mid D$ whenever $\gcd(p,q)=1$. Applying the identity for the larger of $|p|,|q|$ proves
$$
 -100< h(X(2P))-4h(X(P)) < 30 .
$$
Iterating and summing gives $h(X)-100/3\le H(P)\le h(X)+10$.

For each full basis $G_1,G_2,G_3$ below, the script performs six exact doublings at $G_i$ and $G_i+G_j$ to enclose $H$ within $100/(3\cdot4^6)$ plus logarithm rounding. Polarization gives interval bounds for the canonical height Gram matrix, and interval determinants with Sylvester's criterion place all of its eigenvalues strictly between $3/20$ and 4. In particular, $H(P)>(3/20)M^2$ for every nonzero point $P=\sum n_iG_i$ with $M=\max|n_i|$.

From the formula for $x$,
$$
 X=\frac{(4uv-s)b^2+3uvab-2u^2a^2-6uvb+6u^2a}{b^2}.
$$
For $1<t<3$, the script checks in each case that both the numerator magnitude and the denominator stay below $2048 A^2$. Reducing the fraction can only lower the coordinate height, so $h(X)<2\log A+8$ and $H(P)<2\log A+18$. Combining this with the real-tail bound gives
$$
 \log |L| < 19-\tfrac3{40} M^2 .
$$

## Reproducing the arithmetic

| $u/v$ | Minimal $(a_2,a_4,a_6)$, $a_1=a_3=0$ | Full basis $(X,Y)$ |
|---|---|---|
| 2 | $(-1,-65,261)$ | $(5,-6),(-7,18),(-4,21)$ |
| 5/2 | $(1,-1633,32963)$ | $(23,-90),(-37,210),(-31,234)$ |
| 5 | $(-1,-408,6912)$ | $(-24,48),(12,-60),(-18,90)$ |
| 10 | $(1,-1633,97763)$ | $(-58,27),(23,-270),(-37,330)$ |

Run these commands from `erdos-677-equal-lcms/`:

```sh
lake env lean SixElliptic.lean
gp -fq cubic/ellipticGroups.gp
python -B cubic/ellipticMwrank.py
python cubic/ellipticHeight.py
```

[PARI/GP's elliptic-curve routines](https://pari.math.u-bordeaux.fr/dochtml/html/Elliptic_curves.html) verify minimal models, conductors, trivial rational torsion, ranks, and membership of the generators. The Python wrapper runs `mwrank -p 180 -S -1` from [eclib](https://github.com/JohnCremona/eclib) separately on each model, checks that eclib reports an unconditional full Mordell-Weil basis, and compares the returned basis against the table (set `MWRANK` to the executable path if needed). The height and tail verifier uses only Python's standard library.
