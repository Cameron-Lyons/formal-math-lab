# The two marked points force integrality at 7

Let three rational functions on the Pell conic $u^2-3v^2=1$ be represented by polynomials in $u,v$ of total degrees at most $(4,3,6)$. Suppose they satisfy $z^2+y^2z+x^3=2$ identically, take the value $(0,1,1)$ at $(1,0)$, and take either $(1,0,-1)$ or $(-2,3,1)$ at $(2,1)$. **All coefficients in the chart below are integral at 7.** The argument includes arbitrary powers of 7 in potential denominators.

Put $w=u-1-v$. The two marked points have $w=0$ and $v=0,1$, respectively. The conic relation becomes
$$v^2=(1+w)v+w+w^2/2.$$
Successive reduction by this monic relation gives each coordinate of degree bound $d$ a unique expression $P(w)+vQ(w)$ with $\deg P\le d$ and $\deg Q<d$. Both $P(0)$ and $Q(0)$ are integers because the marked values specify $P(0)$ and $P(0)+Q(0)$.

Suppose that some coefficient has negative 7-adic valuation. Take the maximum $h$ of $-v_7(a_i)/i$ over all nonzero coefficients of positive degree in the six polynomials. It is positive. Set $w=\delta s$ with $v_7(\delta)=h$. A totally ramified extension with residue field $\mathbb F_7$ supplies this scalar, including when $h$ is fractional. All rescaled coefficients are integral and some positive-degree coefficient is a unit. After reduction the relation is $v^2=v$. The two evaluations $v=0,1$ therefore give ordinary polynomial solutions $A=P$ and $B=P+Q$ with their respective marked values. At least one is nonconstant. The coefficients of $s^4,s^3,s^6$ in the respective coordinates agree between $A$ and $B$ because each $Q$ has smaller degree.

The finite census tries each of the $7^4$ choices of the positive-degree coefficients of $x$. For constant $x$ the product $z(z+y^2)=2-x^3$ is a nonzero constant at each of the three points, so the other coordinates are constant as well. For nonconstant $x$ the census factors $2-x^3$, enumerates every monic divisor and complementary divisor of degrees at most six, fixes the scalar by $z(0)$ and tests whether the difference of factors is a square of degree at most six. Both signs of the square root are tested. Constant solutions are also included when matching the leading coefficients. [Finite census and rank checks](two_point_alternate.py)

| Second marked value | Nonconstant triples at the second mark | Compatible nonconstant pairs | Jacobian rank | Augmented rank |
|---|---:|---:|---:|---:|
| $(1,0,-1)$ | 18 | 6 | 19 | 20 |
| $(-2,3,1)$ | 42 | 6 | 18 | 19 |

There are six nonconstant triples at the first mark. In each row of the table, all compatible pairs form one orbit under $s\mapsto as$ for $a\in\mathbb F_7^\times$. In each pair, $P_x$ and $P_y$ retain degrees four and three. Their leading coefficients before scaling are rational numbers of valuations $-4h$ and $-3h$, so both $4h$ and $3h$ belong to $\mathbb Z$. Hence $h$ is an integer. We can use a rational $\delta$ of valuation $h$, and its unit factor can realize the displayed orbit representative, whose top coefficients are $(3,3,2)$.

Write $w=2Hs$. Now $H$ is divisible by 7 in $\mathbb Z_7$ and the exact relation is
$$v^2=(1+2Hs)v+2Hs+2H^2s^2.$$
There are 23 free positive-degree coefficients, plus $H$. The identity has 23 nonconstant coefficient equations, 12 in the constant component and 11 in the $v$ component. In each of the two orbit representatives there is a linear combination of these equations whose constant term at the chosen lift is nonzero modulo 49 and whose 24 first corrections all vanish modulo 49. Terms of order at least two in the corrections are divisible by 49. Thus neither representative lifts, contradicting the assumed negative valuation. [Lean certificate for the two obstructions](two_point_alternate.lean)

In the chart $L=1-3t^2$, $u=(1+3t^2)/L$, $v=2t/L$, substitution now gives 7-integral numerator coefficients. Consequently the complete two-point numerator census at 7 covers every rational substitution under these hypotheses.

## The alternate endpoint at 2

For 2-integral coefficients in the original Pell ring, use the unique form
$$f=A+(B-A)v+v(v-1)R(v)+wQ(v),\qquad w=u-1-v,$$
where $A,B$ are its marked values and the degree bounds are $\deg R\le d-2$, $\deg Q<d$. Reduction uses $w^2=2(v^2-v)-2(1+v)w$ and preserves 2-integrality. Conversely, $P(v)-A-(B-A)v$ is divisible by the monic polynomial $v(v-1)$ in the coefficient ring for any $P$ realizing the marked values.

For $(A_x,A_y,A_z)=(0,1,1)$ and $(B_x,B_y,B_z)=(-2,3,1)$ the surface identity holds in this ring modulo 2048 for one explicit assignment. It fails modulo 4096 for every assignment of the 23 free coefficients. Thus 4096 is the first obstructing power of two. The Lean statement uses polynomial convolution in the displayed ring, checks the witness by computation and proves the universal obstruction using bit-vector arithmetic. [Lean theorem and explicit witness](two_point_alternate_two.lean)

The balancing argument at 2 puts every rational candidate for this alternate pair of marks in the original 2-integral lattice. Together these results exclude that quartic ansatz with arbitrary rational coefficients. [Proof covering possible denominators](TwoPointAlternateTwo.md)
