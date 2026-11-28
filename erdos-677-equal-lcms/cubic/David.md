# Initial bound for the three Mordell–Weil coefficients

From the elliptic geometry of our four length-6 cubics ([ellipticGeometry.md](ellipticGeometry.md)), any large integral point maps to a rational point $P = n_1 G_1 + n_2 G_2 + n_3 G_3$ whose elliptic logarithm lies extraordinarily close to that of a fixed nonrational algebraic point $Q_\infty$. Specifically, for each of the four ratios $u/v \in \{2, 5/2, 5, 10\}$, write the real logarithm difference as
$$
L = m_0 \omega + n_1 U_1 + n_2 U_2 + n_3 U_3 - U_\infty,
\qquad M = \max_i |n_i|,
$$
where $U_1, U_2, U_3$ are the elliptic logarithms of the three Mordell–Weil generators, $U_\infty$ is the logarithm of the target point on the real branch at infinity, and $\omega > 0$ is the real period (all four point logarithms chosen in $[0, \omega)$ with respect to the invariant differential $dX/Y$).

**The big idea.** From the geometry of the curve and canonical heights, we have an **upper** bound showing that $|L|$ shrinks quadratically in the exponent:
$$|m_0| \le 3M + 2 \qquad\text{and}\qquad \log |L| \le 25 - 0.075 M^2.$$
On the other hand, **David’s theorem on linear forms in elliptic logarithms** (the elliptic analogue of Baker’s theorem) provides an explicit **lower** bound on $\log |L|$ that decays only like $-(\text{constant}) \cdot (\log M)(\log \log M)^6$. Because $M^2$ overwhelms $(\log M)(\log\log M)^6$ for large $M$, comparing the two bounds forces an explicit cap: **$M < 10^{400}$**! (Once $M$ is finite, LLL lattice reduction in [LengthSix.md](LengthSix.md) shrinks $10^{400}$ down to $250$ in one step.) The numerical checks for the point heights and periods used below live in [logarithms.py](logarithms.py).

## David’s parameters

Theorem 2.1 of [S. David, *Minorations de formes linéaires de logarithmes elliptiques*, Mémoires de la SMF 62 (1995), pp. 9-10](https://doi.org/10.24033/msmf.376) lower-bounds a nonzero linear form in $(1, U_1, \ldots, U_k)$, where each elliptic logarithm may also be a period (a pole of the Weierstrass $\wp$-function representing the identity). In our linear form $L$, the constant additive term has coefficient $0$, while the period $\omega$, the three generator logarithms $U_1, U_2, U_3$, and the target logarithm $U_\infty$ give $k = 5$ terms.

Write $A_i = \log V_i$ for David’s height parameters and set his auxiliary parameter to $E = e$. Using natural logarithms throughout, whenever $L \ne 0$ and the size conditions hold, David’s Theorem 2.1 gives
$$
\log |L| >
-C_k D^{2k+2}(\log B + \log(De))
 (\log\log B + h + \log(De))^{k+1} \prod_{i=1}^{k} A_i,
$$
where
$$C_k = 2.9 \cdot 10^{6 + 6k}\, 4^{2k^2}\, (k + 1)^{2k^2 + 9k + 12.3}.$$

We now verify nonvanishing ($L \ne 0$) and all four size conditions of David’s theorem:

1. **Number-field degree $D = 3$ and nonvanishing ($L \ne 0$).** Set $D = 3$. Put $\beta^3 = uv^2$, so $uv^2 \in \{2, 20, 5, 10\}$ — each is a positive noncube integer, giving a cubic field $K = \mathbb{Q}(\beta)$ of degree $3$. The target point’s coordinates lie in $K$, with short-model abscissa $X_\infty = c - 2u\beta + 3\beta^2$ for a rational number $c$. Because $1, \beta, \beta^2$ are linearly independent over $\mathbb{Q}$, $X_\infty \notin \mathbb{Q}$. If $L = 0$, the complex uniformization would identify this nonrational target point with an integer linear combination of the rational generators — which is rational, a contradiction. (Any sign flip on our logarithms merely negates the corresponding points and reaches the same contradiction.)
2. **Weierstrass normalization and curve height $h = 100$.** On the short Weierstrass model $Y^2 = X^3 + AX + B_0$, rescale via $(x', y') = (X/4, Y/4)$ to obtain David’s standard form
   $$(y')^2 = 4(x')^3 - g_2 x' - g_3, \qquad g_2 = -A/4, \quad g_3 = -B_0/16,$$
   which preserves the invariant differential $dx'/y' = dX/Y$. For each of the four curves, clearing denominators in $[1 : g_2 : g_3 : j]$ produces integers of absolute value strictly below $2^{100}$. This bounds both of David’s heights $h([1 : g_2 : g_3])$ and $h(j)$ by $100$. Replacing his curve-height parameter by the upper bound $h = 100$ only increases the magnitude of the right-hand side.
3. **Algebraic height bound for $A_i = 1000$.** Set all five parameters $A_i = 1000$.
   * Each of the three rational generator abscissae has absolute logarithmic Weil height $h(X) < 100$.
   * For the target abscissa, since $3c$ is an integer,
     $$h(c - 2u\beta + 3\beta^2) \le 2h(\beta) + \log\max(3, |3c| + 6u + 9),$$
     which is also strictly below $100$ in all four cases.
   * After clearing a common denominator, the two homogeneous quartics in the duplication formula have coefficient sums in absolute value below $2^{100}$, so $h(X(2P)) \le 4h(X(P)) + 100$ over every number field. Iterating gives $\lim_{s \to \infty} 4^{-s} h(X(2^s P)) \le h(X(P)) + 100/3$.
   * The curve equation gives $h(Y) \le \tfrac{3}{2} h(X) + O(1)$ and $h([1 : X : Y]) \le h(X) + h(Y)$, while scaling from $(X, Y)$ to $(x', y')$ adds only a bounded term. David’s projective canonical height is therefore at most $\tfrac{5}{2}(100 + 100/3) = 1000/3$. Torsion points, including the identity represented by the period $\omega$, have canonical height $0$.
4. **Period-lattice area and archimedean bound.** Let $i\omega_*$ be a primitive imaginary period of the curve. Writing $f(X) = X^3 + AX + B_0$, the reflected cubic $y^2 = -f(-x)$ is isomorphic to $E$ over $\mathbb{C}$ via $(X, Y) \mapsto (-X, iY)$, which rotates $dX/Y$ by $i$; hence the positive real period of the reflected cubic is precisely $\omega_*$.

   In the real-symmetric period lattice $\Lambda$, the rectangular sublattice generated by $\omega$ and $i\omega_*$ has index at most $2$: for any $z \in \Lambda$, both $z + \bar{z}$ and $z - \bar{z}$ lie on the coordinate axes, and primitivity on each axis leaves the simultaneous half-period $(\omega + i\omega_*)/2$ as the only possible extra coset. Consequently, for any reduced basis $(\omega_1, \omega_2)$ of $\Lambda$, the fundamental area satisfies
   $$|\omega_1|^2 \operatorname{Im}(\omega_2 / \omega_1) \ge \frac{\omega \omega_*}{2}.$$
   The certified period enclosures in [logarithms.py](logarithms.py) prove $\omega / \omega_* < 100$. Because each chosen logarithm has modulus $|U| \le \omega$, David’s archimedean quantity satisfies
   $$\frac{3\pi |U|^2}{D \operatorname{area}\Lambda} \le \frac{\pi \omega^2}{\omega\omega_* / 2} = 2\pi \frac{\omega}{\omega_*} < 200\pi < 1000.$$
   This completes condition (3) (with $A_i = 1000$) and ensures that $E = e$ satisfies both bounds in condition (4).
5. **Coefficient bound $B = 6M$.** It suffices to rule out $M \ge 10^{400}$. Set $B = 6M$. Every linear coefficient in $L$ has absolute value at most $B$ (since $|m_0| \le 3M + 2 \le 6M$, $|n_i| \le M$, and $|-1| = 1$) and logarithmic height at most $\log B$. For $M \ge 10^{400}$ we also have $D \log B > 1000$ and $\log B > 100e$, proving conditions (1) and (2).

## Comparing the bounds

With $k = 5$, $D = 3$, and $A_i = 1000$, the constant prefactor in David’s bound satisfies the elementary estimate
$$
C_5 \cdot 3^{12} \cdot 1000^5
< 3 \cdot 10^{36} \cdot 4^{50} \cdot 6^{108} \cdot 3^{12} \cdot 1000^5
< 10^{172}.
$$

Set $t = \log(6M) = \log B$. Using $\log(De) = \log(3e) < 3$, combining our geometric upper bound $\log |L| \le 25 - 0.075 M^2$ with David’s lower bound would force
$$
0.075 M^2 - 25 < 10^{172}(t + 3)(\log t + 103)^6.
$$

* **At the threshold $M = 10^{400}$:** Here $900 < t < 1000$. The left-hand side exceeds $10^{798}$, whereas the right-hand side is below $10^{190}$ (since $t + 3 < 10^4$ and $\log t + 103 < 200$).
* **For all $M \ge 10^{400}$:** Because $M = e^t/6$, as $t$ increases the logarithmic derivative of the left-hand side with respect to $t$ exceeds $2$, while the logarithmic derivative of the right-hand side is
  $$\frac{1}{t + 3} + \frac{6}{t(\log t + 103)} < 1.$$
  Thus the left-hand side grows strictly faster than the right-hand side for all $M \ge 10^{400}$, so the inequality fails everywhere in this range.

Therefore every solution satisfies $M < 10^{400}$. $\square$
