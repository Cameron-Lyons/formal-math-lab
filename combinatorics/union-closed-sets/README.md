# Frankl's union-closed sets conjecture: certified lower bound `1533 / 4000 = 0.38325`

A finite collection $\mathcal{F}$ of finite sets is called a **union-closed family** if taking the union of any two sets in the collection keeps you inside it: $A \cup B \in \mathcal{F}$ for all $A, B \in \mathcal{F}$. (For instance, $\{\emptyset, \{1\}, \{2\}, \{1, 2\}\}$ is union-closed, and both $1$ and $2$ belong to $2$ of its $4$ sets — exactly half.) Peter Frankl's 1979 conjecture asks whether *every* finite union-closed family containing at least one nonempty set has some element belonging to at least half ($50\%$) of its members. The full conjecture remains open.

The Lean 4 proof here establishes the unconditional lower bound

$$
\frac{1533}{4000} = 0.38325 > c_* + 3.647 \times 10^{-4},
$$

where $c_* \approx 0.38288525996679$ is the Costa-Sadhu single-coordinate entropy threshold (the ceiling that purely single-coordinate entropy arguments cannot pass). Every analytical, univariate, bivariate, covariance, and polytope inequality in the proof is verified inside Lean's kernel using 50-bit scaled-integer interval arithmetic, with zero `sorry`, zero custom axioms, and zero `native_decide`.

| Field | Summary |
| --- | --- |
| Problem | Frankl's union-closed sets conjecture (1979): largest constant $c$ such that every finite union-closed family with a nonempty set has an element in at least $c \lvert\mathcal{F}\rvert$ sets |
| Status | Partial result (lower bound $c \ge 1533 / 4000 = 0.38325$). The conjectured constant $1/2$ remains open. |
| Main theorem | `UCBound.frankl_union_closed_bound` in [UCBound/Main.lean](UCBound/Main.lean) (re-exported by [UCBound.lean](UCBound.lean)) |
| Axioms | `[propext, Classical.choice, Quot.sound]` only (pure kernel `decide`, zero `native_decide`) |
| Verification | `lake exe cache get && lake --wfail build && LEAN_NUM_THREADS=1 lake env leanchecker --fresh UCBound` (Lean 4.36.0 + mathlib v4.36.0) |
| Prior art | Checked 25 November 2026: improves on Gilmer (2022, $0.01$), $(3 - \sqrt{5})/2 \approx 0.38197$, Liu ($0.382709$), Costa and Sadhu (`arXiv:2610.02295`, $0.3828852549667978$), the unrefereed Sadhu-Ursin preprint ($c_* + 9.2 \times 10^{-5}$), and Quantavane's November 2026 announcement ($c_* + 2.9 \times 10^{-4} \approx 0.383175$). No earlier proof of $0.38325$ or Lean formalization of a bound past $c_*$ was located in the sources checked. |

## What Lean proves

Import `UCBound` to access the main theorem ([UCBound/Main.lean](UCBound/Main.lean)):

```lean
theorem UCBound.frankl_union_closed_bound
    {α : Type*} [DecidableEq α]
    (F : Finset (Finset α))
    (hUC : UnionClosed F)
    (hNE : ∃ A ∈ F, A.Nonempty) :
    ∃ a : α, (1533 : ℝ) / 4000 * (F.card : ℝ) ≤ ((F.filter (fun A => a ∈ A)).card : ℝ)
```

| Module | Role in the proof |
| --- | --- |
| [UCBound/Basic.lean](UCBound/Basic.lean) | Binary entropy $h$, perturbation parameter $\tau$, functions $\phi, R, v, b, F, J$, and elementary calculus bounds |
| [UCBound/Entropy.lean](UCBound/Entropy.lean) | Discrete Shannon entropy, chain rule, subadditivity, and reduction from `UnionClosed` to `AndClosed` boolean cubes |
| [UCBound/Protocols.lean](UCBound/Protocols.lean) | Independent two-copy protocol, finite CIID fair-sign protocol, global gap budget, and fibre inequality |
| [UCBound/SubsetAvg.lean](UCBound/SubsetAvg.lean) | Peeling into high- and low-entropy coordinates $(G, T)$, beta-weighted subset averaging, and the 3-vertex single-order `master_contradiction` |
| [UCBound/Interval.lean](UCBound/Interval.lean), [UCBound/IntervalOps.lean](UCBound/IntervalOps.lean), [UCBound/FastLog.lean](UCBound/FastLog.lean) | Pure-kernel 50-bit scaled-integer interval arithmetic and table-accelerated `fastLog` with soundness proofs |
| [UCBound/CertConst.lean](UCBound/CertConst.lean), [UCBound/AnalyticBounds.lean](UCBound/AnalyticBounds.lean) | Certified 50-bit enclosures of all proof constants (`rStar`, `mStar`, `cStar`, `qStar`, `tau`, `pStar`, `cParam`, `kappaParam`, `DParam`) and derivative evaluators |
| [UCBound/Cert1D.lean](UCBound/Cert1D.lean), [UCBound/Cert1DTrees.lean](UCBound/Cert1DTrees.lean) | Kernel-certified proofs of all 7 univariate local inequalities (`R_nonneg`, `R_le_phi`, `Signed`, `b_mem`, `Line1`, `SqrtLB`, `Bopp2D`) |
| [UCBound/CertCov.lean](UCBound/CertCov.lean), [UCBound/CertCovChk.lean](UCBound/CertCovChk.lean) | Kernel-certified covariance inequality (`hCov`) |
| [UCBound/CertF.lean](UCBound/CertF.lean), [UCBound/CertStrips.lean](UCBound/CertStrips.lean) | Unified kernel-certified proofs of the 3 symmetric bivariate lower bounds on $F(x, y)$ (`hF_R`, `hF_v`, `hF_sim`) with boundary strips and Hessian contact squares |
| [UCBound/CertPolytope.lean](UCBound/CertPolytope.lean), [UCBound/CertPolytopeTrees.lean](UCBound/CertPolytopeTrees.lean) | Witness-carrying 2D polytope trees proving $\Phi_G > 0$ at all 3 vertices and $\Phi_T > 0$ on $(0, z]$ using only Option A (exact $U$) and Option B (Boppana $U$), plus the analytic small-$e$ proof |
| [UCBound/Main.lean](UCBound/Main.lean) | Assembles `localInequalities_proof` and proves `UCBound.frankl_union_closed_bound` |

## How the proof works

**The big idea (entropy contradiction past $c_*$):** Modern progress on Frankl's conjecture stems from Justin Gilmer's 2022 information-theoretic breakthrough. If you sample two independent random sets from a union-closed family, their union also lands inside the family — so the Shannon entropy of the union cannot exceed the entropy of a single uniform draw. Yet if every element appeared too rarely, taking unions would *increase* entropy, forcing a contradiction. Pushing past the single-coordinate barrier $c_* \approx 0.382885$ requires coupling coordinates together across multiple protocols and splitting coordinates into high-entropy and low-entropy regimes.

The formal proof executes this strategy in three stages:

1. **Reduction to AND-closed boolean cubes:** Taking set complements turns unions into intersections, converting a finite union-closed family with a nonempty set into an AND-closed subset $\Omega \subseteq \{0, 1\}^n$ with $\lvert\Omega\rvert \ge 2$ (closed under bitwise AND). Assuming for contradiction that every element appears in fewer than $1533/4000$ of the sets translates to coordinate marginals satisfying $s_i \ge m_* - \varepsilon$ (`epsParam = 365 / 1000000`).
2. **Single-order shared-budget accounting:** Coordinates are peeled into a high-entropy core $G$ ($e_i \ge z = 21/50$) and a low-entropy tail $T$ ($e_i < z$). Averaging three information-theoretic bounds — the fibre inequality, the two-copy independent protocol, and the CIID (conditionally independent and identically distributed) fair-sign protocol — over all permutations of $G$ against a beta-weighted subset density produces a **nonpositive** weighted sum of single-coordinate objectives: $\Phi_G$ (evaluated at the three vertices $(w, \omega) \in \{(0, 3/8), (1, 3/8), (1, -5/8)\}$) and $\Phi_T$.
3. **Kernel-certified local and polytope bounds:** Seven 1D inequalities, the covariance inequality `hCov`, and three bivariate $F$-bounds (`hF_R`, `hF_v`, `hF_sim`) define the feasible relaxation `ValidPoint`. Witness-carrying 50-bit scaled-integer branch-and-bound trees certify $\Phi_G > 0$ on $[z, \ln 2] \times [0, 1]$ and $\Phi_T > 0$ on $[1/10, z] \times [0, 1]$ using only exact $U$ and Boppana $U$ bounds; an analytic convex combination $(17/20)\,\mathrm{OptA} + (3/20)\,\mathrm{OptB}$ certifies $\Phi_T > 0$ for $0 < e \le 1/10$. Because every term in the nonpositive sum is strictly positive, we reach a contradiction.

## Reproduce

Run from this directory with the pinned Lean 4.36.0 toolchain. On machines with limited RAM (16 GiB or less), build the seven 2D check modules sequentially before running the final build so multiple kernel reductions do not run simultaneously:

```sh
lake exe cache get
lake --wfail build UCBound.CertCovChk
lake --wfail build UCBound.CertFRChk1
lake --wfail build UCBound.CertFRChk2
lake --wfail build UCBound.CertFvChk1
lake --wfail build UCBound.CertFvChk2
lake --wfail build UCBound.CertFsimChk1
lake --wfail build UCBound.CertFsimChk2
lake --wfail build
LEAN_NUM_THREADS=1 lake env leanchecker --fresh UCBound
```

Verify the axiom footprint directly:

```sh
lake env lean --stdin <<'EOF'
import UCBound
#print axioms UCBound.frankl_union_closed_bound
EOF
```

Expected output:

```text
'UCBound.frankl_union_closed_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## References and attribution

* Peter Frankl (1979): union-closed sets conjecture.
* Justin Gilmer (2022), *A constant lower bound for the union-closed sets conjecture* (`arXiv:2211.09055`).
* Jingbo Liu (2024), *Improving the lower bound for the union-closed sets conjecture via conditionally iid coupling* (`arXiv:2405.00807`, $0.382709$).
* Yunjiang Jiang (2026), *Entropy bounds and global couplings for union-closed families* (`arXiv:2609.08291`).
* Simone Costa and Ankan Sadhu (2026), *Beyond Liu's $0.382709$ threshold for the union-closed sets conjecture* (`arXiv:2610.02295`, $0.3828852549667978$ and the single-coordinate limit $c_*$).
* Ankan Sadhu and Touko Ursin (2026), *An improved lower bound for union-closed families* (preprint, $c_* + 9.2 \times 10^{-5}$): fibre inequality, peeling, and subset-averaging framework.
* Quantavane (November 2026), [Union-closed sets conjecture announcement](https://quantavane.com/results/union-closed-sets/) ($c_* + 2.9 \times 10^{-4} \approx 0.383175$): single-order shared-budget accounting and Cauchy-Schwarz low-entropy fibre bound.
