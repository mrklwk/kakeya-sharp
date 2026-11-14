# Sharp logarithmic Kakeya estimates

Two Lean theorems give upper bounds for tube overlap and the Kakeya maximal operator in every dimension $n\ge2$.
Written arguments establish the optimality of their logarithmic powers.
Their written consequence is a sharp lower bound for the volume occupied by tubes in separated directions.
For $0<\delta\le1$, put $L:=\log(2/\delta)$; every implicit constant depends only on $n$.

| Quantity | Dependence on $L$ |
| --- | --- |
| Critical maximal operator norm $L^n(\mathbb R^n)\to L^n(S^{n-1})$ | $L^{(n-1)/n}$ |
| Critical tube overlap integral | $L$ |
| Smallest union or Kakeya-neighbourhood volume, full set of directions | $L^{-(n-1)}$ |

## Definitions

Let $dx$ be Lebesgue measure on $\mathbb R^n$ and $d\sigma$ the unnormalized surface measure on $S^{n-1}$, so that $\sigma(S^{n-1})=n\kappa_n$ where $\kappa_j$ is the volume of the unit ball of $\mathbb R^j$.
For $0<\delta\le1$, a unit vector $\omega$, and a center $x\in\mathbb R^n$ let

$$
 T_\delta(\omega,x):=\bigcup_{-1/2\le t\le1/2}B(x+t\omega,\delta).
$$

This is the open $\delta$-neighbourhood of a unit segment, with rounded end caps, and $|T_\delta(\omega,x)|=\kappa_{n-1}\delta^{n-1}+\kappa_n\delta^n\asymp_n\delta^{n-1}$.
The Kakeya maximal operator is

$$
 K_\delta f(\omega):=\sup_{x\in\mathbb R^n}\frac1{|T_\delta(\omega,x)|}\int_{T_\delta(\omega,x)}|f(y)|\,dy .
$$

The supremum is over every center, and $f$ may be any complex-valued function in $L^n(\mathbb R^n)$.
A Kakeya set is a subset of $\mathbb R^n$ containing a unit segment in every direction; $N_\delta(K)$ denotes the open $\delta$-neighbourhood of $K$.

## The formalized estimates

**Theorem 1 (maximal estimate).**
For every integer $n\ge2$ there is $C_n>0$ such that for every $0<\delta\le1$ and every $f\in L^n(\mathbb R^n)$ the function $K_\delta f$ belongs to $L^n(S^{n-1},d\sigma)$ and

$$
 \|K_\delta f\|_{L^n(S^{n-1})}\le C_nL^{(n-1)/n}\|f\|_{L^n(\mathbb R^n)} .
$$

This is `KakeyaPalomar.sharpMaximalBound` in `Solution.lean`.
The constant is chosen before $\delta$ and $f$.

**Theorem 2 (weighted tube estimate).**
Let $q:=n/(n-1)$.
There is $C_n>0$ such that for every $0<\delta\le1$, every finite family of unit vectors $\omega_j$ with $|\omega_i-\omega_j|\ge\delta$ for $i\ne j$, every choice of centers $x_j$, and every choice of coefficients $a_j\ge0$,

$$
 \int_{\mathbb R^n}\Bigl(\sum_ja_j1_{T_{2\delta}(\omega_j,x_j)}\Bigr)^q\,dx\le C_nL\,\delta^{n-1}\sum_ja_j^q .
$$

This is `KakeyaPalomar.sharpTubeBound`.
The radius $2\delta$ agrees with the formal statement; since $T_\delta\subset T_{2\delta}$, the same bound holds for radius-$\delta$ tubes.
Neither theorem carries any further analytic hypothesis.

Taking the $q$-th root in Theorem 2 produces $L^{1/q}=L^{(n-1)/n}$, and the proof of Theorem 1 passes from Theorem 2 to the maximal operator by duality over finite sets of centers and a direction net, which is where the power $(n-1)/n$ enters.

## Union volume and Kakeya sets

**Corollary 3 (tube union).**
For $N$ radius-$\delta$ tubes $T_j$ in $\delta$-separated directions with arbitrary centers,

$$
 \Bigl|\bigcup_{j=1}^NT_j\Bigr|\ge c_n\frac{N\delta^{n-1}}{L^{n-1}} .
$$

*Proof.*
The empty family is trivial.
Otherwise put $M:=\sum_j1_{T_j}$, $U:=\bigcup_jT_j$, and $A:=N\delta^{n-1}$, so that $\int M=\sum_j|T_j|\asymp_nA$.
Let $M_2:=\sum_j1_{T_{2\delta}(\omega_j,x_j)}$ be the overlap of the enlarged tubes; then $M\le M_2$ pointwise, and Theorem 2 with unit coefficients gives $\int M^q\le\int M_2^q\lesssim_nLA$.
Hölder's inequality on $U$ yields

$$
 A\lesssim_n\int_UM\le|U|^{1/n}\Bigl(\int M^q\Bigr)^{(n-1)/n}\lesssim_n|U|^{1/n}(LA)^{(n-1)/n}.
$$

Raising to the $n$-th power and dividing by $A^{n-1}$ proves the claim. $\square$

**Corollary 4 (Kakeya neighbourhoods).**
If $K\subset\mathbb R^n$ is a Kakeya set, then $|N_\delta(K)|\ge c_nL^{-(n-1)}$.

*Proof.*
Choose a maximal $\delta$-separated set of unit vectors; it has $N\asymp_n\delta^{-(n-1)}$ elements.
For each such direction, the radius-$\delta$ tube about the unit segment of $K$ in that direction lies in $N_\delta(K)$.
Corollary 3 applied to these tubes gives $|N_\delta(K)|\gtrsim_nN\delta^{n-1}L^{-(n-1)}\asymp_nL^{-(n-1)}$. $\square$

Fernández-Delgado and de la Salle (arXiv:2607.14824, Theorem 1.3) prove that for every $n\ge2$ there exist a fixed Kakeya set $K\subset\mathbb R^n$ and a constant $C$ with $|N_\delta(K)|\le C|\log\delta|^{-(n-1)}$ for every $\delta\in(0,1)$.
Their paper describes this order as conjecturally optimal; Corollary 4 supplies the matching lower bound, as a consequence of Theorem 2 and the written Hölder step above.
Selecting $\delta$-separated directions in their set gives tube families that show Corollary 3 is sharp when $N\asymp_n\delta^{-(n-1)}$.
Sharpness is asserted only in this full-direction regime, not for every sparse value of $N$.

| Dimension | Maximal norm | Smallest neighbourhood volume |
| --- | --- | --- |
| $2$ | $L^{1/2}$ | $L^{-1}$ |
| $3$ | $L^{2/3}$ | $L^{-2}$ |
| $4$ | $L^{3/4}$ | $L^{-3}$ |
| $n$ | $L^{(n-1)/n}$ | $L^{-(n-1)}$ |

## Consequences for the Kakeya conjectures

The Kakeya maximal function conjecture asks for $\|K_\delta\|_{L^n(\mathbb R^n)\to L^n(S^{n-1})}\lesssim_{n,\varepsilon}\delta^{-\varepsilon}$ for every $\varepsilon>0$.
For each such $\varepsilon$, the function $\delta^\varepsilon[\log(2/\delta)]^{(n-1)/n}$ is bounded on $(0,1]$, so Theorem 1 implies this estimate in every dimension.

Corollary 4 gives lower and upper Minkowski dimension $n$ for every bounded Kakeya set $K$.
Indeed, let $N(K,\delta)$ be the least number of radius-$\delta$ balls covering $K$.
Their concentric radius-$2\delta$ balls cover $N_\delta(K)$, so

$$
 N(K,\delta)\gtrsim_n\delta^{-n}[\log(2/\delta)]^{-(n-1)}.
$$

Taking logarithms and dividing by $\log(1/\delta)$ gives lower Minkowski dimension at least $n$, because $\log\log(2/\delta)/\log(1/\delta)\to0$.
Boundedness gives upper Minkowski dimension at most $n$.
These are written consequences of the estimates; no claim of priority is made.

## Sharpness of the maximal and overlap estimates

For $0<\delta\le1/256$ let $f_\delta(y):=|y|^{-1}1_{\{2\delta<|y|<1/2\}}$.
Then $\|f_\delta\|_n^n=\sigma(S^{n-1})\log(1/(4\delta))$, while every tube $T_\delta(\omega,0)$ through the origin has average at least $c_n\log(1/\delta)$, because $f_\delta\ge1/(2t)$ on the cylinder $\{t\omega+z:4\delta<t<1/4,\ z\perp\omega,\ |z|<\delta/2\}$ inside the tube.
Hence $\|K_\delta f_\delta\|_n/\|f_\delta\|_n\ge c_n[\log(1/\delta)]^{(n-1)/n}$.
This rules out a smaller power and any factor that is little-oh of $L^{(n-1)/n}$, including division by a growing iterated logarithm.
The complete calculation for the exact tube is in `STATEMENT_AND_OPTIMALITY.md`.

The one logarithm in Theorem 2 is also necessary.
With all centers at the origin, a maximal $\delta$-separated set of directions, and unit coefficients, the overlap function satisfies $M(r\theta)\gtrsim_nr^{-(n-1)}$ for $C\delta\le r\le c$, so $\int M^q\gtrsim_n\int_{C\delta}^cdr/r\asymp\log(1/\delta)$ while $\delta^{n-1}\sum_ja_j^q\asymp_n1$.
Besicovitch families give the same conclusion in the opposite way: they have $\int M\asymp_n1$ and $|U|\lesssim_nL^{-(n-1)}$, and Hölder's inequality in the form $\int M^q\ge(\int M)^q/|U|^{q-1}$ yields $\int M^q\gtrsim_nL$.
These are statements about the dependence on $\delta$ for fixed $n$; no optimal numerical constant is asserted.

## Formal scope and sources

Theorems 1 and 2 are the two submitted Lean results.
Corollaries 3 and 4, the sharpness arguments, and the consequences above are written deductions and are not separately formalized in this package.
The matching construction is an external result.
No claim of a sharp Hausdorff gauge or of priority is made.

The Lean 4.34.1 proof checks and semantic audits have passed.
Claude's AI review on 14 November 2026 found no semantic defect in the two statements and recompiled all 212 local files from source against cached OpenAI and mathlib artifacts.
The earlier Lake log retains successful completion but only as a tail excerpt.
The review and the accepted editorial changes are preserved in `review/claude/INTEGRATION.md`; this is not independent human mathematical review or independent kernel replay.
Verification on the targeted Lean 4.35.0 configuration, the official Palomar Comparator, and an independent kernel replay remain pending.
The exact status is listed in `VALIDATION.json` and `CLAIMS.md`.

- R. J. Fernández-Delgado and M. de la Salle, [A construction of Kakeya Sets in Arbitrary Dimension](https://arxiv.org/abs/2607.14824), Theorem 1.3.
- OpenAI, [Local smoothing for the Euclidean wave equation, Kakeya section](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/Local-smoothing-for-the-Euclidean-wave-equation-October-25-2026/build/sections/kakeya.tex). This source records the radial obstruction; its displayed maximal upper power is $2(n-1)/n$.
- `INFORMAL.md`, `TRACE_METHOD.md`, and `formalization.yaml` describe the proof route, upstream reuse, and changes from the working manuscript.
