# Sharp logarithmic Kakeya estimates in every dimension

## Abstract

We formalize in Lean two logarithmic upper bounds for the Euclidean Kakeya maximal operator and tube overlap in every integer dimension $n\ge2$.
For $r>0$, a unit vector $\omega$, and a center $x\in\mathbb R^n$, let $T_r(\omega,x)$ be the open radius-$r$ neighborhood of the unit segment centered at $x$ in direction $\omega$.
Write $|T_r(\omega,x)|$ for its Lebesgue volume, and define

$$
K_\delta f(\omega)
:=\sup_{x\in\mathbb R^n}
\frac{1}{|T_\delta(\omega,x)|}
\int_{T_\delta(\omega,x)} |f(y)|\,dy.
$$

For every $0<\delta\le1$ and every complex-valued $f\in L^n(\mathbb R^n)$, we prove

$$
\|K_\delta f\|_{L^n(S^{n-1})}
\le C_n\bigl[\log(2/\delta)\bigr]^{(n-1)/n}
\|f\|_{L^n(\mathbb R^n)}.
$$

For the tube estimate, fix $0<\delta\le1$ and any finite family of directions $\omega_1,\ldots,\omega_N\in S^{n-1}$ satisfying $|\omega_i-\omega_j|\ge\delta$ for $i\ne j$.
Choose arbitrary centers $x_1,\ldots,x_N\in\mathbb R^n$ and nonnegative real weights $a_1,\ldots,a_N$.
Writing $1_T$ for the indicator of a tube $T$, we prove

$$
\int_{\mathbb R^n}
\left(\sum_{j=1}^{N} a_j\,1_{T_{2\delta}(\omega_j,x_j)}(y)\right)^{\!\frac{n}{n-1}}
\,dy
\le
C_n\,\log(2/\delta)\,\delta^{n-1}
\sum_{j=1}^{N} a_j^{\frac{n}{n-1}}.
$$

The constants depend only on $n$.
The same inequality holds for radius-$\delta$ tubes by inclusion.
Hölder's inequality therefore gives, for $N$ such tubes $T_j=T_\delta(\omega_j,x_j)$,

$$
\left|\bigcup_{j=1}^{N}T_j\right|
\ge c_n\,\frac{N\delta^{n-1}}{[\log(2/\delta)]^{n-1}}.
$$

A direction net gives volume at least $c_n[\log(2/\delta)]^{-(n-1)}$ for the $\delta$-neighborhood of every Kakeya set, matching the construction of Fernández-Delgado and de la Salle.
Consequently every bounded Kakeya set has Minkowski dimension $n$, and the maximal estimate implies the Kakeya maximal function conjecture in every dimension.
Written lower-bound arguments establish the optimality of the logarithmic powers, including the exclusion of a growing iterated-logarithm improvement in the maximal estimate.

## Formal scope and verification

Only the two upper estimates are Lean theorems; the geometric consequences and sharpness arguments are not formalized here.
The local modules passed Lean 4.34.1 compilation and Claude's AI review against cached OpenAI and mathlib artifacts.
Lean 4.35.0 verification, the official Palomar Comparator, independent kernel replay, and independent human review remain pending.
Detailed evidence is recorded in `VALIDATION.json` and `review/claude/INTEGRATION.md`.

## Acknowledgments and AI usage

Developed under Mark Lewko's research direction with substantial ChatGPT/Codex assistance and a separate Claude AI review.
The project uses Lean and mathlib and reuses identified parts of OpenAI's harmonic-analysis formalization.
Sources, adaptations, and licenses are recorded in `formalization.yaml`; no claim of priority is made.
