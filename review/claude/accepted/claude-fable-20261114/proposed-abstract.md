# Proposed abstract

Reviewer note.
This text replaces `ABSTRACT.md`.
It keeps every factual claim of the current abstract, moves the statement of formal scope to the first paragraph, names the two conventions of the tube estimate, adds one sentence on consequences, and refreshes the verification status.
Bracketed items are for the author to confirm; the reviewer's knowledge of the literature ends in mid-2026.

---

# Abstract

We formalize in Lean two logarithmic upper estimates for the Euclidean Kakeya maximal operator in every integer dimension $n\ge2$.
The logarithmic powers in both estimates are optimal, and the optimality is proved by written arguments supplied alongside the formal theorems.

Let $T_\delta(\omega,x)$ denote the open $\delta$-neighbourhood of the unit segment centered at $x\in\mathbb R^n$ with direction $\omega\in S^{n-1}$, and let $K_\delta f(\omega)$ be the supremum over all centers $x$ of the average of $|f|$ over $T_\delta(\omega,x)$, normalized by the actual Lebesgue volume of the tube.
The first formal theorem is the strong bound
\[
 \|K_\delta f\|_{L^n(S^{n-1})}\le C_n[\log(2/\delta)]^{(n-1)/n}\|f\|_{L^n(\mathbb R^n)},
 \qquad 0<\delta\le1,\ f\in L^n(\mathbb R^n),
\]
with $C_n$ depending only on $n$, membership of $K_\delta f$ in $L^n(S^{n-1})$ included.
The second is the weighted overlap estimate at the exponent $q=n/(n-1)$: for finitely many $\delta$-separated unit directions $\omega_j$, arbitrary centers $x_j$, and coefficients $a_j\ge0$,
\[
 \int_{\mathbb R^n}\Bigl(\sum_j a_j1_{T_{2\delta}(\omega_j,x_j)}\Bigr)^q\,dx
 \le C_n\log(2/\delta)\,\delta^{n-1}\sum_j a_j^q .
\]
The radius $2\delta$ is the convention of the formal statement; the radius-$\delta$ version follows by domination.

Hölder's inequality turns the second estimate into the union bound $|\bigcup_{j\le N}T_j|\ge c_nN\delta^{n-1}[\log(2/\delta)]^{-(n-1)}$ for $N$ radius-$\delta$ tubes in $\delta$-separated directions, and a direction net then gives $|N_\delta(K)|\ge c_n[\log(2/\delta)]^{-(n-1)}$ for the $\delta$-neighbourhood of every set $K$ containing a unit segment in every direction.
Fernández-Delgado and de la Salle construct, in every dimension, a Kakeya set whose $\delta$-neighbourhoods have volume at most $C|\log\delta|^{-(n-1)}$, so the neighbourhood bound is attained.
A radial test function shows that the power $(n-1)/n$ in the maximal estimate cannot be lowered, even by a growing iterated logarithm.
In particular the maximal theorem implies the Kakeya maximal function conjecture in every dimension with the endpoint logarithmic loss, and in dimension two it recovers Córdoba's bound [author to confirm the literature status].

Only the two upper estimates are Lean theorems.
The union and neighbourhood bounds, the matching lower bounds, and the comparison with the literature are written mathematical arguments and are not formalized here.
No claim of optimal constants, of a sharp Hausdorff gauge, or of priority is made.

## Verification status

The source checkpoint and the module-ported submission have passed Lean 4.34.1 compilation and axiom checks, and both theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.
An AI review (Claude, 14 November 2026, `review/claude/runs/claude-fable-20261114/`) compared the Lean statements with the intended theorems, recompiled the local proof modules from source in Lean 4.34.1, and found no issue; it is not a human review.
The target Lean 4.35.0 build, the official Palomar Comparator, and an independent kernel replay remain pending.
See `VALIDATION.json`.

## Acknowledgments and AI usage

This project was developed under Mark Lewko's research direction with substantial ChatGPT/Codex assistance, and it reuses identified parts of OpenAI's harmonic-analysis formalization under Apache-2.0.
Exact source revisions, adaptations, licenses, and the division between formalized results and written consequences are recorded in `formalization.yaml` and the provenance files.
Independent human mathematical review is not claimed.
