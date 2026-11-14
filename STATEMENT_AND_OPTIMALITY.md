# Statement audit and logarithmic optimality

14 November 2026.

The submitted upper bound is exactly the strong critical Kakeya maximal
inequality below. Its logarithmic dependence is optimal up to constants
depending on dimension. The upper bound and the semantic checks are checked
in Lean 4.34.1. The elementary matching lower bound in this note is a
mathematical proof, not a Lean theorem in this submission. The Lean 4.35.0
build, official Palomar Comparator, and independent kernel replay remain
pending.

## The precise statement

Fix an integer $n\ge2$. Let $dx$ be Lebesgue measure on $\mathbb R^n$ and
$d\sigma$ the usual, unnormalized surface measure on $S^{n-1}$.
For $0<\delta\le1$, $\omega\in S^{n-1}$ and $x\in\mathbb R^n$, put

```math
 T_\delta(\omega,x)
 =\bigcup_{-1/2\le t\le1/2} B(x+t\omega,\delta),\qquad
 K_\delta f(\omega)
 =\sup_{x\in\mathbb R^n}\frac1{|T_\delta(\omega,x)|}
                   \int_{T_\delta(\omega,x)}|f(y)|\,dy.
```

There exists $C_n>0$ such that, for every $0<\delta\le1$ and every
complex-valued $f\in L^n(\mathbb R^n)$, the maximal function belongs to
$L^n(S^{n-1},d\sigma)$ and

```math
 \|K_\delta f\|_{L^n(S^{n-1},d\sigma)}
 \le C_n[\log(2/\delta)]^{(n-1)/n}\|f\|_{L^n(\mathbb R^n)}.
```

The quantifier order is $\forall n\ge2\;\exists C_n>0\;\forall\delta\;
\forall f$. Thus $C_n$ cannot depend on $\delta$, $f$, the tube center,
or the direction. There are no unproved analytic hypotheses in the
submitted theorem. It applies to all $L^n$ functions, without a support
restriction, and takes a supremum over all spatial centers.

The normalization uses the actual volume of the open tube, including its
end caps. Probability surface measure changes only the dimensional
constant. The theorem gives strong $L^n$ control, including membership,
and does not merely control indicators or distribution functions.

## Checks of the meaning of the Lean declarations

`SemanticAudit.lean` proves the following statements using the compiled
`Solution` module. All eleven declarations have only `propext`,
`Classical.choice`, and `Quot.sound` in their axiom reports.

| Check | What it establishes |
| --- | --- |
| `literal_maximal_statement` | The theorem with the tube union and full spatial supremum expanded, and canonical mathlib `MemLp`, `eLpNorm`, `volume`, and `Real.rpow` written explicitly |
| `space_dimension` | The ambient Euclidean space has real dimension exactly $n$ |
| `extended_output_norm_is_identity` | The extended norm used for nonnegative maximal values is the value itself |
| `sphere_total_mass` | The spherical measure has total mass $n\,|B(0,1)|$ |
| `sphere_mass_positive`, `sphere_mass_finite` | The measure on directions is nonzero and finite for $n\ge2$ |
| `sphere_supported_on_unit_vectors` | Almost every measured direction has Euclidean norm one |
| `tube_membership` | Tube membership means distance less than $\delta$ from a point of the stated unit segment |
| `actual_tube_volume_positive_finite` | Every denominator is strictly positive and finite |
| `includes_every_center` | The maximal function dominates the average at each arbitrary center |
| `indicator_of_tube_is_nontrivial` | A tube's indicator has maximal average at least one in its own direction |

`scripts/audit_statement_bindings.py` separately loads `Challenge` and
`Solution` and compares the exact representations of their elaborated Lean
expressions, after normalizing only bound variable names and metadata.
All constants, arguments and typeclass instances are preserved. It compares
the types and bodies of `Space`, `sphereMeasure`,
`tube`, and `kakeyaMaximal`, and the types of both submission theorems.
The challenge imports only canonical mathlib. This checks that the two
environments bind the same written notation to the same declarations and
instances. It is an additional local audit, not the official Comparator.

The local mathlib checkout is at
`d13f23b723b8a846827a245b89c10fc7d3f11612`, with no tracked source changes
reported by Git. Reports are in
`provenance/semantic-audit-lean434.txt` and
`provenance/statement-bindings-lean434.json`.

## Matching lower bound

Let $\kappa_j$ denote the volume of the unit ball in $\mathbb R^j$, and
let $s_{n-1}=\sigma(S^{n-1})=n\kappa_n$. For $0<\delta\le1/256$, set

```math
 f_\delta(y)=|y|^{-1}\mathbf1_{\{2\delta<|y|<1/2\}}(y).
```

This is a bounded, compactly supported, nonnegative function, hence an
admissible complex-valued $L^n$ input. Polar coordinates give the exact
identity

```math
 \|f_\delta\|_n^n
 =s_{n-1}\int_{2\delta}^{1/2}\frac{dr}{r}
 =s_{n-1}\log\frac1{4\delta}
 \le s_{n-1}\log\frac1\delta.
```

Fix any unit direction $\omega$. Inside $T_\delta(\omega,0)$ integrate
over the cylinder

```math
 y=t\omega+z,\qquad 4\delta<t<1/4,\quad
 z\perp\omega,\quad |z|<\delta/2.
```

Here $t$ is in the defining unit segment, the distance to $t\omega$ is
less than $\delta$, and $2\delta<|y|<1/2$. Moreover
$|y|\le t+\delta/2\le2t$, so $f_\delta(y)\ge1/(2t)$. Therefore

```math
 \int_{T_\delta(\omega,0)}f_\delta(y)\,dy
 \ge\frac{\kappa_{n-1}}{2^n}\delta^{n-1}
          \log\frac1{16\delta}.
```

The volume of a radius-$\delta$ neighborhood of a unit segment is
$\kappa_{n-1}\delta^{n-1}+\kappa_n\delta^n$, and is at most
$(\kappa_{n-1}+\kappa_n)\delta^{n-1}$ when $\delta\le1$.
Also $\log(1/(16\delta))\ge\tfrac12\log(1/\delta)$ for
$\delta\le1/256$. It follows, for every $\omega$, that

```math
 K_\delta f_\delta(\omega)\ge c_n\log(1/\delta),\qquad
 c_n=\frac{\kappa_{n-1}}
 {2^{n+1}(\kappa_{n-1}+\kappa_n)}>0.
```

Taking the norm on the sphere and dividing by the input norm gives

```math
 \frac{\|K_\delta f_\delta\|_n}{\|f_\delta\|_n}
 \ge c_n[\log(1/\delta)]^{(n-1)/n}.
```

Together with the checked upper bound, this establishes

```math
 \boxed{\quad\|K_\delta\|_{L^n(\mathbb R^n)\to L^n(S^{n-1})}
 \asymp_n [\log(2/\delta)]^{(n-1)/n}\quad(\delta\downarrow0).\quad}
```

Consequently no smaller logarithmic power works. More generally, the
factor cannot be replaced by a function that is little-oh of it. In
particular, dividing by any positive power of a growing iterated logarithm
fails. This is optimality of the dependence on scale for each fixed
dimension; no optimal dimensional constant is asserted.

The same radial obstruction appears in the paragraph beginning “The radial
test” in [OpenAI's Kakeya deductions from local smoothing](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/Local-smoothing-for-the-Euclidean-wave-equation-October-25-2026/build/sections/kakeya.tex).
That source has upper power $2(n-1)/n$ and lower power $(n-1)/n$; the upper
bound in this submission is the smaller, matching power. The calculation
above checks the lower bound directly for this submission's precise tubes.

## The one logarithm in the tube formulation

The second submitted theorem has $q=n/(n-1)$ and states

```math
 \int\Big(\sum_i a_i\mathbf1_{T_{2\delta}(v_i,x_i)}\Big)^q
 \le C_n\log(2/\delta)\,\delta^{n-1}\sum_i a_i^q
```

for arbitrary finite $\delta$-separated unit directions, arbitrary centers,
and nonnegative coefficients. Its one logarithm is also necessary.
To see this, choose a maximal $\delta$-separated set of unit directions,
put all centers at zero, and let all coefficients be one.

There are $N\asymp_n\delta^{-(n-1)}$ directions. For a point $r\theta$
with $C\delta\le r\le c$, where $c>0$ is a sufficiently small fixed
constant, all directions in the cap of radius $\delta/(2r)$ about
$\theta$ have a tube containing that point: the point $r v_i$ belongs
to the segment and $|r\theta-rv_i|<\delta/2$. The covering property of
a maximal separated set, and the usual cap-volume estimates, give at
least $c_n r^{-(n-1)}$ such directions. Thus, writing $M$ for the sum of
the tube indicators, polar coordinates yield

```math
 \int M^q\gtrsim_n
 \int_{C\delta}^{c}r^{-(n-1)q}r^{n-1}\,dr
 =\int_{C\delta}^{c}\frac{dr}{r}
 \asymp\log(1/\delta),
 \qquad \delta^{n-1}\sum_i a_i^q\asymp_n1.
```

This also proves sharpness of the tube logarithm mathematically. This
lower-bound construction, like the radial lower bound, is not formalized
in the present submission.
