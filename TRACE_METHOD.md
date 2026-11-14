# Weighted trace by smooth comparison

This note records the argument implemented in checkpoints 0.14.0 through 0.19.0. It proves
the trace estimate needed for arbitrary coefficients without constructing
general mixed Moore determinants, and follows its application through the
sharp weighted tube and maximal upper bounds in every dimension n>=2.
The matching logarithmic lower bounds are written out in
`STATEMENT_AND_OPTIMALITY.md`; they are not formalized. Historical checkpoint
references below explain the development; the current proof includes $m=1$.

Let $B=B_R(o)$ be the physical ball in $\mathbb R^{3m}$, with $R>0$
and $m\ge1$. Write $D$ for the actual three-slot quaternionic Hessian,
$G$ for its quaternionic gradient, and $\det$ for the signed Moore
determinant already defined in the project. An admissible $u$ is $C^3$
near the closed ball, vanishes on the boundary, and satisfies $Du\ge0$.
The checked maximum principle gives $u\le0$.

The barrier $\phi$ is $C^3$ near the closed ball and satisfies

$$
D\phi\ge0,\qquad -H\le\phi\le0,\qquad H\ge0.
$$

There is no boundary condition on $\phi$.

## Smooth comparison

Suppose $u,v$ are globally $C^3$ and have positive semidefinite Hessians
in $B$. Let $\chi$ be $C^1$, nondecreasing, and satisfy
$\chi(v-u)=0$ on the boundary. For
$u_s=u+s(v-u)$, differentiation under the integral and the checked
cofactor Green identity give

$$
\frac{d}{ds}\int_B\chi(v-u)\det Du_s
=-\int_B\chi'(v-u)\,
  \langle C(Du_s)G(v-u),G(v-u)\rangle\le0.
$$

Here $C$ is the actual first cofactor. Its nonnegativity includes singular
positive semidefinite Hessians. Integration over $0\le s\le1$ proves

$$
\int_B\chi(v-u)\det Dv\le\int_B\chi(v-u)\det Du.
$$

Lean theorem: thinDet_smooth_comparison.

## Sublevel masses

For $H,t>0$, put $U=-u$, $v=(t/H)\phi-t$, and
$\chi(s)=\mathrm{smoothTransition}(s/t)$. The transition is between
zero and one, equals zero when its argument is nonpositive, and equals one
when its argument is at least one. Consequently:

- $\chi(v-u)=0$ on the boundary and wherever $U\le t$.
- $\chi(v-u)=1$ wherever $U>3t$.
- $\det Dv=(t/H)^m\det D\phi$.

Smooth comparison therefore gives

$$
t^m\int_{\{U>3t\}}\det D\phi
\le H^m\int_{\{U>t\}}\det Du.
$$

No nonsmooth comparison principle or limiting approximation to an
indicator is used. Lean theorem: thinDet_sublevel_bound.

## Layer cake and the variational bound

Apply layer cake to the measures
$d\nu=(\det D\phi)\,dz$ and $d\mu=(\det Du)\,dz$, both restricted to
$B$. The tail comparison yields

$$
\begin{aligned}
\int_B U^{m+1}\,d\nu
&=(m+1)3^{m+1}\int_0^\infty t^m\nu\{U>3t\}\,dt\\
&\le 3^{m+1}(m+1)H^m\int_B U\,d\mu.
\end{aligned}
$$

Thus $K_m=3^{m+1}(m+1)$ is sufficient. Compact smooth extension transfers
the result to the original admissible class while preserving all actual
derivatives on the closed ball. A one-sided limit in $H+\varepsilon$
includes $H=0$. Lean theorem: ThinAdmissibleAt.trace_bound.

Let $q=(m+1)/m$. If a continuous source $\rho$ satisfies
$\rho\le b\det D\phi$, where $b\ge0$ and $b^q\det D\phi$ is
integrable, set $L=K_m^{1/m}H$. For $H>0$, scaled Young's inequality gives

$$
Ub\le\frac{U^{m+1}}{(m+1)L^m}
       +\frac{m}{m+1}L b^q.
$$

Multiply by $\det D\phi$, integrate, and use the trace estimate. The
first term is at most $\mathcal A(u)/(m+1)$, where
$\mathcal A(u)=\int_B(-u)\det Du$. Subtracting this energy term and
taking the original variational supremum proves

$$
F_B(\rho)\le C_m H\int_B b^q\det D\phi,
\qquad C_m=\frac{m}{m+1}K_m^{1/m}.
$$

The weight may be discontinuous. The zero-height case is again included
by a one-sided limit. Lean theorem: thinValueRealAt_weighted_bound.

## Explicit input barrier

For a unit orientation $(a,b)$, write
$\alpha_j=aP_{j,0}+bP_{j,1}$ and
$\beta_j=aP_{j,1}-bP_{j,0}$. The implemented quadratic form is

$$
q_0(x,P)=\sum_j\bigl((x_j+\alpha_j)^2+2\beta_j^2\bigr).
$$

Its actual derivatives satisfy
$Dq_0=8I$, $|Gq_0|^2=8q_0$, and
$0\le q_0\le2(|x|^2+|P|^2)$. For $h>0$, the barrier

$$
\phi_h=\log(h+q_0)-\log(h+2R^2)
$$

is globally smooth, has positive semidefinite Hessian, and obeys

$$
\det D\phi_h=\frac{8^m h}{(h+q_0)^{m+1}},\qquad
-\log\frac{h+2R^2}{h}\le\phi_h\le0\quad\text{on }\overline B_R(0).
$$

The determinant and gradient calculations hold in every unit orientation.
For $h=\delta^4$, $0<\delta\le1$, the height is bounded by
$C_R\log(2/\delta)$, with
$C_R=4+\log(1+2R^2)/\log2$.

The theorem inputBarrier_value_le_log combines these calculations with the
weighted variational bound.

## Normalized packet input

Checkpoint 0.15.0 supplies every remaining input hypothesis for the actual
Kakeya-scale family. Let $0<\delta\le1$, $h=\delta^4$, and let the
nonnegative packet weights be $\lambda_l$. The unscaled intercept vectors
$a_l$ satisfy $|a_l|^2\le A$; the actual packet intercepts are
$\delta^2a_l$. At time zero and every unit transverse orientation, a
nonzero cutoff implies

$$
|\alpha-v_l|^2\le5\delta^2,\qquad q_0(x,P)\le(3A+11)\delta^4.
$$

Write $Z_m>0$ for the cutoff mass. Exact mass normalization therefore gives

$$
\mu\le C_{m,A}w(\alpha)\det D\phi_{\delta^4},\qquad
C_{m,A}=\frac{(3A+12)^{m+1}}{8^m Z_m},\qquad
w(\alpha)=\sum_l\lambda_l\,1_{\{|\alpha-v_l|^2\le5\delta^2\}}.
$$

This is proved directly from the normalized density, not assumed.
The linear change of variables

$$
x=u-\alpha,\qquad P_0=a\alpha-b\beta,\qquad
P_1=b\alpha+a\beta
$$

has determinant $(-1)^m$ and preserves volume. In these coordinates,
$q_0=|u|^2+2|\beta|^2$. The previously checked radial primitive proves

$$
\int_{\mathbb R^{2m}}\frac{h}{(h+|P|^2)^{m+1}}\,dP
\le |B^{2m}_1|,
$$

uniformly in $h>0$, together with integrability over the whole space.

If the directions $v_l$ are $\delta$-separated, disjoint balls of radius
$\delta/2$ prove that at most $8^m$ centers lie within $3\delta$ of any
point. Finite Holder and the exact volume of the directional balls then
give

$$
\int w^q\le (8^m)^{q-1}3^m|B^m_1|\,\delta^m\sum_l\lambda_l^q,
\qquad q=(m+1)/m.
$$

The theorem kakeyaPacketFamily_input_estimate consequently proves

$$
F_{B_R}(\mu)\le C_{m,A,R}\log(2/\delta)\,
\delta^m\sum_l\lambda_l^{(m+1)/m}.
$$

The constant is explicit and positive and is independent of the scale,
number of packets, weights, directions and transverse orientation.
The source continuity and all required weighted integrability are proved.

## Single-log propagation

Checkpoint 0.15.0 also assembles the upstream radial comparison,
time averaging and fixed-region mixing into a single-log estimate for
smooth nonnegative superharmonic functions. For $0<\rho<1$, the function
need only be smooth and superharmonic where

$$
-5\pi-1<t<5\pi+1,\qquad \rho/2<|Y|<4.
$$

For every input angle $\theta$, the checked estimate is

$$
\int_1^2\int_0^{2\pi} f(t,\rho e^{i\varphi})\,d\varphi\,dt
\le C(1+|\log\rho|)\,f(0,e^{i\theta}),
$$

with one fixed positive constant $C$. The input point stays at radius one.
The outer comparison is localized in time, so no assumption is made at
arbitrarily large times. The proof imports the underlying OpenAI lemmas;
it does not use the upstream final cylinder bound with cubic log loss.

## Continuous weak propagation

Checkpoint 0.16.0 removes the smoothness assumption. Let \(K\) be the
closed cylinder in the preceding estimate, and let \(f\) be continuous,
nonnegative and weakly superharmonic on an open neighborhood \(\Omega\)
of \(K\). Extend \(f\) continuously to a global function agreeing with it
on a neighborhood of \(K\). Choose a fixed positive distance from \(K\)
to the complement of that neighborhood, and convolve the extension with
nonnegative normalized smooth kernels supported in successively smaller
balls.

For every sufficiently small kernel \(\kappa\), the actual derivative
calculation gives

$$
\Delta(f*\kappa)(x)=\int f(y)\,\Delta\kappa(x-y)\,dy\le0
\qquad(x\in K).
$$

The last inequality is precisely weak superharmonicity tested against
the nonnegative function \(y\mapsto\kappa(x-y)\). Kernel support,
reflection of the Laplacian, differentiation under convolution and
agreement with the original local function are all proved. The
approximations are nonnegative and uniformly bounded on \(K\).
Pointwise convergence and two applications of dominated convergence
pass both cylinder integrals to the limit. The input point also
converges.

For the actual packet family, the enlarged fixed parameter domain is

$$
(p_0-1)^2<576,\qquad 0<|Y|<5.
$$

If \(|a_l|^2\le A\) and \(|v_l|^2\le V\), its spatial support lies
strictly inside the fixed radius
\(\sqrt{\max(4A+2354V+2458,0)}+1\). Consequently the propagation theorem
applies directly to the continuous weak packet value. At
\(\rho=\delta^4\), it gives

$$
\int_1^2\int_0^{2\pi}F(t,\delta^4e^{i\theta})\,d\theta\,dt
\le C_{m,A,V}\log(2/\delta)^2\,
       \delta^m\sum_l\lambda_l^{(m+1)/m}.
$$

Here \(0<\delta<1\). No approximation or solution family is supplied as
an additional hypothesis.

## Finite-ball localization

Let the open balls \(B_j\) be pairwise disjoint and have closures inside
the outer ball \(B\). For a smooth positive source \(\mu\), let \(u\)
and \(u_j\) be the actual zero-boundary Dirichlet solutions on these
balls. The existing OpenAI comparison theorem, lifted and descended
through the already checked coordinates, gives \(u\le u_j\) on
\(\overline B_j\). Since \(u\le0\), the checked representation yields

$$
\sum_j F_{B_j}(\mu)
=\frac{m}{m+1}\sum_j\int_{B_j}(-u_j)\mu
\le\frac{m}{m+1}\int_B(-u)\mu
=F_B(\mu).
$$

Integrability, the finite disjoint-union identity and all comparison
hypotheses are checked. Replacing \(\mu\) by \(\mu+\varepsilon\)
and using the established continuity of the variational value proves
the same result for smooth nonnegative sources, including those that
vanish. Thus the earlier logarithmic thin-source lower bounds can be
added over this ball family.

## Actual output density and scale

Set \(r=\delta^2\) and \(h=\delta^4\). Suppose \(|Y|=h\),
\((p_0-1)^2\le r^2\), and a selected packet satisfies

$$
|v_l|^2\le\frac1{16},\qquad
|x-\delta^2a_l-(p_0-1)v_l|^2\le\frac{rh}{16},
\qquad |P|^2\le\frac{h^2}{16}.
$$

Evaluate the minimized phase at \(w=v_l\). The exact ratio identity
gives \(|\alpha|^2+|\beta|^2=|P|^2/h^2\). The resulting energy is
at most \(h/16+h/4<h/2\), so the fixed standard cutoff equals one.
Also
\((r+h)^2+(p_0-1)^2\le5r^2\). The actual prefactor and mass
normalization therefore give the pointwise lower bound

$$
\mu\ge c_m\delta^{-10m}\sum_{l\text{ selected}}\lambda_l,
\qquad c_m=\frac{5^{-m/2}}{Z_m}>0.
$$

For balls centered at \((x_j,0)\), take
\(R_j\le\delta^3/4\) and
\(\varepsilon_j\le\min(R_j/10,\delta^4/4)\).
If every selected axis is within \(\delta^3/8\) of \(x_j\), the
displayed bounds hold throughout the thin core of that ball.
Localization and the thin-source test give the sum of

$$
c'_m R_j^m\varepsilon_j^{2m+2}
\left(c_m\delta^{-10m}M_j\right)^{(m+1)/m}
\log(R_j/\varepsilon_j),
\qquad M_j=\sum_{l\text{ selected at }j}\lambda_l.
$$

For \(m\ge1\), \(R_j=r_0\delta^3\) and
\(\varepsilon_j=\varepsilon_0\delta^4\), the exact checked
identity reduces each term to

$$
C_{m,r_0,\varepsilon_0}\,
\delta^{m-2}M_j^{(m+1)/m}
\log\!\frac{r_0}{\varepsilon_0\delta}.
$$

The exponent \(m-2\) is a real exponent, equal to \(-1\) when \(m=1\).
The current Lean identities are `output_delta_power_real` and
`output_lower_scaling_real`; the earlier natural-power identities required
\(m\ge2\). The constant is positive when \(r_0,\varepsilon_0>0\).
Checkpoint 0.17.0 constructs the ball family and its relation to the
tube overlap integral, and completes time integration and cancellation
of the logarithm, as follows.

## Finite covering and the normalized tube bound

Fix \(m\ge1\), \(q=(m+1)/m\), \(A\ge0\), and \(0<\delta<1\).
Let \(a_l,v_l\in\mathbb R^m\) satisfy
\(|a_l|^2\le A\) and \(|v_l|\le1/4\), with nonnegative weights
\(\lambda_l\). Initially write

$$
M(t,x)=\sum_l\lambda_l
  \mathbf1_{\{|x-a_l-tv_l|\le\delta/64\}},
\qquad 0\le t\le1.
$$

The support of each slice lies in the closed ball of radius
\(\sqrt A+1\). Choose a fixed finite net \(b_j\) of this ball,
with distinct points separated by more than \(\delta/32\) and
covering radius \(\delta/32\). At time \(t\), set

$$
M_j(t)=\sum_{\{|b_j-a_l-tv_l|\le\delta/16\}}\lambda_l .
$$

Whenever \(|x-b_j|\le\delta/32\), each tube contributing to
\(M(t,x)\) contributes to \(M_j(t)\). The measurable finite-ball
majorant therefore gives

$$
\int_{\mathbb R^m}M(t,x)^q\,dx
\le c^{\mathrm{vol}}_m\delta^m\sum_jM_j(t)^q,
\qquad
c^{\mathrm{vol}}_m=32^{-m}|B_{\mathbb R^m}(0,1)|.
$$

This uses no maximum of the overlap function and no measurable choice
of a maximizing point. Joint measurability, integrability of every
spatial slice, and a time-uniform integral bound are proved directly
from the finitely many tube indicators.

Use physical centers \((\delta^2b_j,0)\), ball radius
\(\delta^3/100\), and transverse thickness \(\delta^4/1000\).
Their open balls are disjoint, and their closures lie in the fixed
outer ball. At \(p_0=1+\delta^2t\), a selected packet axis is
within \(\delta^3/16\) of the physical center. The proved localized
lower bound and exact scale identity thus give

$$
F(1+\delta^2t,\delta^4e^{i\theta})
\ge K_m\delta^{m-2}\log(10/\delta)\sum_jM_j(t)^q.
$$

Since \(\log(10/\delta)\ge\log(2/\delta)>0\), combining the two
bounds yields, for a positive dimension constant \(c_m\),

$$
c_m\log(2/\delta)\int M(t,x)^q\,dx
\le\delta^2F(1+\delta^2t,\delta^4e^{i\theta}).
$$

The angular trace of the continuous variational value is continuous
on \(1\le p_0\le2\). This is proved by extension near the compact
cylinder and continuity of parameterized integrals; smoothness of
the value is unnecessary. Integrating in angle and time, using the
exact affine substitution and nonnegativity, gives

$$
\begin{aligned}
2\pi c_m\log(2/\delta)\int_0^1\int M(t,x)^q\,dx\,dt
&\le\int_1^{1+\delta^2}\int_0^{2\pi}
    F(s,\delta^4e^{i\theta})\,d\theta\,ds\\
&\le C_{m,A}\log(2/\delta)^2\delta^m
    \sum_l\lambda_l^q.
\end{aligned}
$$

Here the last step uses the checked input and propagation bounds,
assuming the slopes \(v_l\) are \(\delta\)-separated. Cancellation
of the positive logarithm proves

$$
\int_0^1\int M(t,x)^q\,dx\,dt
\le C'_{m,A}\log(2/\delta)\delta^m\sum_l\lambda_l^q.
$$

Lean theorem: Packet.exists_normalizedTube_constant.

## Fixed radius enlargement

Take a fixed finite \(1/64\)-net \(u_j\) of the radius-two ball.
The radius-\(2\delta\) graph tube with intercept \(a_l\) is covered
by the radius-\(\delta/64\) graph tubes with intercepts
\(a_l+\delta u_j\). The slopes are unchanged, and
\(|a_l+\delta u_j|^2\le2A+8\).
If the net has \(J\) points, finite Holder gives

$$
\left(\sum_j M_j\right)^q\le J^{q-1}\sum_jM_j^q.
$$

Applying the normalized estimate separately to each translated family
proves the same single-log bound for radius-\(2\delta\) graph tubes.
The factor depending on \(J\) is dimensional and independent of
\(\delta\), the original tube count and the weights.
Lean theorem: Packet.exists_enlargedGraphTube_constant.

The ambient dimension of these graph tubes is \(n=m+1\ge3\).
At checkpoint 0.17.0, arbitrary locations and directions, exact Euclidean
unit-segment conventions, the planar endpoint, and a matching logarithmic
lower-bound example remained unproved.

## From graph tubes to arbitrary Euclidean tubes

Checkpoint 0.18.0 completes the upper bound in every \(n\ge3\).
Put \(m=n-1\) and \(q=(m+1)/m\). All constants below depend only on dimension.

First partition the intercepts \(a_l\) using a finite 2-separated net
\(\{b_j\}\), assigning \(l\) to a point within distance 2. If a group
contributes at \((t,x)\), with \(0\le t\le1\), slopes of norm at most \(1/4\)
and graph radius \(2\delta\le2\), then \(|b_j-x|\le6\).
Packing gives at most \(8^m\) such groups. For their overlaps \(M_j\),

$$
M(t,x)^q\le (8^m)^{q-1}\sum_j M_j(t,x)^q.
$$

Translate each group by \(-b_j\). Its active intercepts have squared norm
at most 4; inactive coefficients vanish. The previously proved estimate
applies with the fixed intercept bound \(A=4\), while

$$
\sum_j\sum_l(\lambda_l1_{\{l\text{ assigned to }j\}})^q
=\sum_l\lambda_l^q.
$$

Thus the intercept restriction disappears without a factor depending
on the number of occupied regions. Lean theorems:
Packet.normalizedTubeMoment_spatial_le and
Packet.exists_globalGraphTube_constant.

At \(1/2\le\delta\le1\), packing all slopes in the fixed small ball gives
a direct bound with the same scale and logarithm. This includes \(\delta=1\).
Translation of time changes the intercept from \(a_l\) to \(a_l+\tau v_l\).
Additivity of interval integrals yields the estimate on
\([\tau,\tau+K]\), with factor \(K\), for every natural \(K\).
A fixed finite spatial cover further enlarges the graph radius to
\(8\delta\), preserving slope separation. These are the theorems in
Packet.GraphEndpoint, Packet.GraphTimeIntervals and Packet.BroadGraphTubes.

Split \(y\in\mathbb R^{m+1}\) as \(y=(t,x)\). The coordinate equivalence
preserves actual Lebesgue volume. Write \(e_0=(1,0)\).
For a unit direction \(v\) with \(|v-e_0|\le1/16\), define

$$
s(v)=\frac{v'}{v_0},\qquad a(c,v)=c'-c_0s(v).
$$

Here \(v'\) and \(c'\) are the last \(m\) coordinates. The checked
inequalities give \(v_0>0\), \(|s(v)|\le1/4\), and

$$
|v-w|\le2|s(v)-s(w)|.
$$

Thus \(\delta\)-separated unit directions give
\(\eta\)-separated slopes with \(\eta=\delta/2\).
For an actual radius-\(2\delta\) tube about the centered unit segment,
every \(y=(t,x)\) in the tube satisfies

$$
|x-a(c,v)-t\,s(v)|\le\frac52\delta.
$$

If \(c_0\in[-2,2]\), its time coordinate belongs to \([-5,5]\).
These statements include both end caps, not only the cylindrical part.
Use the graph estimate with radius \(8\eta=4\delta\), which contains
this transverse error, and use

$$
\log(2/\eta)\le2\log(2/\delta),\qquad \eta^m\le\delta^m.
$$

Joint measurability, integrability, Fubini, and the exact coordinate
change turn pointwise containment into the one-chart tube estimate.
Lean theorems: Graph.powerWindow_integral and Graph.exists_chartTube_constant.

Next apply a 2-separated spatial net to the actual Euclidean centers.
At a point of any unit tube of radius at most 2, its center is within
distance \(5/2\). Hence only at most \(8^{m+1}\) groups contribute.
After translation, all centers in a group have norm at most 2, so their
longitudinal coordinates lie in \([-2,2]\). The same finite Holder and
coefficient partition remove all center restrictions.
Lean theorem: Graph.exists_globalChartTube_constant.

Finally cover the unit sphere by finitely many caps of radius \(1/16\).
Reflection across the orthogonal complement of the difference between a
cap center and \(e_0\) sends that center to \(e_0\). These maps preserve
distances, actual Euclidean tubes and volume. Restrict each class to its
own finite index set, rotate it, and apply the global one-chart estimate.
Finite Holder over the fixed number of charts proves

$$
\int_{\mathbb R^n}\left(\sum_l\lambda_l1_{T_l}\right)^{n/(n-1)}
\le C_n\log(2/\delta)\delta^{n-1}
\sum_l\lambda_l^{n/(n-1)}
$$

for arbitrary centers and \(\delta\)-separated unit directions,
\(0<\delta\le1\). Each \(T_l\) is the open radius-\(2\delta\)
neighborhood of the centered unit segment.

Lean theorem sharpTubeBound_of_three_le proves the original
SharpTubeBound proposition. Applying the existing maximal transfer gives
sharpMaximalBound_of_three_le, with no supplied analytic hypothesis:

$$
\|K_\delta f\|_{L^n(S^{n-1})}
\le C_n\log(2/\delta)^{(n-1)/n}\|f\|_{L^n(\mathbb R^n)},
\qquad n\ge3.
$$

The theorem uses the supremum over every spatial center and the actual
tube-volume normalization. It includes measurability and membership in
\(L^n\). At that checkpoint, the planar extension and a written matching logarithmic
lower bound were still pending; their current status is recorded below.

## Including the planar case

Checkpoint 0.19.0 extends the same proof to transverse dimension m=1,
hence to ambient dimension n=2. The new radial estimate retains the
radius r rather than using the squared-radius boundary substitution.
For a>0 and 0<=r<=1,

    boundaryKernel(a,1-r^2) <= 1 + 1/(a+1-r).

The radial factor r^(m-1) is at most one for every m>=1. The scalar integral
of the displayed majorant is 1+log((a+1)/a), which is at most
6 log(1/eta) when a=eta^2 and 0<eta<=1/10. Multiplying by the radial volume
constant gives spatial_boundary_integral_log_of_one_le. The energy bound
and amplitude optimization require only an enlarged dimension constant;
all downstream thin-source estimates then hold for m>=1.

The localized scale factor is delta raised to the real exponent m-2.
The new output_delta_power_real and output_lower_scaling_real retain this
exponent, so the planar case gives delta^(-1), not a truncated natural
power. The time-change factor delta^2 recovers delta^m. The rest of the
graph covering, arbitrary location and direction assembly, and maximal
transfer is unchanged in form.

The final Lean theorems are sharpTubeBound_of_two_le and
sharpMaximalBound_of_two_le. Their only dimension hypothesis is n>=2.
Audit.lean checks their full types, axiom dependencies and explicit n=2
applications. The matching lower bounds are now written in
`STATEMENT_AND_OPTIMALITY.md`, and the tube union and Kakeya-neighborhood
consequences in `SUMMARY.md`. These remain outside the two formal targets.
