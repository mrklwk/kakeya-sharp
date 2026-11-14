# Sharp Kakeya maximal: Lean checkpoint

Status: **sharp maximal upper bound proved for every n >= 2; nineteenth checkpoint
(14 November 2026)**. A matching logarithmic lower-bound example remains
to be formalized.

The sharp tube and maximal upper bounds now include the planar case.
A radial boundary estimate valid in transverse dimension one and a real
exponent scale identity extend the same argument to n=2. All tube locations
and directions are allowed, and the constant depends only on dimension.
No packet estimate, PDE solution, trace inequality or tube-overlap bound
is supplied as a hypothesis.

The project compiles with Lean 4.34.1 and mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Checked theorems

```lean
theorem sharpTubeBound_of_two_le {n : ℕ} (hn : 2 ≤ n) : SharpTubeBound n

theorem sharpMaximalBound_of_two_le {n : ℕ} (hn : 2 ≤ n) : SharpMaximalBound n
```

The first theorem proves, for 0 < delta <= 1,

    integral (sum_i a_i 1_{T_i})^(n/(n-1))
      <= C_n log(2/delta) delta^(n-1) sum_i a_i^(n/(n-1)).

The directions are arbitrary delta-separated unit vectors, the centers
are arbitrary, and the coefficients are arbitrary nonnegative reals.
Each T_i is the open radius-2-delta neighborhood of a centered unit segment,
including its end caps. The positive C_n is uniform in the scale, the
number of tubes, their positions, directions and coefficients.

The second theorem concerns the actual Euclidean maximal operator, defined
as the supremum of tube averages over every spatial center and normalized
by the actual tube volume. For every complex f in L^n(R^n), it proves
measurability, membership of K_delta f in L^n on the sphere, and

    ||K_delta f||_n <= C_n log(2/delta)^((n-1)/n) ||f||_n.

The earlier `sharpMaximal_of_sharpTube` remains available as a conditional
transfer in every n >= 2. `SharpTheorem.lean` now supplies its hypothesis
by an actual proof for every such dimension. Both final theorems have been
checked for axiom dependencies: only `propext`, `Classical.choice`, and `Quot.sound`
occur. The project has not yet formalized the matching lower bound that
proves logarithmic optimality.

## Checked parts of the logarithmic test

`ThinProfile.lean` defines the actual function

    v_eta(x,P) = log((eta^2 + |P|^2)/(eta^2 + 1 - |x|^2)).

It proves smoothness near the closed unit ball, nonpositivity in the ball,
zero boundary values, and

    -v_eta(x,P) >= log(1/eta)

when 0 < eta <= 1/10, |x| <= 1/2 and |P| <= eta.

The transverse space uses coordinates indexed by `Fin m × Fin 2`, so it has
real dimension 2m. The three directions at index j are x_j, P_(j,0), P_(j,1).

`HessianCalculus.lean` and `ThinHessian.lean` now derive the complete Hessian
from actual iterated Frechet derivatives, using quaternionic slots 1, i, j:

    D v_eta = (4/b) I - (1/b^2) g g* + (2/d) I + (4/d^2) x x*,
    b = eta^2 + |P|^2,  d = eta^2 + 1 - |x|^2,
    g_j = 2 P_(j,0) i + 2 P_(j,1) j,  sum_j |g_j|^2 = 4 |P|^2.

`ThinPositive.lean` proves Hermitian symmetry and the quadratic-form bound

    D v_eta >= (4 eta^2/b^2 + 2/d) I > 0.

This is a quantified inequality on every quaternionic vector, with strict
positivity on nonzero vectors. No positivity assumption is supplied by the caller.

`ThinDeterminant.lean` proves, for every m >= 1,

    det((4/b + 2/d) I - g g*/b^2)
      = (4/b + 2/d)^(m-1) (4 eta^2/b^2 + 2/d),

and the bound for the full Hessian

    det D v_eta <= 4 * 6^(m-1) *
      (eta^2/b^(m+1) + 1/(d b^(m-1)) + |x|^2/(d^2 b^(m-1))).

Here `det` is the signed Moore determinant defined by an explicit Pfaffian
polynomial. The project checks its normalization, rank-one affineness and
inverse-trace differential identity. The determinant bound is proved using
an explicit inverse and quaternionic Cauchy--Schwarz. It is not an assumed
spectral formula or a separately defined scalar substitute for the determinant.

`RadialIntegrals.lean` proves, for a > 0, s >= 0 and k a natural number,

    integral_0^s t^k a/(a+t)^(k+2) dt
      = (s/(a+s))^(k+1)/(k+1) <= 1/(k+1),

and

    integral_0^s (t/(a+t))^k log((a+s)/(a+t)) dt <= s.

It also proves the exact unweighted logarithmic integral.

`BoundaryIntegrals.lean` adds the remaining scalar boundary estimate:

    integral_0^1 (s/(a+s) + s(1-s)/(a+s)^2) ds
      <= 1 + log((a+1)/a),

and, with a = eta^2 and 0 < eta <= 1/10, bounds this integral by
`6 * log(1/eta)`.

## Completed determinant-energy and thin-source estimates

`ThinEnergy.lean` now proves the full volume-integral estimate, for m >= 2:

    integral_{|x|^2 + |P|^2 < 1} (-v_eta) det D v_eta
      <= C_m log(1/eta),    0 < eta <= 1/10.

`thinEnergyConstant m` is an explicit positive constant depending only on m.
This is the actual Hessian determinant integrated against Euclidean volume.
`RadialVolume`, `EnergyIntegrability`, `EnergyKernels`, `EnergySlices`,
`EnergyFubini`, and `EnergyBoundary` check the two radial substitutions,
integrability, the transverse sections, Fubini, and the final boundary
integral. No integral bound is supplied as an assumption.

`VariationalTest.lean` defines the actual functional

    J_mu(v) = integral_B (-v) mu - (1/(m+1)) integral_B (-v) det Dv.

An admissible function is smooth near every point of the closed ball,
vanishes on the boundary, and has a nonnegative quaternionic Hessian
quadratic form. The logarithmic profile is proved admissible. Amplitude
scaling of its determinant energy is checked from the actual derivatives:

    E(A v) = A^(m+1) E(v).

`ThinSource` and `ThinVariational` prove the source integral, calculate the
volume of its thin central region, and choose a positive amplitude. They
establish the endpoint power a^((m+1)/m), including a = 0.

`SpatialScaling` and `ScaledVariational` also prove spatial translation and
dilation, including the Jacobian R^(3m), Hessian factor R^(-2), and energy
factor R^m. The resulting theorem is:

```lean
#check KakeyaSharp.thinSource_variational_lower_scaled
```

For m >= 2, R > 0, 0 < epsilon <= R/10, and a >= 0, let B_R(o) be the
Euclidean ball in R^m x R^(2m). If the density mu is continuous on its
closure, nonnegative in the ball, and mu >= a whenever

    |x-o_x| < R/2,    |P-o_P| < epsilon,

the theorem constructs a smooth admissible v with

    J_mu(v) >= c_m R^m epsilon^(2m+2) a^((m+1)/m) log(R/epsilon).

`thinLowerConstant_pos` proves c_m > 0. The center o is arbitrary, so this
includes the manuscript's centers (x_0, 0). All source, scale, and dimension
assumptions appear explicitly in the theorem; no PDE solvability assumption
is used in this lower bound.

`AdmissibleIntegrability` verifies that both integrals defining J_mu are
integrable for every admissible test and continuous source on these balls.
`VariationalValue` defines F_B(mu) as the extended-real supremum over these
actual tests and proves the same lower bound for F_B. The fifth checkpoint
proves that this supremum is finite for every continuous source when m >= 1
and R > 0. The stronger witness theorem above provides a specific admissible
test attaining the stated lower bound.

## Cofactor, Green identity, and first variation

`Moore/Cofactor`, `Moore/Smooth`, and `Moore/NullLagrangian` construct the
actual Hermitian cofactor C(A) of the signed determinant and prove

    Re trace(C(A) H) = d(det)(A)[H]    for Hermitian H,
    Re trace(C(A) A) = m det(A)       for Hermitian A.

The determinant and cofactor are smooth even at singular matrices. The
rank-one identity for the derivative of the cofactor, together with symmetry
of third derivatives, yields the actual quaternionic divergence identity
for C(Du). This works for arbitrary constant real directions and includes
both three and four quaternionic slots. No definiteness or invertibility
hypothesis is used for this identity.

The `Green` modules derive integration by parts using Haar integration and
zero extension, then remove compact-support assumptions on bounded domains.
`ThinDomain` proves convexity, boundedness, and zero boundary volume for our
actual translated balls in the product space. `ThinCofactor` specializes the
Green identity and self-adjointness to the actual three-slot Hessian.

`ThinVariation` proves the following genuine derivatives of the integrals:

    d/dt E(u+t v)|_(t=0) = -(m+1) integral_B v det(Du),
    d/dt J_rho(u+t v)|_(t=0) = integral_B v (det(Du)-rho).

Here B = B_R(o), R > 0, u and v are globally C^3 and vanish on the boundary,
and rho is continuous on the closed ball. The determinant is the same
Pfaffian-defined Moore determinant used throughout the project.
`CompactVariation` proves differentiation under the integral from joint
continuity on a compact parameter interval, including the domination and
integrability conditions. These are not postulated as extra hypotheses.

Consequently an actual solution det(Du) = rho is stationary under every
such zero-boundary C^3 variation. The fifth checkpoint extends this argument
to maximality and finiteness, as described next.

## Concavity, finiteness, and the original admissible class

The additional Moore determinant modules prove positivity on positive
definite matrices, then nonnegativity of the determinant differential and
cofactor on the closed positive cone. Positivity is derived from the same
signed Pfaffian polynomial used throughout the project.

`ThinSecondVariation` proves differentiation along arbitrary parameter
values and the cofactor energy identity. `ThinConcavity` obtains

    d^2/dt^2 J_rho(u+t v)
      = -integral_B <C(D(u+t v)) Dv, Dv> <= 0

whenever the Hessian of u+t v is nonnegative. Here C is the actual Moore
cofactor, Dv is the three-slot quaternionic gradient, and the bracket is
the real quaternionic quadratic form. Boundary-zero C^3 functions suffice.

`LocalExtension` constructs a global C^3 representative of a function
smooth near the compact closed ball. It agrees with the original function
on a neighborhood of each point of that ball. This transfers both the
values and the actual derivatives. `VariationalRepresentation` consequently
proves the supporting inequality for the original admissible class:

    J_rho(v) - J_rho(u) <= integral_B (v-u)(det(Du)-rho).

If an actual admissible u satisfies det(Du) = rho, it therefore attains the
supremum, and

    F_B(rho) = J_rho(u) = m/(m+1) integral_B (-u) rho.

The solution u and its equation are explicit hypotheses of this last
statement. Existence for a general source is not proved.

`ThinMaximum` proves that every admissible f is nonpositive, using the
ordinary maximum principle for the trace of its quaternionic Hessian.
The explicit quadratic

    q(z) = (|z_x-o_x|^2 + |z_P-o_P|^2 - R^2)/6

is admissible and has Dq = I. Given a continuous real source rho, choose
c >= 0 with rho <= c^m. Monotonicity in the source and the supporting
inequality give, for every admissible f,

    J_rho(f) <= J_(c^m)(f) <= J_(c^m)(c q).

The final quantity is finite. The zero test gives the lower bound zero.
Thus `VariationalFinite` proves, without general nonlinear PDE existence,

    0 <= F_B(rho) < infinity,     m >= 1, R > 0.

`VariationalStructure` defines the corresponding real value, proves that
its coercion equals the original supremum, and checks monotonicity,
convexity in the continuous source, and exact homogeneity:

    F_B(a rho) = a^((m+1)/m) F_B(rho),     a >= 0.

It also proves a quantitative comparison under relative source changes:
if 0 <= epsilon <= 1 and (1-epsilon)rho <= sigma <= (1+epsilon)rho, then

    (1-epsilon)^((m+1)/m) F_B(rho) <= F_B(sigma)
      <= (1+epsilon)^((m+1)/m) F_B(rho).

The earlier logarithmic thin-source lower bound is now also stated for
this finite real-valued functional.

## Source continuity and conserved-current calculus

`VariationalContinuity` proves the uniform estimate

    |F_B(rho)-F_B(sigma)| <= a (A+1)^((m+1)/m) F_B(1)

for continuous sources rho, sigma <= A, A >= 0, and
|rho-sigma| <= a <= 1. The sources may vanish; no positive lower bound is
required. It also checks convergence F_B(rho+epsilon) -> F_B(rho) for any
nonnegative scalar epsilon tending to zero. This supplies the value
continuity needed for positive-source regularization.

`Green/QuaternionPairing` and `Green/QuaternionGreen` extend the earlier
real Green identity to every real linear functional L on the quaternions:

    integral_B L((Gu)* C(Dpsi) Gv)
      = L(1) [-integral_B u d(det)(Dpsi)[Dv]].

Here psi is C^3, u is C^1 and zero on the boundary, and v is C^2. The
identity uses the actual cofactor and Frechet derivatives. In particular,
the imaginary components of the integrated pairing vanish.

For three C^2 zero-boundary functions g_0, g_1, g_2, put

    w = sum_beta Gg_beta conjugate(e_beta),    e = (1,i,j),
    Q = sum_beta integral_B (Gg_beta)* C(Dpsi) Gg_beta.

`ThinPairings` checks the exact cancellation

    integral_B w* C(Dpsi) w = Q.

`Calculus/CurrentConservation` differentiates the first-order mass and
momentum conservation equations, including commutation of actual second
derivatives. `ThinCurrent` defines the current on R^3 x ThinSpace m and
derives those equations from quaternionic real-column conservation. It
then proves

    Delta_parameter mu = sum_pq partial_p partial_q S_real(q,p).

The tensor A is C^2 and Hermitian, with mu = A_00 and S its spatial block.
Strong quaternionic divergence zero is proved sufficient for real-column
conservation. `Green/CurrentIntegrals` checks the boundary integrations,
including transfer of two derivatives between zero-boundary functions.

The new integrated comparison is `thinCurrent_energy_le_stress`. Suppose
H = Dpsi is positive definite, C is its Moore cofactor, and

    det H = sum_l rho_l,    xi = sum_l rho_l b_l,
    S = sum_l rho_l b_l b_l*,    rho_l >= 0.

Its explicit differential hypothesis is the linearized conservation law

    d(det)(H)[Dg_beta]
      + sum_(j,alpha) partial_(j,alpha) Re(conjugate(e_alpha) xi_j e_beta) = 0.

The g_beta vanish on the boundary, xi is C^1, and S is continuous.
`ThinCrossPairing` derives integral Re(w*xi) = -Q. `CurrentSquare` proves
the exact pointwise identity, for an actual two-sided inverse V of H,

    Re trace(S H) + w* C w + 2 Re(w*xi)
      = sum_l rho_l (b_l+Vw)* H (b_l+Vw) >= 0.

The inverse is constructed from positivity when assembling the inequality.
Combining the identities gives, with no extra numerical factor,

    Q <= integral_B Re trace(S H).

This comparison has an explicit linearized conservation hypothesis. The
seventh checkpoint derives that hypothesis from an actual solution family
and uses the comparison to control derivatives of the actual supremum.

## Actual parameter derivatives and the conditional Laplacian estimate

`Calculus/SliceDerivatives` proves restriction and commutation formulas for
actual Frechet derivatives. `ThinParameterHessian` defines the spatial slice
u_p(z) = U(p,z), where p has three real coordinates, and proves

    partial_beta det(D_z u_p)
      = d(det)(D_z u_p)[D_z(partial_beta U)].

It also differentiates the zero boundary condition. `ThinSolutionCurrent`
combines this calculation with current conservation to derive the precise
linearized equation used by `thinCurrent_energy_le_stress`. Its theorem
`thinSolution_current_energy` uses g_beta = partial_beta U and does not
assume the linearized equation separately.

`ThinValueDerivative` differentiates the actual finite variational value,
using its previously checked conditional PDE representation and compact
differentiation under the integral. `ThinValueCurvature` proves existence
of the first and second coordinate derivatives and the identities

    partial_beta F_B(mu_p) = -integral_B u_p partial_beta mu,
    partial_beta^2 F_B(mu_p)
      = integral_B (G partial_beta U)* C_u (G partial_beta U)
        - integral_B u_p partial_beta^2 mu.

Here mu(p,z) = A(p,z)_00.re and C_u is the actual Moore cofactor of D_z u_p.
`Green/DoubleDivergence` and `ThinCurrentCurvature` transfer both spatial
derivatives from the stress to u_p. The main new theorem is

```lean
thinValueRealAt_current_laplacian_nonpos
```

Its conclusion is the nonpositivity of the sum of the three actual second
coordinate derivatives of `thinValueRealAt`. Its hypotheses explicitly include:

- A globally C^3 joint function U whose spatial slices are admissible and
  solve det(D_z u_p) = mu_p for every parameter p.
- A globally C^2 Hermitian current A satisfying real-column conservation.
- At the parameter under consideration, strict positivity of D_z u_p in
  the ball, the nonnegative finite rank-one decomposition of the density,
  flux and stress, and zero spatial stress on the ball boundary.

The proof differentiates the actual supremum, derives its linearized
equation, proves the boundary cancellation, and applies the energy bound.
No identity for derivatives of the supremum is postulated. The smooth
solution family itself is still supplied as a hypothesis. The statement
uses globally smooth families. The next section records the checked
distributional formulation and regularization limit added in checkpoint eight.

## Distributional estimate and positive source regularization

`CompactParameterIntegral` proves continuity, differentiation, and joint
C^2 regularity for integration over a fixed relatively compact set. The
dominating bounds are obtained from continuity on compact products.
`ThinValueSmooth` applies this to the conditional PDE representation and
proves that the actual variational value is jointly C^2 in the three
parameters whenever the given solution and source families have this
regularity.

`Green/DistributionalLaplacian` identifies the coordinate sum with mathlib's
usual Euclidean Laplacian. It proves integration by parts against compact
test functions. The predicate `WeakSuperharmonicOn Omega F` requires local
integrability of F on Omega and, for every smooth nonnegative compactly
supported test phi with support in Omega, integrability and the inequality

    integral F(p) Delta phi(p) dp <= 0.

`thinValueRealAt_current_weakSuperharmonic` proves this statement from the
checked smooth-family current inequality. `Green/WeakSuperharmonicLimit`
then proves closure under pointwise convergence with a uniform bound on
each compact subset of an open Omega. Both local integrability of the limit
and the convergence of the test integrals are proved.

`ThinValueWeakLimit` applies this to the actual values F_B(rho+epsilon).
Continuity of the source on compact parameter/spatial products, source
monotonicity, and the earlier value-continuity theorem supply every bound
and the pointwise limit. The limiting source needs no positive lower bound.

`ThinCurrentRegularization` constructs the actual current

    A_epsilon = A + epsilon e_0 e_0*,

where e_0 is the vector with first coordinate one and all others zero. It
checks that the density becomes mu+epsilon, the flux and spatial stress
are unchanged, and Hermitian symmetry and real-column conservation are
preserved. The positive rank-one decomposition gains one weight epsilon
with zero spatial direction. Strict positivity of the regularized density
is also checked.

The combined theorem is

```lean
thinValueRealAt_current_weakSuperharmonic_of_regularized_solutions
```

It proves the distributional inequality for the unregularized actual value.
The Dirichlet hypotheses require globally C^3 admissible solution families
for a sequence of positive epsilon tending to zero, with strictly positive
spatial Hessians on Omega. Those families and the original conserved
positive current and its zero boundary stress remain explicit hypotheses.
No nonlinear existence theorem is included. The ninth checkpoint below
removes the global smoothness and global equation requirements.

## Local parameter domains

The ninth checkpoint proves the stronger local theorem

```lean
thinValueRealAt_current_weakSuperharmonic_of_local_regularized_solutions
```

Let Omega be any open subset of the three-dimensional parameter space,
and let B be the fixed spatial ball. The conclusion is

    integral F_B(currentDensity A(p, .)) Laplacian(phi)(p) <= 0

for every nonnegative smooth compactly supported phi with support in Omega.
Local integrability of the value and integrability of every test product are
part of the checked conclusion. The source can vanish.

The explicit hypotheses are now local:

- At every parameter in Omega, A is jointly C^2 near every point of the
  closed spatial ball. Hermitian symmetry and real-column conservation
  are required only on Omega x B.
- For positive epsilon_n tending to zero, the supplied solutions U_n are
  jointly C^3 near those same points. Their spatial slices are admissible,
  solve det H(U_n) = currentDensity(A) + epsilon_n in B, and have strictly
  positive Hessians there. These conditions are required only on Omega.
- The current has the displayed finite nonnegative rank-one decomposition
  in Omega x B, and its spatial stress vanishes on the boundary of B.

No smoothness or equation is required at parameter points outside Omega.
In particular, the theorem can be used on a region excluding Y = 0,
provided the packet and Dirichlet hypotheses are subsequently verified.

The proof constructs global smooth extensions near a compact spatial slice,
finds one common parameter neighborhood by compactness, and proves that
these extensions preserve the local current equations, spatial Hessians,
admissibility, and actual variational value. Differentiation, the current
energy inequality, and stress transfer are localized to that neighborhood.
A compact extension of each test function calculation then gives the usual
distributional Laplacian inequality on Omega. The source regularization
limit uses convergence and source continuity only inside Omega and over
the closed spatial ball.

The main local theorem is in `ThinCurrentWeakOn.lean`; the local smooth
transfer is in `ThinValueSmoothOn.lean`. The analytic Dirichlet existence is still to be supplied. The concrete
packet current and its connection to this theorem are now proved below.

## Packet construction and conservation

The explicit packet is defined on the actual parameter and spatial
coordinates: s = |Y|, tau = t-1, alpha + k beta = P/Y, the minimizing
center c, the residual d, the phase Phi, the quaternionic column B, and

    rawPacket = f0 chi(Phi/h) B B*,   f0 = (s^2 ((r+s)^2+tau^2))^(-m/2).

The mass-normalizing scalar has not yet been included. The construction
has nineteen modules in `KakeyaSharp/Packet`; ten are new in this checkpoint.

The exact quadratic minimization, uniqueness, completed square, scalar
transport identities, smoothness away from Y = 0, Hermitian symmetry,
and density/flux/stress block identities were checked in checkpoint ten.
This checkpoint completes the derivative identification and conservation.

`CoordinateDerivative.lean` differentiates the physical radius and the
real and imaginary parts of P/Y, including changes in Y with P fixed.
`PhysicalGradient.lean` identifies the algebraic `phaseGradient` with the
actual Frechet derivatives of `physicalPhase` in all coordinate directions.
It proves the actual tangency identity B* G Phi = 0.

`ColumnDerivative.lean` differentiates the actual physical column.
`ColumnJet.lean` derives all parameter and spatial partial derivatives,
the spatial divergence of each column entry, and the cancellation of
all acceleration terms. These hold in every orientation of Y, without
a rotation-covariance assumption. `WeightDerivative.lean` proves that
the prefactor derivatives cancel the column divergence.

`RankOneDerivative.lean` gives the actual Frechet product rule for a
scalar multiple of an outer product. `Conservation.lean` combines that
rule with tangency and the cutoff theorem to prove, for r > 0 and Y != 0,

    sum_{i=0}^m sum_{a=0}^2 star(e_a) partial_{ia} rawPacket_{ij} = 0
    for every column j.

The theorem is `rawPacket_strongDivergence`; its hypotheses are only
r > 0, a C1 cutoff, and |Y| > 0. Strong conservation is a conclusion,
not an assumed property. `rawPacket_realColumnConservationOn` derives
the real column equations on the entire domain |Y| > 0.

## Packet support and scalar transfer

`Support.lean` proves quantitative support estimates from the actual
minimized phase. If Phi <= L, then

    sum_j |x_j-a_j-tau v_j|^2 <= 2 L (tau^2/r+r+s),
    sum_j |P_j-Y v_j|^2 <= L (2 s^2/r+3s).

It also proves an explicit upper bound on the squared spatial norm.
For r = delta^2, h = delta^4, a = delta^2 b, a cutoff vanishing above M,
0 < delta <= 1, M >= 0, |tau|^2 <= 16 and s <= 4, the bound is

    |x|^2+|P|^2 <= 4 delta^4 A + 96 V + 172 M delta^2,

on nonzero packet support, where sum_j b_j^2 <= A and sum_j v_j^2 <= V.
The underlying uniform estimate is `supportBound_uniform`; the packet
vanishes wherever the supplied support bound is smaller than the
squared distance from the spatial origin. This supplies exact boundary
vanishing on any larger fixed spatial ball.

`Family.lean` constructs arbitrary finite real weighted sums of packets.
Smoothness, Hermitian symmetry, and full conservation are proved. For
nonnegative coefficients and cutoff it verifies the nonnegative density
and the exact rank-one density/flux/stress decomposition, including zero
coefficients and the empty family. It also proves boundary vanishing
from the explicit support bound for each constituent packet.

`Transfer.lean` applies the local weak scalar-transfer theorem to this
concrete family. Its main theorem is

    packetFamily_weakSuperharmonic_of_regularized_solutions.

The output is distributional superharmonicity of the actual variational
value of the packet source on the supplied open parameter domain.
Conservation, local current regularity, Hermitian symmetry, positive
block decomposition, and boundary vanishing are all derived from the
packet formulas and numeric support hypotheses. The remaining analytic
assumption is a family of regularized admissible Dirichlet solutions,
with joint local C3 parameter/spatial regularity and strictly positive
Hessians. Existence of these solution families has not been proved here.

## Dirichlet existence and unconditional packet transfer

The twelfth checkpoint completes the previously unfinished Dirichlet
adapter and connects the upstream nonlinear existence and smooth-family
proofs to the actual three-coordinate balls and packet sources.

`Dirichlet/Coordinates` proves that the fourth quaternionic coordinates
can be separated from the three physical coordinates. The signed Moore
determinant agrees definitionally with the imported determinant.
`Dirichlet/Ball` checks the ball-times-torus geometry, including the
strictly positive defining-function Hessian and regular boundary.
`Dirichlet/Existence` applies the proved nonlinear periodic solver.
`Dirichlet/Translation` uses uniqueness to prove invariance under every
translation in the fourth coordinates. `Dirichlet/Descent` then identifies
the actual spatial Hessian, including at the boundary, after descent.

`Dirichlet/Solution` proves, for every m >= 1, R > 0, and center o:

```lean
#check KakeyaSharp.Dirichlet.exists_thinDirichletSolution
#check KakeyaSharp.Dirichlet.exists_thinVariational_maximizer
```

For a globally smooth density positive on the closed ball, there is a
C4 admissible solution whose actual three-slot Hessian is strictly positive
and has determinant equal to the density on the whole closed ball. The
solution attains the original variational supremum, and

    F_B(rho) = m/(m+1) integral_B (-u) rho.

No solution or nonlinear existence principle is a hypothesis of these
existence statements.

`Dirichlet/Data` and `Dirichlet/Family` apply the upstream theorem for
smooth parameter families. The latter produces actual spatial solutions
and joint smooth local representatives near every point of the closed
ball. Their agreement is on the closed physical domain; no unsupported
claim about arbitrary extensions outside that domain is made.
`Dirichlet/LocalFamily` glues these representatives on a compact parameter
neighborhood and proves equality of actual spatial Hessians on the closed
ball, using equality of two-jets on a dense interior.

`Packet/Dirichlet` constructs solutions for the actual source
`currentDensity(packetFamily) + epsilon`, for every epsilon > 0, on any
open parameter domain avoiding Y = 0. Smoothness of the cutoff,
nonnegative weights, and nonnegative cutoff values imply the source
hypotheses. Joint parameter regularity is a conclusion of the construction.

The new main theorem is

```lean
#check KakeyaSharp.Packet.packetFamily_weakSuperharmonic
```

For m >= 1, r,h,R > 0, any finite weighted packet family with nonnegative
weights, a smooth nonnegative cutoff vanishing above M, and an open
parameter domain Omega on which Y != 0 and each explicit packet support
bound is strictly less than R^2, it proves

    integral F_B(currentDensity(A(p,.))) Laplacian(phi)(p) dp <= 0

for every smooth nonnegative compactly supported test phi in Omega.
Local integrability and integrability of the displayed test product are
included. There is no supplied solution family, PDE existence assumption,
or parameter-regularity assumption on a solution. The proof constructs
positive regularized solutions, glues their boundary representatives,
applies the checked local current calculation, and passes to the limit
with epsilon_n = 1/(n+1).

This is a scalar-transfer theorem for the unnormalized explicit packets.
It is not yet the weighted tube estimate or the maximal theorem.

## Exact mass and the normalized Kakeya family

The thirteenth checkpoint uses mathlib's proved linear change of variables
to complete the normalization; it adds no PDE assumptions.

`Packet/Coordinates` gives volume-preserving coordinates between the
physical product space and the ordinary real coordinates indexed by
`Fin 3 × Fin m`. `Packet/Affine` constructs the explicit affine map taking
the actual physical phase divided by h to the sum of the 3m coordinate
squares. Its linear part is a block diagonal matrix. The three-by-three
determinant, the full determinant, and cancellation with the original
packet prefactor are all proved, for every orientation of nonzero Y.

Write

    Z_m(chi) = integral_(R^(3m)) chi(|u|^2) du.

`Packet/Mass` proves, for r,h > 0 and Y != 0,

    integral raw_packet_density = (h^(3/2)/sqrt(r))^m Z_m(chi).

The Lean expression uses `(sqrt(h)^3/sqrt(r))^m`. The mass is independent
of the intercept, direction, time, and Y. For a continuous cutoff vanishing
above a finite threshold, integrability is proved separately. Nonnegativity
and chi(0) > 0 imply Z_m(chi) > 0, so the normalizer is nonzero.

`Packet/Normalized` constructs mass-one packets and weighted sums whose
integrated density equals the sum of their weights. These normalized sums
inherit the already proved weak superharmonicity theorem. It also fixes an
actual smooth cutoff `standardCutoff`, equal to one for t <= 1/2 and zero
for t >= 1, using mathlib's `Real.smoothTransition`.

`Packet/KakeyaFamily` sets r = delta^2, h = delta^4 and a_l = delta^2 b_l,
and assigns mass delta^m times the weight lambda_l. It proves

    integral mu_p = delta^m sum_l lambda_l.

For 0 < delta <= 1, |b_l|^2 <= A, |v_l|^2 <= V and A >= 0, every packet
is supported in one spatial ball of radius

    R = sqrt(max(4 A + 96 V + 172, 0)) + 1

throughout the fixed open parameter domain -3 < p_0 < 5, 0 < |Y| < 4.
This radius is independent of delta, the number of packets, and their
weights. `kakeyaPacketFamily_weakSuperharmonic` therefore has no supplied
solution-family hypothesis and no pointwise support-bound hypothesis.
Nonnegative weights are required for this transfer theorem; direction
separation is not required at this stage.

`VariationalParameterContinuity` proves that a jointly continuous source
on an open parameter domain times the closed spatial ball gives a
continuous variational value, even when the source vanishes. Its proof
uses compact uniform continuity and the previously proved Lipschitz
estimate in the source. Applied to the actual scaled packets, this gives
`kakeyaPacketFamily_value_continuous` and the accompanying nonnegativity
theorem. These are the regularity properties needed for scalar propagation.

## Weighted trace and the input logarithmic barrier

The fourteenth checkpoint proves, for every m >= 1, R > 0 and H >= 0,

    integral_B (-u)^(m+1) det(D phi)
      <= K_m H^m integral_B (-u) det(Du),
    K_m = 3^(m+1) (m+1).

Here u belongs to the original admissible class: it is C3 near the closed
ball, is zero on the boundary, and has positive semidefinite quaternionic
Hessian. The barrier phi is C3 near the closed ball, has positive
semidefinite Hessian in the ball, and satisfies -H <= phi <= 0.
**No boundary condition is imposed on phi.** Singular Hessians and H = 0
are included. The main theorem is `ThinAdmissibleAt.trace_bound`.

`Trace/Comparison` differentiates a smoothly weighted determinant integral
along the segment between two functions. The existing first cofactor and
Green identity prove the required sign. `Trace/Sublevel` applies a fixed
smooth transition to get a comparison of determinant masses at levels t
and 3t. `Trace/LayerCake` integrates this comparison using mathlib's proved
layer-cake formula, including the real/extended-real and density-measure
conversions. `Trace/Estimate` transfers it to the original local admissible
class and includes zero height by a one-sided limit. The proof is detailed
in [TRACE_METHOD.md](TRACE_METHOD.md).

`Trace/Weighted` then proves

    F_B(mu) <= C_m H integral_B b^((m+1)/m) det(D phi),
    C_m = m/(m+1) * K_m^(1/m),

when mu is continuous on the closed ball, b >= 0 in the ball,
mu <= b det(D phi), and the displayed weighted integrand is integrable.
The weight can be discontinuous. The proof uses scaled Young's inequality,
the trace bound, and the actual supremum over admissible functions.
There is no supplied PDE solution or trace estimate in this theorem.
Its name is `thinValueRealAt_weighted_bound`.

`Trace/LogBarrier` derives the actual Hessian of log(h+rho), its positive
lower bound, and its determinant when D rho = kappa I and
|G rho|^2 = kappa rho. `Packet/InputBarrier` verifies these identities for

    alpha_j = a P_(j,0) + b P_(j,1),
    beta_j  = a P_(j,1) - b P_(j,0),       a^2+b^2 = 1,
    rho(x,P) = sum_j ((x_j+alpha_j)^2 + 2 beta_j^2).

It proves D rho = 8 I, |G rho|^2 = 8 rho, rho >= 0 and
rho <= 2 (|x|^2+|P|^2), directly from Frechet derivatives. Thus

    phi_h = log(h+rho) - log(h+2R^2),
    det(D phi_h) = 8^m h/(h+rho)^(m+1).

The barrier is globally smooth and positive semidefinite, and its values
on the closed ball lie between -log((h+2R^2)/h) and zero. The coordinates
are identified with the actual packet ratios at |Y| = 1.
For h = delta^4 and 0 < delta <= 1, its height is at most

    (4 + log(1+2R^2)/log 2) log(2/delta).

`inputBarrier_value_le_log` applies the weighted variational theorem with
this explicit kernel. Its source domination and weighted integrability
hypotheses are still explicit; it does not yet prove the complete packet
input estimate or the weighted tube estimate.

## Completed normalized input estimate and smooth propagation

The fifteenth checkpoint adds eight packet modules and two propagation
modules. For m >= 1, 0 < delta <= 1, R > 0, unscaled intercepts satisfying
sum_j a_lj^2 <= A, delta-separated directions v_l and nonnegative weights,
`kakeyaPacketFamily_input_estimate` proves

    F_B(input packet density)
      <= C_(m,A,R) log(2/delta) delta^m sum_l weights_l^((m+1)/m).

The input has time p_0 = 0 and p_1^2+p_2^2 = 1. The actual packet family
uses intercepts delta^2 a_l. The constant is explicit and positive;
it is independent of delta, the number of packets, weights, directions
and transverse orientation. No density domination or integral bound is
supplied by the caller.

`Packet/InputSupport` proves directional distance at most sqrt(5) delta
and normal quadratic form at most (3A+11) delta^4 on the cutoff support.
`InputDomination` combines these with exact packet normalization.
`InputCoordinates` proves the volume-preserving change to directional
and normal coordinates. `NormalKernel` and `InputIntegration` prove
whole-space integrability and the scale-independent normal integral.
`DirectionPacking` and `DirectionIntegral` bound cap overlap by 8^m
and integrate the critical power of the actual directional weight.
`InputEstimate` combines these with the previously checked weighted trace.

`Propagation/OuterRegion` localizes the OpenAI fixed-region comparison in
time. `Propagation/SingleLog` proves a fixed positive constant C such that

    integral_(1..2) integral_(0..2pi) f(t, rho exp(i phi))
      <= C (1+abs(log rho)) f(0, exp(i theta)),  0 < rho < 1.

Here f is smooth, nonnegative and superharmonic only on
-5pi-1 < t < 5pi+1 and rho/2 < |Y| < 4. The input radius is fixed at one.
The proof reuses the underlying upstream radial and mixing theorems;
it does not apply the cubic-log final cylinder theorem.

See `TRACE_METHOD.md` for the mathematical argument and exact hypotheses.

## Weak propagation and localized output: checkpoint 0.16.0

`Propagation/Mollifier` proves the Laplacian identity for convolution with
a smooth compact kernel and tests weak superharmonicity against its
translates. `LocalApproximation` constructs smooth approximations which
are nonnegative, superharmonic and uniformly bounded on any compact
interior set. `WeakSingleLog` passes both cylinder integrals to the limit.
The resulting single-log estimate applies to continuous weakly
superharmonic functions on an open neighborhood of the closed cylinder.

`Packet/PropagationDomain` gives the actual packet family the larger domain

    (p_0-1)^2 < 576,    0 < |Y| < 5,

with spatial radius sqrt(max(4A+2354V+2458,0))+1, independent of delta.
`Packet/Propagation` combines weak propagation with the checked input
estimate. At the exact output radius h = delta^4, it proves

    integral_(1..2) integral_(0..2pi) F(t, delta^4 exp(i theta))
      <= C_(m,A,V) log(2/delta)^2 delta^m sum_l weights_l^((m+1)/m).

This is the actual variational value of the normalized packet density.
No smoothing, solution-family or PDE-solvability hypothesis is supplied.

`Dirichlet/Comparison` adapts the pinned OpenAI comparison theorem to
translated three-coordinate balls. `VariationalLocalization` proves

    sum_j F_(B_j)(mu) <= F_B(mu)

for a finite collection of disjoint open balls whose closures lie inside
B, and any smooth source nonnegative on the closed outer ball. Positive
sources use the checked Dirichlet solutions and comparison; the proved
source-continuity theorem passes to sources which can vanish. The
logarithmic thin-source lower bounds can therefore be summed.

`Packet/OutputDensity` proves that the fixed cutoff is exactly one when
|v_l| <= 1/4, |P| <= h/4, and the squared physical axial error is at most
r*h/16, with r=delta^2 and h=delta^4. For |p_0-1| <= r, each selected
packet then contributes at least

    c_m delta^(-10m) weights_l,
    c_m = 5^(-m/2) / cutoffMass(m, standardCutoff) > 0.

`Packet/OutputLocalization` applies this to disjoint balls centered at
(x_j,0), with radii R_j <= delta^3/4 and transverse thicknesses
epsilon_j <= min(R_j/10, delta^4/4). The selected packet axes are within
delta^3/8 of x_j. It derives the source lower bound throughout each thin
core and proves the resulting sum of logarithmic variational lower bounds.
`Packet/OutputScaling` checks that radii R_j=r0*delta^3 and
epsilon_j=epsilon0*delta^4 give precisely delta^(m-2) times the critical
power of the selected weight sum, multiplied by log(r0/(epsilon0*delta)).
At checkpoint 0.16.0, this part required m >= 2. Checkpoint 0.19.0 extends the thin-source test and scale arithmetic to m >= 1.

At checkpoint 0.16.0 the ball collection and its relationship to the tube
overlap integral were still hypotheses. The next checkpoint constructs them.

## Normalized weighted tubes: checkpoint 0.17.0

Let m >= 2, q=(m+1)/m, 0<delta<1, A>=0, and let a_l,v_l lie in R^m.
Suppose |a_l|^2<=A, |v_l|<=1/4, and the slopes v_l are delta-separated.
For arbitrary nonnegative weights lambda_l, define

    M(t,x) = sum_l lambda_l 1_{|x-a_l-t v_l| <= 2 delta},  0 <= t <= 1.

`Packet.exists_enlargedGraphTube_constant` proves

    integral_(0..1) integral_(R^m) M(t,x)^q dx dt
      <= C_(m,A) log(2/delta) delta^m sum_l lambda_l^q.

The positive constant is uniform in delta, the number of tubes and their
weights. This theorem has no assumed packet estimate, PDE solvability,
trace inequality, geometric cover or integral bound.

For the initial radius delta/64, `TubeSlices` and `CoverIntegral` construct
a measurable finite-net majorant and prove spatial integrability.
`OutputGeometry` scales a delta/32-separated net to centers
(delta^2 b_j,0), with ball radius delta^3/100 and transverse thickness
delta^4/1000. The balls are disjoint, lie in the fixed outer ball, and
the selected axes satisfy the checked output-density hypotheses.
`OutputSlice` combines the cover and localization to prove

    c_m log(2/delta) integral M(t,x)^q dx
      <= delta^2 F(1+delta^2 t, delta^4 exp(i theta)).

Here M in the slice inequality uses the initial radius delta/64.
`TubeSliceIntegral` proves measurability and uniform integrability in time.
`Propagation/ContinuousTrace` proves continuity of angular integrals of
the actual continuous value, with no smoothness assumption.
`NormalizedTubes` integrates the displayed inequality, changes time
variables exactly, restricts the nonnegative propagation integral to
[1,1+delta^2], and cancels the positive logarithm.

`GraphCover` and `EnlargedGraphTubes` use a fixed finite 1/64-net of the
radius-two ball. Translating each intercept by delta times a net point
covers a radius-2-delta graph tube by finitely many radius-delta/64 tubes.
Finite Holder, both integrals and the enlarged intercept bound 2A+8
are checked. This preserves the single logarithm and delta separation.

At checkpoint 0.17.0 these graph tubes still had a fixed time interval,
a small slope chart and bounded intercepts. The next checkpoint removes
these restrictions and identifies the actual Euclidean tubes.

## Arbitrary Euclidean tubes: checkpoint 0.18.0

`Packet/SpatialGroups`, `SpatialLocalization`, and `GlobalGraphTubes`
remove the bounded-intercept hypothesis. A finite 2-separated net of the
intercepts assigns each tube to a center within distance 2. Only at most
8^m groups can contribute to the graph overlap at any point. Finite Holder,
translation invariance and the exact partition of the coefficient powers
give a constant depending only on m, regardless of the net's cardinality.

`GraphEndpoint` includes delta=1 using a coarse packing estimate.
`GraphTimeIntervals` handles translation in time and any fixed finite
integer-length interval. `BroadGraphTubes` enlarges the graph radius to
8 delta by a fixed finite cover; the slope separation stays delta.

`GraphCoordinates` splits R^(m+1) into a real time coordinate and R^m,
with an exact proof that Lebesgue volume is preserved. `GraphSlopes`
proves that unit vectors within 1/16 of the north pole have slopes of norm
at most 1/4, and delta-separated directions give delta/2-separated slopes.
`GraphTubeGeometry` includes actual radius-2-delta Euclidean tubes inside
graph tubes with transverse error at most 5 delta/2. If the longitudinal
center lies in [-2,2], all times lie in [-5,5]. This includes the end caps.

`GraphWindow` proves product integrability and Fubini on finite intervals.
`ChartTubes` applies the radius-8-eta graph estimate with eta=delta/2,
so its graph radius is 4 delta. The checked logarithmic comparison is
log(2/(delta/2)) <= 2 log(2/delta). This yields the Euclidean tube estimate
inside one direction chart with bounded longitudinal centers and arbitrary
transverse centers.

`TubeGroups`, `TubeSpatialLocalization`, and `GlobalChartTubes` remove
the last center restriction by a spatial net in the actual ambient space.
Each translated group has all its centers in the radius-two ball, and at
most 8^(m+1) groups contribute at any point. The coefficient-power sums
partition exactly, so the total number of occupied regions never enters
the constant.

`DirectionCharts` constructs finitely many orthogonal reflections from a
fixed sphere net. Each sends its central direction to the north pole and
preserves separation, Euclidean tubes and Lebesgue integration.
`TubeReindex` restricts each direction class to its own finite index set,
so no unassigned directions need satisfy that class's cap condition.
`AllDirectionTubes` sums the rotated class estimates with a factor depending
only on the number of charts, hence only on dimension. `SharpTheorem`
identifies q=(m+1)/m with n/(n-1), proves `SharpTubeBound n` for n>=3,
and applies the full maximal transfer.

## The planar endpoint: checkpoint 0.19.0

The earlier m>=2 restriction came from bounding the radial Jacobian by r
in the boundary integral. `EnergyBoundaryAllDimensions` instead uses,
for a>0 and 0<=r<=1,

    boundaryKernel(a,1-r^2) <= 1 + 1/(a+1-r).

Since r^(m-1)<=1 for every m>=1, radial integration gives

    integral_(|x|<1) boundaryKernel(eta^2,1-|x|^2)
      <= 6 m vol(B_1^m) log(1/eta).

This enlarges only a dimension-dependent constant in the energy bound.
The thin-source variational estimate and its scaled/localized versions
therefore hold for m>=1.

The second correction keeps the exponent m-2 as a real number in
`output_delta_power_real` and `output_lower_scaling_real`. In m=1 the
localized output factor is delta^(-1). Multiplication by the delta^2
time-change factor gives delta^m exactly, as in every higher dimension.
The former natural-exponent identities remain available for m>=2.

The graph, Euclidean tube and maximal assembly now accepts m>=1, giving
`sharpTubeBound_of_two_le` and `sharpMaximalBound_of_two_le`. The former
n>=3 theorem names remain available. The audit also checks explicit
applications of both new theorems at n=2.

## Remaining proof work and efficient reuse

The remaining sharpness task is to formalize a matching logarithmic lower
bound. The existing manuscript uses the radial test

    f_delta(x) = |x|^(-1) 1_{2 delta < |x| < 1/2}.

Its n-th power integral has size log(1/delta), while every centered radial
tube has average at least a dimension constant times log(1/delta). These
lower-bound assertions are not yet Lean theorems in this project.
The upper bound, including n=2, is now checked.

The finite spatial partition here is a weighted counterpart of the
localization in OpenAI's `Kakeya/Log/VolumeLocalization.lean` (inspected at
the pinned commit). Its result concerns unweighted tube-union volumes;
the present weighted moment and coefficient identities were proved locally.
`CapReduction.lean`, `Log/Overlap.lean`, and `Log/TubeBound.lean` were also
inspected. Their restriction-to-tube route is not required for this direct
packet-to-tube proof. No new upstream source file was imported or modified.

The most useful upstream entry points are pinned at commit
`4eaee87548250b2682affda7d05d947c05554bae`:

| Purpose | Existing checked source | Status here |
| --- | --- | --- |
| Nonlinear Dirichlet existence | [Boundary/Continuity/Existence.lean](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Analysis/PDE/Dirichlet/Boundary/Continuity/Existence.lean) | Applied to the actual ball-times-torus domain |
| Joint smooth boundary representatives | [General/Family/Regularity.lean](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Analysis/Fourier/WavePackets/General/Family/Regularity.lean) | Applied and descended to the packet problem |
| Gluing compatible local representatives | [Extension/Local.lean](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Analysis/Calculus/SmoothExtension/Periodic/Extension/Local.lean) | Applied on compact parameter neighborhoods |
| Radial comparison with a single logarithm | [RadialComparison.lean](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Analysis/PDE/Concentration/RadialComparison.lean) | Applied to the actual weak packet value through positive smoothing |
| Uniform control in a fixed region | [BallChain.lean](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Analysis/PDE/Concentration/BallChain.lean) | Used through the localized fixed-region mixing theorem |
| Positive smoothing calculus | [MollificationDerivatives.lean](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Analysis/PDE/Schauder/Calculus/Schauder/MollificationDerivatives.lean) | Used to preserve the weak Laplacian inequality under convolution |
| Nonlinear comparison | [ContinuousComparison.lean](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Analysis/PDE/Dirichlet/ContinuousComparison.lean) | Adapted to prove finite-ball localization |
| Existing final cylinder estimate | [Cylinder/Estimate.lean](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Analysis/PDE/Concentration/Cylinder/Estimate.lean) | Cubic logarithm; not a substitute for the target single-log estimate |

The Ma--Zhu paper [arXiv:2611.03214](https://arxiv.org/abs/2611.03214)
is a mathematical reference for the Dirichlet input. It is not introduced
as a Lean axiom. The formal proof now uses the proved OpenAI solver.
`UPSTREAM_DIRICHLET.json` pins 1,682 unmodified upstream source files by
Git blob hash; every included file has been compared with that manifest.
Keep the existing mathlib/Lean pins and cached builds. Import the needed
source modules instead of rebuilding the entire OpenAI repository.

## Reproduce

From this directory, with elan/Lean available:

```sh
lake exe cache get
python3 scripts/build_checked.py build KakeyaSharp
lake env lean Audit.lean > AUDIT.txt
python3 scripts/audit_sources.py
```

The project target and all 207 local `KakeyaSharp` modules compile successfully.
The 587 axiom reports are recorded in `AUDIT.txt`, including the upstream nonlinear solver,
the family theorem, exact packet normalization, scalar transfer for the scaled family,
weighted trace, the normalized weighted input bound, weak single-log propagation,
finite-ball localization, actual localized output, the normalized weighted
tube theorem, radius enlargement, arbitrary Euclidean tube assembly,
and unconditional sharp maximal upper bound for n>=2, including explicit planar instances. The checked results depend
only on `propext`, `Classical.choice`, and `Quot.sound`. There are no proof
placeholders or additional axioms in the project sources.

## Provenance

Elementary Kakeya infrastructure, quaternionic algebra, and selected Moore
determinant proofs were adapted from `openai/math`, with namespaces and
imports changed and unrelated results removed.
`SOURCES.json` records source URLs and blob hashes; `LICENSE-OpenAI` contains
the upstream Apache-2.0 license. The new quantitative transfer is in
`SharpTransfer.lean`. The new test-function, Hessian, positivity, determinant
bound and scalar integral proofs are in the `Thin*`, `HessianCalculus`,
`QuaternionPositive`, `Moore/ScalarOuter`, `Moore/RankTwoBound`,
`RadialIntegrals`, and `BoundaryIntegrals` modules. The radial volume,
energy assembly, variational tests and optimization, spatial scaling, and
variational supremum modules are new proofs using the pinned mathlib.
The fourth checkpoint adds selected upstream cofactor, third-derivative,
and integration-by-parts proofs. The ball-boundary geometry, integrated
energy cancellation, compact differentiation lemma, and first variation
of the actual thin functional are new local proofs. The fifth checkpoint
adapts upstream positivity and maximum-principle proofs, and adds new local
proofs of second variation, concavity, compact extension, the supporting
inequality, conditional PDE representation, the quadratic barrier,
finiteness, and source comparison, convexity, and homogeneity.
The sixth checkpoint adds new local proofs of continuity and positive-source
regularization, full quaternionic Green pairings, three-parameter
cancellation, actual current conservation, boundary derivative transfer,
completion of squares, and the integrated current energy comparison.
The seventh checkpoint adds local proofs of slice differentiation, parameter
linearization of the determinant equation, the differentiated boundary
condition, first and second derivatives of the actual variational value,
double-divergence boundary transfer, and the conditional nonpositive
coordinate Laplacian for a smooth Dirichlet family.
The eighth checkpoint adds local proofs of joint parameter regularity under
compact integration, the usual Laplacian and its test-function identity,
local integrability and stability of distributional superharmonicity,
regularization of the actual current and rank-one decomposition, and the
weak inequality for the unregularized value conditional on positive-source
Dirichlet families.

The ninth checkpoint adds new local proofs of conservation, determinant and
boundary differentiation, first and second value variations, current energy
and stress transfer, distributional superharmonicity on open sets, compact
smooth extension for normed-space-valued functions, and the local source
regularization limit. It removes the global smoothness and global equation
assumptions from the final conditional scalar-transfer theorem.

The tenth checkpoint adds new local proofs for the packet minimizer and
completed phase, finite-dimensional deviation bounds, quaternionic identities
at every orientation, actual curve derivatives of the minimizer and phase,
the scalar density prefactor, the explicit physical-coordinate packet and
its local smoothness and block identities, and preservation of actual
conservation under a tangent scalar cutoff. No new upstream files are ported.

The mathematical argument being formalized is the working manuscript
`Kakeya_sharp_maximal_all_dimensions_2026-11-12.tex`. The full argument
remains subject to independent verification.

The eleventh checkpoint adds new local proofs of actual physical-coordinate
phase and column derivatives, full packet conservation with cutoff,
quantitative spatial support, finite weighted packet families, and their
conditional scalar transfer. No additional upstream proof files were
ported in this checkpoint.

The twelfth checkpoint completes and integrates the five previously staged
Dirichlet adapters, adds actual variational attainment, packages the fixed
ball for the upstream smooth-family theorem, descends the parameter
representatives, glues them with preservation of actual boundary Hessians,
and constructs regularized solutions for the explicit packets. It removes
the Dirichlet-family hypothesis from the packet scalar-transfer conclusion.
The upstream files are included unchanged with the Apache-2.0 license and
exact provenance in `UPSTREAM_DIRICHLET.json`.

The thirteenth checkpoint adds six local modules: `Packet/Coordinates`,
`Packet/Affine`, `Packet/Mass`, `Packet/Normalized`, `Packet/KakeyaFamily`,
and `VariationalParameterContinuity`. These use the existing pinned mathlib
change-of-variables, determinant, compactness, and uniform-continuity
theorems; no additional OpenAI source files were needed.

The fourteenth checkpoint adds seven local modules: `Trace/Comparison`,
`Trace/Sublevel`, `Trace/LayerCake`, `Trace/Estimate`, `Trace/Weighted`,
`Trace/LogBarrier`, and `Packet/InputBarrier`. They reuse the checked first
cofactor, Green identity, local smooth extension, maximum principle, and
mathlib layer cake and Young inequalities. No new upstream source files
are imported or modified. The different dimension constant in the trace
bound preserves exactly the barrier-height power required for the target
logarithmic exponent.

The fifteenth checkpoint adds eight new local packet modules:
`InputSupport`, `InputDomination`, `InputCoordinates`, `NormalKernel`,
`InputIntegration`, `DirectionPacking`, `DirectionIntegral`, and
`InputEstimate`. It adds `Propagation/OuterRegion` and
`Propagation/SingleLog`, adapting the fixed-region assembly from the
pinned OpenAI concentration development while directly importing its
proved radial, averaging and mixing lemmas. No upstream source is changed.
At that checkpoint, the full sharp tube and maximal bounds were still unproved.

The sixteenth checkpoint adds ten local modules: `Propagation/Mollifier`,
`Propagation/LocalApproximation`, `Propagation/WeakSingleLog`,
`Packet/PropagationDomain`, `Packet/Propagation`, `Dirichlet/Comparison`,
`VariationalLocalization`, `Packet/OutputDensity`, `Packet/OutputLocalization`,
and `Packet/OutputScaling`. They reuse the pinned OpenAI convolution and
nonlinear comparison proofs, mathlib dominated convergence, and the existing
actual packet and thin-source theory. All 1,682 vendored upstream files
retain their pinned Git blob hashes. At that checkpoint, the full sharp
tube and maximal estimates were still unproved.

The seventeenth checkpoint adds nine local modules: `Packet/TubeSlices`,
`Packet/CoverIntegral`, `Packet/OutputGeometry`, `Packet/OutputSlice`,
`Packet/TubeSliceIntegral`, `Propagation/ContinuousTrace`,
`Packet/NormalizedTubes`, `Packet/GraphCover`, and `Packet/EnlargedGraphTubes`.
They reuse the existing separated-net theorem, finite Holder inequalities,
parametric integration, and interval substitution in the pinned mathlib.
The weighted graph-tube estimate with one logarithm is now proved, including
radius 2 delta. No additional upstream source is imported or modified.
At that checkpoint, arbitrary-location/direction assembly, n=2 and logarithmic optimality remained.

The eighteenth checkpoint adds eighteen local modules, listed in
`SOURCES.json`. They prove global graph estimates, the endpoint scale,
time intervals, orthogonal direction charts, exact Euclidean tube
containment, product integration, weighted spatial localization, finite
reindexing, and the unconditional sharp tube and maximal upper bounds
for n>=3. All 1,682 vendored OpenAI files remain unmodified.

The nineteenth checkpoint adds `EnergyBoundaryAllDimensions` and extends
nineteen existing theorem modules, together with real-exponent identities
in `Packet/OutputScaling`. It proves the planar endpoint through the same
packet/variational argument. No additional upstream source is needed.
