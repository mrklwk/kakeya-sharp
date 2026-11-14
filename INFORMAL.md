# Mathematical account and formal correspondence

Fix an integer dimension `n >= 2`, and put `m = n-1` and `q = n/(n-1)`.
The goal is a uniform weighted tube estimate with one logarithm, followed
by the actual Kakeya maximal inequality. The proof is of interest to
harmonic analysts studying endpoint maximal estimates and to formalizers
of geometric analysis. The submission makes no assertion of priority
relative to an independently checked literature survey.

The following describes the proof implemented in Lean, including its
changes from the included working manuscript. All analytic inputs used
by the final theorems are proved in the imported source graph. No PDE
existence theorem or tube inequality appears as an extra hypothesis in
either submitted result.

## Variational quantity and logarithmic lower bound

On the unit ball `B` in an auxiliary real space of dimension `3m`, let `D` denote the
three-slot quaternionic Hessian and let `det` be its signed Moore determinant.
For a nonnegative continuous density `mu`, consider the supremum over
admissible zero-boundary functions `u` of

\[
J_\mu(u)=\int_B(-u)\mu-\frac1{m+1}\int_B(-u)\det Du.
\]

Admissibility means $C^3$ regularity near the closed ball, zero boundary values,
and a positive semidefinite quaternionic Hessian. The development proves
finiteness of this supremum and identifies it with the appropriate
Dirichlet solution energy when a smooth positive source is present.

Write a point of that ball as `(x,P)`, where `x` has `m` real coordinates
and `P` has `2m` real coordinates; thus `|x|^2+|P|^2 < 1`.
For a positive regularization parameter `eta`, the explicit test is

\[
v_\eta(x,P)=\log\frac{\eta^2+|P|^2}{\eta^2+1-|x|^2}.
\]

Its actual Hessian is positive semidefinite, its value is zero on
`|x|^2+|P|^2=1`, and its
determinant energy is bounded by a dimensional constant times
`log(1/eta)`. Rescaling and choosing its amplitude give a logarithmic
lower bound for the variational quantity on thin source regions.
The radial estimate in `EnergyBoundaryAllDimensions` is valid for every
`m >= 1`, which includes the planar case. The real-exponent scale
identities retain the negative exponent when `m = 1`.

## Weighted input estimate

The formal proof uses smooth comparison in place of the manuscript's
general mixed-determinant argument. Integrating the cofactor Green identity
along an affine interpolation gives a sublevel mass comparison. Layer cake
then gives a trace estimate for `(-u)^(m+1)` against a barrier determinant.
Young's inequality converts it into a weighted upper bound for `J_mu`
and hence for its supremum.

For the actual normalized packet family, an explicit logarithmic barrier
has determinant `8^m*h/(h+q_0)^(m+1)`, with `h = delta^4` and a specified
quadratic form `q_0`. A volume-preserving change of coordinates and
direction separation control its weighted integral. This yields the input
bound with one logarithm and the required sum of `q`-th powers of weights.
The formulas, constants, and relevant Lean declarations are detailed in
`TRACE_METHOD.md`.

## Propagation, localization, and tube geometry

The packet variational quantity is continuous and weakly superharmonic
in three auxiliary parameters. An annular propagation estimate loses
one logarithm. Mollification and dominated convergence prove the estimate
for the actual weak quantity. Localized variational lower bounds may be
added over finite disjoint balls. At the output, the logarithmic test
recovers one logarithm, leaving one overall in the weighted tube estimate.

Finite covering, time integration, and exact scale calculations turn the
packet estimate into the graph-tube estimate. Spatial localization removes
bounded-center restrictions. Finitely many rotated charts cover all unit
directions and include the end caps of the Euclidean tubes. The large-scale
range is treated separately. The resulting constant depends only on `n`.

The maximal deduction proves tube-average measurability and passes from
finite selections of tube centers to the supremum over all centers.
Direction nets, spherical integration, and duality give the power
`(n-1)/n` on the logarithm. This step uses the actual tube volume.

## Main locations in the source

| Step | Lean source |
| --- | --- |
| Concrete Euclidean operator and target propositions | `KakeyaSharp/Definitions.lean` |
| Logarithmic test and actual determinant energy | `KakeyaSharp/ThinProfile.lean`, `KakeyaSharp/ThinEnergy.lean` |
| Boundary integral including transverse dimension one | `KakeyaSharp/EnergyBoundaryAllDimensions.lean` |
| Weighted trace and barrier argument | Modules and theorem names in `TRACE_METHOD.md` |
| Scale identities including dimension two | `KakeyaSharp/Packet/OutputScaling.lean` |
| All centers and all directions | `KakeyaSharp/AllDirectionTubes.lean` |
| Final unconditional upper bounds | `KakeyaSharp/SharpTheorem.lean` |
| Independent statements and proof bridges | `Challenge.lean`, `Solution.lean` |

## Scope of the evidence

Kernel checking establishes the encoded statements relative to the
permitted foundations and imported definitions. Semantic correspondence
is made reviewable by writing the concrete definitions directly in the
short Challenge module. Palomar Comparator and independent kernel replay
must still run on the exact submitted commit; see `VALIDATION.json`.
The matching lower bounds and geometric volume consequences are written
out in `STATEMENT_AND_OPTIMALITY.md` and `SUMMARY.md`, but are not
formalized here. Independent human review and a novelty assessment are
not represented as completed.
