# Independent review: sharp Kakeya estimates

Task: `kakeya-20261114-formal-and-narrative`.
Status: queued for user launch; no Claude review has yet been received.

Mark Lewko requests two reviews: verify that the actual Lean statements
and proofs establish the intended estimates, and critique the abstract
and narrative summaries for correctness, clarity, and faithful scope.
Do not assume that the desired conclusion is true. Try to find a missing
hypothesis, changed definition, circular assumption, vacuous norm or
measure, incorrect exponent, or misleading description.

## Materials and intended result

The repository root is two directories above this file. Begin with
`Challenge.lean`, `Solution.lean`, `ABSTRACT.md`, `SUMMARY.md`, `CLAIMS.md`,
`VALIDATION.json`, and `formalization.yaml`.

The exact intended maximal theorem is: for every integer $n\ge2$, there
exists $C_n>0$, chosen before $\delta$ and $f$, such that for every
$0<\delta\le1$ and complex-valued $f\in L^n(\mathbb R^n)$,

$$
 \|K_\delta f\|_{L^n(S^{n-1})}
 \le C_n[\log(2/\delta)]^{(n-1)/n}\|f\|_{L^n(\mathbb R^n)}.
$$

Here $K_\delta$ takes the supremum over all centers of the absolute-value
average over the open radius-$\delta$ neighborhood of a unit segment,
using its actual Lebesgue volume. Directions carry the usual nonzero
surface measure. Membership in strong $L^n$ is part of the conclusion.

The second theorem is the weighted overlap inequality at $q=n/(n-1)$:

$$
 \int\left(\sum_j a_j1_{T_{2\delta}(\omega_j,x_j)}\right)^q
 \le C_n\log(2/\delta)\delta^{n-1}\sum_j a_j^q,
$$

for all finite $\delta$-separated unit directions, arbitrary centers and
nonnegative real weights. The radius is exactly $2\delta$ in the Lean
target. The radius-$\delta$ version follows by domination.

Targets: `KakeyaPalomar.sharpMaximalBound` and
`KakeyaPalomar.sharpTubeBound`. `Challenge` imports only mathlib and has
two deliberate proof placeholders. `Solution` must not import it.

## Review A: formal meaning and proof evidence

1. Read the actual declarations. Print their elaborated types and axioms.
   Check canonical Euclidean space, Lebesgue and spherical measures, the
   tube union, actual positive finite denominators, real powers, ENNReal
   conventions, arbitrary centers, dimension two, and the quantifier order.
   For the overlap integral, check integrability so that the totalized
   Bochner integral cannot make the statement vacuous.
2. Independently formulate the intended statement using literal mathlib
   definitions. Inspect `SemanticAudit.lean` and
   `scripts/audit_statement_bindings.py`, but do not treat agreement with
   an existing harness as a substitute for your own semantic assessment.
3. Check that the source bytes, compiled modules, imported dependencies,
   and toolchain correspond. The prior full module-port build was in Lean
   4.34.1 with mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
   The root configuration now targets Lean 4.35.0 and mathlib
   `56a005855ea17e0b0958f73ec801ae140b0a1679`; that newer build has NOT run.
   Do not relabel an older compiled artifact as a target-toolchain result.
4. Inspect the proof dependency route, particularly:
   - `ThinProfile.lean`, `ThinHessian.lean`, `ThinDeterminant.lean`,
     `ThinEnergy.lean`, and `EnergyBoundaryAllDimensions.lean`;
   - the weighted trace argument and declarations identified in
     `TRACE_METHOD.md`;
   - `Propagation/WeakSingleLog.lean`, `Packet/OutputScaling.lean`,
     `AllDirectionTubes.lean`, and `SharpTheorem.lean`.
   These paths are under `KakeyaSharp/`. Trace their actual dependencies.
   Check each logarithmic loss/gain, uniform constants, the transverse
   dimension-one case, the negative scale exponent in that case, source
   regularization, weak propagation, and removal of bounded-center and
   restricted-direction conditions.
5. Check that the only final axioms are `propext`, `Classical.choice`, and
   `Quot.sound`. Distinguish the Lean kernel from an independent kernel
   implementation. The official Palomar Comparator and independent replay
   are still pending. Inspect `MODULE_MIGRATION.json`, the migration patch,
   and upstream provenance; imported analytic results are not exempt from
   a semantic review merely because they are imported.

The original working manuscript is historical provenance. The formal proof
replaced its general mixed-determinant trace step with smooth comparison,
sublevel estimates, layer cake, and Young's inequality. It also includes
dimension two. Review the implemented route, not an assumed identity with
the manuscript.

## Review B: narrative and mathematical implications

Read `ABSTRACT.md`, `SUMMARY.md`, `README.md`, `STATEMENT_AND_OPTIMALITY.md`,
`INFORMAL.md`, `TRACE_METHOD.md`, and the metadata description. Check each
claim against the two actual Lean statements.

- Verify the Hölder calculation giving
  $|\bigcup T_j|\gtrsim_n N\delta^{n-1}/\log(2/\delta)^{n-1}$.
- Verify the direction-net consequence for neighborhoods of every Kakeya
  set, including the normalization and the fixed unit segment length.
- Check the matching construction in Fernández-Delgado–de la Salle,
  arXiv:2607.14824, Theorem 1.3, directly against a primary source. It should
  give a fixed Kakeya set with the matching neighborhood upper bound in
  every dimension. Do not confuse this with a sharp bound for every sparse
  tube cardinality or a sharp Hausdorff gauge.
- Check the radial lower bound for the precise tube definition, and the
  conclusion excluding a growing iterated-logarithm denominator.
- Distinguish optimality of an overlap integral from optimality of union
  volume; verify the reverse Hölder calculation for the Besicovitch examples.
- Check the three exponents: $(n-1)/n$, $1$, and $-(n-1)$. Watch for a
  missing $q$-th root, a radius change, or confusion with the upstream
  maximal exponent $2(n-1)/n$.
- Check that the abstract does not imply that the lower bounds, geometric
  corollaries, external construction, or a sharp Hausdorff gauge are
  formalized. Check the description of AI assistance and the absence of an
  independent human review or priority determination.
- Suggest clearer prose in Mark's mathematical style: define symbols on
  introduction, use theorem/proof structure, explain why each estimate is
  useful, and omit routine algebra and promotional language.

## Running checks

For the configured target toolchain, the reproduction commands are in
`README.md`. If Lean 4.35.0 or its dependencies are unavailable, report that
fact and continue the source and narrative review.

On the preparation Mac there is also a checked sibling project
`../kakeya_sharp`. After reading the driver, this command reruns the short
local checks against the existing Lean 4.34.1 module-port artifacts:

```sh
python3 scripts/review_local_434.py --output review/claude/runs/local-434
```

It records source hashes and toolchain details and refuses to reuse its
output directory. It is a cached-artifact check, not a clean build or an
independent-kernel replay. Inspect existing evidence before starting a
full fresh rebuild; use a separate build directory for a fresh rebuild.

## Deliverables

Create a new directory under `review/claude/runs/` and write:

1. `formal-review.md`: verdict, issues ordered by severity, exact file and
   declaration references, checks run, and limits of verification.
2. `narrative-review.md`: inaccurate or unclear claims with proposed
   replacements, and a claim-by-claim correspondence table.
3. `proposed-abstract.md` and `proposed-summary.md`: revised prose where
   revisions improve fidelity or readability; otherwise explain that the
   existing text can stand.
4. `verdict.json`: source identity, reviewer/model as actually available,
   formal and narrative verdicts separately, unresolved blockers, and log
   paths. Distinguish “no issue found” from “independently verified.”

Preserve the candidate and write proposed changes separately. This review
does not publish a repository or submit to Palomar. Do not mark the queue
completed unless the requested reports have actually been written.
