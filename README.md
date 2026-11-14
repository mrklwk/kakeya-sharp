# Sharp logarithmic Kakeya estimates

This is a Palomar submission candidate for the Kakeya maximal upper bound
with logarithmic power `(n-1)/n` in every integer dimension `n >= 2`, together
with the weighted tube overlap bound with one logarithm.

The abstract is in [`ABSTRACT.md`](ABSTRACT.md), with printable LaTeX source in
[`ABSTRACT.tex`](ABSTRACT.tex). The mathematical summary,
including the exact tube union bound and its match with known Besicovitch
constructions, is in [`SUMMARY.md`](SUMMARY.md).

**Preparation status:** the original checkpoint and the module-converted
candidate have Lean 4.34.1 checks. The earlier Lake log records successful
build completion but retains only the tail of the run. Claude's separate AI
review recompiled all 212 local files against cached OpenAI and mathlib
artifacts and found no semantic defect in the two statements. Both submission
results use only `propext`, `Classical.choice`, and `Quot.sound`; a further
587 declaration axiom reports passed the same check. The AI review and its
editorial corrections are recorded in `review/claude/INTEGRATION.md`.
This candidate targets Lean 4.35.0, which satisfies the Palomar minimum
examined on 14 November 2026. Consult `VALIDATION.json` for completed checks
and outstanding verification. A passing older-toolchain build is not a
passing Palomar run. This repository has not been registered with Palomar.

The first full Palomar preflight on the published source failed during the
Lean 4.35.0 Solution build because of changed mathlib arguments and imports.
Compatibility edits in 19 files are recorded in `provenance/lean435-port.json`
and require a fresh full preflight. The two target statements are unchanged;
the older checks and Claude review apply to their recorded source revisions.

## Results

For `0 < delta <= 1`, let `K_delta f(omega)` be the supremum over all centers
of the average of `|f|` over the open radius-delta neighborhood of a centered
unit segment in direction `omega`. For every `n >= 2`, the main result is

```math
\|K_\delta f\|_{L^n(S^{n-1})}
\le C_n [\log(2/\delta)]^{(n-1)/n}\|f\|_{L^n(\mathbb R^n)}.
```

The constant is positive and depends only on dimension. The theorem also
gives `MemLp` for the maximal function. It uses complex-valued functions,
actual tube volumes, and the spherical measure induced by Lebesgue measure.

For delta-separated unit directions, arbitrary centers, nonnegative
coefficients `a_i`, and radius-`2*delta` tubes `T_i`, the second result is

```math
\int_{\mathbb R^n}\Big(\sum_i a_i\mathbf 1_{T_i}\Big)^{n/(n-1)}
\le C_n\log(2/\delta)\,\delta^{n-1}\sum_i a_i^{n/(n-1)}.
```

The matching logarithmic lower bound is proved mathematically in
`STATEMENT_AND_OPTIMALITY.md`; it is not formalized. The radial example there
rules out a smaller power or a growing iterated-logarithm denominator.
No theorem about optimal constants or priority is claimed by this submission.

Hölder's inequality gives the geometric consequence

```math
\left|\bigcup_{j=1}^N T_j\right|
\ge c_n\frac{N\delta^{n-1}}{[\log(2/\delta)]^{n-1}}.
```

In particular, the delta-neighborhood of every Kakeya set has volume at
least `c_n / log(2/delta)^(n-1)`. Fernández-Delgado and de la Salle's
construction attains this order. These consequences and the external
matching construction are explained in `SUMMARY.md`; they are not
additional formalized targets. The maximal estimate implies the Kakeya
maximal function conjecture, and the neighborhood bound gives Minkowski
dimension `n` for every bounded Kakeya set. These are implications of the
estimates, not claims of priority.

## Review entry points

| File | Purpose |
| --- | --- |
| `Challenge.lean` | Self-contained statements; imports only mathlib |
| `Solution.lean` | Same concrete definitions and statements, proved from the development |
| `SemanticAudit.lean` | Literal expanded upper bound and nondegeneracy checks for the measures and operator |
| `STATEMENT_AND_OPTIMALITY.md` | Exact statement, audit explanation, and mathematical matching lower bounds |
| `comparator.json` | Both result names and the three permitted standard axioms |
| `INFORMAL.md` | Proof outline and correspondence with the Lean modules |
| `formalization.yaml` | Mathematical abstract, provenance, AI usage, and scope |
| `MODULE_MIGRATION.json` | Original and ported source hashes |
| `provenance/module-port.patch` | Changes beyond the uniform module conversion |
| `VALIDATION.json` | Exact completed checks and outstanding checks |
| `CLAIMS.md` | Formalized claims, written consequences, and external comparisons |
| `review/claude/INTEGRATION.md` | Completed Claude AI review, accepted edits, and preserved evidence |
| `RELEASE.md` | GitHub publication and Palomar preparation steps |

The two `sorry` terms in `Challenge.lean` are deliberate statement
placeholders for Comparator. There are no proof placeholders in `Solution`
or its local proof dependencies. `Solution` does not import `Challenge`.

## Reproduction

Install the toolchain specified in `lean-toolchain`, then run from this root:

```sh
lake exe cache get
lake build
lake env lean SubmissionAudit.lean
lake env lean SemanticAudit.lean
python3 scripts/audit_statement_bindings.py --output statement-bindings.json
lake comparator --config comparator.json
python3 scripts/check_submission.py
```

`scripts/build_checked.py build` is an optional disk-saving wrapper around
Lake. It deletes completed, regenerable module setup files and preserves
source and proof artifacts. It does not replace any proof checker.

The dependency manifest pins canonical mathlib and its complete dependency
closure by full Git commit. Source is included under `KakeyaSharp/` and
`OAI/`; no compiled proof artifacts are distributed.

## Palomar verification

The manual workflow `.github/workflows/palomar.yml` calls the official
PalomarSubmission workflow pinned at
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7`, in `full` mode with the
`palomar-standard-v1` execution profile. It requires a public GitHub
repository and checks the exact triggering commit. This is a mechanical
preflight; it does not submit or register the result.

Before dispatching, the responsible maintainer should review the proposed
authorship, provenance and license, and choose the truthful authorization
relationship offered by the workflow. Obtain a passing full report before
using the [Palomar submission service](https://submit.palomar-registry.org).
Actual submission and later registration are separate actions.

## Provenance and license

The source is checkpoint 0.19.0 of this project. It reuses 1682 files from
[OpenAI's mathematical formalizations](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae),
plus identified adaptations. The submission copy adds module headers,
public imports and exposed public interfaces; any further porting changes
are recorded explicitly. Original checkpoint records and the working
manuscript are preserved in `provenance/`.

Apache-2.0; see `LICENSE`, `LICENSE-OpenAI`, and `NOTICE`. The original
manuscript is supplied as historical provenance. `Challenge.lean` is the
authoritative submitted statement. Substantial AI assistance and the lack
of independent human mathematical review are disclosed in `formalization.yaml`.
