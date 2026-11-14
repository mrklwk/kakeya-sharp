# Submission port

The starting point is the checked 0.19.0 project, using Lean 4.34.1 and
mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
The original project is preserved separately. The target submission uses
Lean 4.35.0 and canonical mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

The module conversion is applied to 1891 original Lean files. Each receives
`module`, public imports, and an exposed public section. All 207 local
mathematical modules remain reachable from the final proof. The additional
statement, solution, and axiom-audit files brought the count to 1894.
The later `SemanticAudit.lean` brings the current total to 1895.

The upstream files needing changes beyond the uniform conversion are listed
in `MODULE_MIGRATION.json`. They fall into the following categories:

- Eight internal declarations used by exposed interfaces become public:
  `memLp_wavePhase_mul`, four fourth-derivative Holder norm definitions,
  and three Holder-space aliases.
- `HolderPullback` and `CutoffEquation` explicitly supply the real constant
  in their calls to `HolderMap.ofBounded`. The original proof already
  determines that constant. `BoundaryTraceEnergy` similarly supplies the
  operator bound `M = 1` explicitly.
- Three Green identity files explicitly import the private implementation
  of mathlib's implicit-function construction for use in their proofs.
  Two also specify the scalar field as the real numbers. The statement
  module does not use these imports.
- The 22 modules constructing continuous scalar multiplication through
  bounded scalar multiplication use a consistent increased typeclass search
  heartbeat budget. Several exceeded the default limit after migration.
  The fourth-derivative pullback module raises the general elaboration budget.

These are elaboration and visibility changes. They do not add mathematical
hypotheses, axioms, or proof placeholders. Exact differences are in
`provenance/module-port.patch`, and SHA-256 records are in
`MODULE_MIGRATION.json`. The original OpenAI Git blob hashes remain in
`UPSTREAM_DIRICHLET.json`; the ported files are not described as byte-identical
to upstream.

`Solution.lean` repeats the concrete definitions in `Challenge.lean` and
proves the two statements by changing each goal to its definitionally
equal checkpoint target. It imports the proof development without importing
the Challenge's intentional theorem placeholders.

Local checks use the available Lean 4.34.1 installation to test the module
conversion and the proof bridges. Their exact configuration is retained
under `provenance/local-check-*`. They do not validate the newer mathlib
revision or substitute for the required Lean 4.35.0 and Palomar checks.
Those outstanding checks are recorded explicitly in `VALIDATION.json`.
