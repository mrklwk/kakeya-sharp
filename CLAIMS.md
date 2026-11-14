# Claim and verification ledger

Status on 14 November 2026. “Checked” below refers to the specified local
Lean configuration, not Palomar acceptance or an independent human review.

| Claim or check | Status | Evidence or next action |
| --- | --- | --- |
| Strong maximal bound, all integer $n\ge2$, power $(n-1)/n$ | Lean 4.34.1 checked | `Solution.lean`: `KakeyaPalomar.sharpMaximalBound` |
| Weighted tube overlap, exponent $n/(n-1)$, one logarithm | Lean 4.34.1 checked | `Solution.lean`: `KakeyaPalomar.sharpTubeBound` |
| Earlier module-port build | Successful completion recorded; only a tail log retained | `provenance/module-port-lean434-build.log`, starting at job 9396 of 10819; not a complete from-source transcript |
| Claude local from-source recompile | All 212 local files passed in Lean 4.34.1; OpenAI and mathlib artifacts reused | `review/claude/accepted/claude-fable-20261114/local-rebuild-434/rebuild-summary.json` |
| Main theorem axiom audit | Only the three permitted standard axioms | `provenance/module-port-lean434-axioms.txt` |
| Broader audit of 587 declarations | Passed the same axiom allowlist | `provenance/module-port-lean434-full-audit.txt` |
| Literal statement and measure/operator semantics | 11 declarations checked in Lean 4.34.1 | `SemanticAudit.lean`, `provenance/semantic-audit-lean434.txt` |
| Challenge/Solution elaborated definitions and statement types | 10 expression comparisons passed | `provenance/statement-bindings-lean434.json`; normalizes bound names and metadata only |
| Tube union-volume lower bound | Written Hölder consequence | `SUMMARY.md`, Corollary 3; not a separate Lean target |
| Kakeya-neighborhood lower bound | Written direction-net consequence | `SUMMARY.md`, Corollary 4; not a separate Lean target |
| Kakeya maximal function conjecture | Written consequence of the logarithmic bound | `SUMMARY.md`; no priority claim |
| Minkowski dimension of every bounded Kakeya set is `n` | Written consequence of the neighborhood bound | `SUMMARY.md`; not a separate Lean target |
| Matching maximal lower bound and no iterated-log improvement | Written radial proof | `STATEMENT_AND_OPTIMALITY.md`; not formalized |
| Matching Besicovitch construction in every dimension | External preprint result | Fernández-Delgado–de la Salle, arXiv:2607.14824, Theorem 1.3; not formalized here |
| Optimal numerical constants or a sharp Hausdorff gauge | Not claimed | The constants depend on fixed dimension |
| Lean 4.35.0 and pinned newer mathlib | Not yet checked | Build the exact target configuration before Palomar preflight |
| Official metadata and textual source checks | Passed locally | `provenance/palomar-static-validation.json` |
| Official Palomar Comparator and independent replay | Not run | `.github/workflows/palomar.yml`, `comparator.json` |
| Claude formal and narrative review | Completed; supported narrative and evidence corrections integrated | `review/claude/INTEGRATION.md`, `review/claude/QUEUE.json`; AI review, not independent human review or kernel replay |
| Independent human mathematical review | Not completed | Do not infer this from AI review or compilation |
| Public GitHub repository and Palomar submission | Not created/submitted by this task | `RELEASE.md` lists the remaining steps |

The original checkpoint and proof source are preserved. Narrative edits and
review preparation do not alter the two target statements or their proofs.
