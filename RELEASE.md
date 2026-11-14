# GitHub and Palomar preparation

The complete source is public at <https://github.com/mrklwk/kakeya-sharp>.
The initial source commit is `9a20b2896cdab913f21d7db197af3b30306f8250`;
its Git tree matches the reviewed local candidate exactly. No Palomar
submission or registration has been created.

The first official full preflight failed at the Lean 4.35.0 Solution build.
The report is `provenance/palomar-preflight-43625069473.json`. The subsequent
mathlib compatibility edits are recorded in `provenance/lean435-port.json`
and require publication and a fresh full preflight before intake.

## Review the prepared result

Start with `ABSTRACT.md`, `SUMMARY.md`, and the two exact Lean targets in
`Solution.lean`. `Challenge.lean` contains the same declarations with the
two intentional Comparator placeholders. `CLAIMS.md` records which results
are formalized and which are mathematical consequences or external facts.

Claude's formal and narrative review completed on 14 November 2026.
The review and accepted editorial changes are recorded in
`review/claude/INTEGRATION.md`; that integration left the Lean sources unchanged.
The later compatibility edits are outside that review's recorded source revision.
The review recompiled 212 local files in Lean 4.34.1 against cached upstream
artifacts. It does not complete the supported-toolchain preflight below.

For a subsequent review, the request is `review/claude/REQUEST.md`.
From the repository:

```sh
bash scripts/claude_review.sh
```

When the CLI is unavailable, use a Claude Code local session for this
folder and paste the prompt printed by:

```sh
bash scripts/claude_review.sh --print-prompt
```

The queue is a file-based handoff, not a running background job. Review
outputs belong in `review/claude/runs/`, which is excluded from release
archives and Git. The first completed run is preserved verbatim under
`review/claude/accepted/claude-fable-20261114/`. Integrate accepted changes and selected review evidence
deliberately, then refresh the source manifest. A review of one source
revision should not be presented as a review of a later changed proof.

To refresh the manifest and archive from the repository root:

```sh
python3 scripts/package_source.py --output ../../output/Kakeya_Palomar_submission_candidate_2026-11-14.zip
python3 scripts/check_submission.py
```

The package command is a packaging check, not a mathematical verifier.

## Build the supported configuration

The earlier Lean 4.34.1 build retains a successful completion tail only;
Claude's later from-source recompile covers the local files, with compiled
OpenAI and mathlib dependencies reused. The target configuration
uses Lean 4.35.0 and a pinned canonical mathlib revision. On a host with
that toolchain, run the reproduction commands in `README.md`, retaining
the output and the axiom reports. Resolve build failures before treating
the target configuration as verified. The short local 4.34.1 review
driver does not perform this step.

## Public repository

The intended public files include the complete Lean sources, canonical
dependency pins, licenses and upstream notices, narrative summaries,
metadata, and provenance. Build caches, personal credentials, local
review scratch files, and runtime environment files are excluded.

After review and an explicit decision to publish, the prepared Git
repository can be published with the usual GitHub CLI workflow:

```sh
gh repo create mrklwk/kakeya-sharp --public --source . --remote origin --push
git rev-parse HEAD
```

Do not run the create command when the repository or remote already
exists; inspect the existing destination and use the appropriate push.
Record the actual public URL and exact 40-character commit. Preparation
of these commands does not publish anything.

## Full Palomar preflight

The workflow `.github/workflows/palomar.yml` is manual. It pins the official
pipeline and uses `mode: full` with `palomar-standard-v1`.
After the exact source commit is public, the responsible maintainer can
dispatch it, selecting the truthful relationship:

```sh
gh workflow run palomar.yml --repo mrklwk/kakeya-sharp --ref main \
  -f authorization_relationship='I am a responsible author or maintainer'
```

Inspect the actual workflow run and full report. Record the checked commit,
the workflow URL, Comparator result, independent replay result, and resource
status. A local build or a passing source-only check does not replace this
full report. Rerun the relevant verification after a proof or configuration
change.

## Submission and registration

Submit through <https://submit.palomar-registry.org> only after a passing
full mechanical report. Before intake, confirm the exact public repository,
commit, `comparator.json`, and the maintainer relationship being recorded.
Submission and later registration are distinct from publishing on GitHub.
The public description is `project.description` in `formalization.yaml`;
it must continue to agree with `ABSTRACT.md`, `SUMMARY.md`, and the exact
two formal statements.

Current official instructions: <https://submit.palomar-registry.org/llms.txt>.
