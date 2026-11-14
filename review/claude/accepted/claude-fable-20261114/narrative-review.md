# Narrative review: abstract and summaries

Run `claude-fable-20261114`, 14 November 2026.
Reviewer: Claude (model `claude-fable-5-1`, Claude Code desktop session). This is an AI review, not an independent human mathematical review.
Source reviewed: Git commit `f23da3e966c49a2ffba03d933aabb7521daedcd9`, Lean source identity `1fec6ac9…b411` (see `verdict.json`).

Files read: `ABSTRACT.md`, `SUMMARY.md`, `README.md`, `STATEMENT_AND_OPTIMALITY.md`, `INFORMAL.md`, `TRACE_METHOD.md`, `CLAIMS.md`, `formalization.yaml` (`project.description`, `fidelity`, `review`), `RELEASE.md`, `PORTING.md`.
Each claim was compared against the two Lean statements in `Solution.lean` and against the primary sources named below.

## Verdict

The narrative is accurate about what is formalized and what is not.
No claim overstates the formal scope, the three logarithmic exponents are correct, and the written deductions (Hölder, direction net, radial lower bound, one-log tube lower bound) check.
The principal shortcomings are omissions and imprecision rather than errors.
The most important omission is that no file says what Theorem 1 implies: an endpoint $L^n\to L^n(S^{n-1})$ Kakeya maximal estimate with logarithmic loss in every dimension implies the Kakeya maximal function conjecture and the Minkowski-dimension form of the Kakeya set conjecture in every dimension.
A reader should be told this plainly, with the appropriate caveats about the verification status.

## Checks performed against primary sources

1. **Fernández-Delgado and de la Salle, arXiv:2607.14824, Theorem 1.3.** Fetched the arXiv abstract page and the HTML full text (v3, revised 17 September 2026) on 14 November 2026. Theorem 1.3 reads, in substance: for every $d$ there exist a Kakeya set $E\subset\mathbb R^d$ and a constant $C$ such that for every $\delta\in(0,1)$ the volume of the $\delta$-neighbourhood of $E$ is less than $C/|\log\delta|^{d-1}$. The set is a single fixed set, the segments have unit length (Definition 5.2), and the paper calls the bound "most likely optimal" and notes that Carbery's reverse Littlewood–Paley conjecture would imply a matching lower bound. This matches the use made of it in `SUMMARY.md` and `ABSTRACT.md`. The paper's Theorem 1.4 is a separate statement about finitely many tubes with a disjointness side condition; the narrative correctly does not cite it as a sharp bound for every sparse tube count.
2. **OpenAI, `kakeya.tex` at commit `4eaee875…`.** Fetched the raw file. Its displayed maximal bound has power $4/p_c$ with $p_c=2n/(n-1)$, that is $2(n-1)/n$, and its radial paragraph gives the lower power $1-1/n=(n-1)/n$. `STATEMENT_AND_OPTIMALITY.md` and the reference note in `SUMMARY.md` describe this correctly.
3. **Hölder calculation (Corollary 3).** With $M=\sum_j 1_{T_j}$, $U=\bigcup_j T_j$, $A=N\delta^{n-1}$, $q=n/(n-1)$: $\int M\asymp_n A$, and $\int M^q\le\int M_{2\delta}^q\le C_nL\,\delta^{n-1}N=C_nLA$ by pointwise domination $M\le M_{2\delta}$. Hölder gives $A\lesssim|U|^{1/n}(LA)^{(n-1)/n}$, so $|U|\gtrsim A/L^{n-1}$. Correct. The domination step by radius-$2\delta$ tubes is used but not written in the proof; it should be.
4. **Direction-net consequence (Corollary 4).** A maximal $\delta$-separated set of unit vectors has cardinality $\asymp_n\delta^{-(n-1)}$; the radius-$\delta$ tube about the unit segment of $K$ in each direction lies in the open $\delta$-neighbourhood $N_\delta(K)$; Corollary 3 gives $|N_\delta(K)|\gtrsim_n\delta^{-(n-1)}\delta^{n-1}/L^{n-1}=L^{-(n-1)}$. Correct. The normalization (unit segment, open neighbourhood, tube centered at the segment midpoint) agrees with the Lean `tube`.
5. **Radial lower bound (`STATEMENT_AND_OPTIMALITY.md`).** Every inequality was rechecked for the exact tube: $\|f_\delta\|_n^n=s_{n-1}\log(1/(4\delta))$; the cylinder $4\delta<t<1/4$, $|z|<\delta/2$ lies in $T_\delta(\omega,0)\cap\{2\delta<|y|<1/2\}$; $|y|\le t+\delta/2\le2t$; the integral is at least $\kappa_{n-1}2^{-n}\delta^{n-1}\log(1/(16\delta))$; $|T_\delta|=\kappa_{n-1}\delta^{n-1}+\kappa_n\delta^n$; $\log(1/(16\delta))\ge\tfrac12\log(1/\delta)$ exactly when $\delta\le1/256$. The ratio bound $c_n[\log(1/\delta)]^{(n-1)/n}$ and the little-oh conclusion follow. Correct.
6. **One-log tube lower bound.** Centers at the origin, maximal $\delta$-separated directions, unit weights. For $C\delta\le r\le c$, directions within $\delta/(2r)$ of $\theta$ give tubes containing $r\theta$; a maximal separated set is a $\delta$-net so the cap holds $\gtrsim_n r^{-(n-1)}$ directions once $\delta/(2r)\ge2\delta$; then $\int M^q\gtrsim\int_{C\delta}^c r^{-n}r^{n-1}dr\asymp\log(1/\delta)$ while $\delta^{n-1}\sum a_i^q\asymp_n1$. Correct. The reverse-Hölder argument for Besicovitch families in `SUMMARY.md` is also correct: $\int M^q\ge(\int M)^q/|U|^{q-1}\gtrsim L^{(n-1)(q-1)}=L$.
7. **Exponents.** $(n-1)/n$ is the $q$-th root of the one logarithm in Theorem 2 (`KakeyaSharp/SharpTransfer.lean`, `sharpTube_to_norm` and `critical_scale_identity`); $1$ is the exponent in `sharpTubeBound`; $-(n-1)$ comes from raising the Hölder inequality to the $n$-th power. No $q$-th root is missing, the radius change $\delta\to2\delta$ is handled by domination, and the upstream power $2(n-1)/n$ is only mentioned as the upstream power. For $n=2$ the maximal power $1/2$ agrees with Córdoba's bound, which is a useful sanity check that the narrative could mention.

## Issues, ordered by importance

### N1. The mathematical consequence of Theorem 1 is never stated

`ABSTRACT.md`, `SUMMARY.md`, and `README.md` describe exponents and sharpness but never say that a bound $\|K_\delta\|_{L^n\to L^n(S^{n-1})}\lesssim_n[\log(2/\delta)]^{(n-1)/n}$ in every dimension implies the Kakeya maximal function conjecture, that Corollary 4 gives lower Minkowski dimension $n$ for every Kakeya (Besicovitch) set, and that Hausdorff dimension $n$ follows by the standard argument from the maximal estimate.
"Faithful scope" cuts both ways: the text must not overstate what is formalized, but it should also not leave the reader to infer the significance.
To the reviewer's knowledge (literature through mid-2026) the maximal conjecture was known in dimension two (Córdoba, with the same $\log^{1/2}$) and the set conjecture in dimension three (Wang–Zahl, 2025); the all-dimension statements are attributed in this project's own references to the October 2026 OpenAI preprint, with a weaker power. The author should confirm the literature status before publication; the reviewer cannot.
**Proposed fix:** add one paragraph to `SUMMARY.md` (included in `proposed-summary.md`) and one sentence to the abstract, both labelled as consequences of the formal theorem plus written deductions, and keep the existing disclaimer that no priority claim is made.

### N2. "Sharp ... estimates" reads as if sharpness were formalized

The title and first sentence of `ABSTRACT.md` ("We give a Lean formalization of sharp logarithmic estimates") and `formalization.yaml`'s `project.name` and `description` put "sharp" inside the scope of "formalize". The disclaimer arrives only in the last sentence. A reader of the first line alone will take the lower bounds as formalized.
**Proposed fix:** "We give a Lean formalization of two logarithmic upper estimates ... whose logarithmic powers are optimal; the optimality is a written argument, not a Lean theorem." See `proposed-abstract.md`.

### N3. The abstract omits the two conventions a formal reader needs

The abstract says "for separated directions" without saying $\delta$-separated unit vectors, and does not mention that the formal tube estimate uses radius $2\delta$. The request treats both as part of the exact intended statement; `SUMMARY.md` has them, the abstract and `formalization.yaml` description do not.
**Proposed fix:** one clause each; see `proposed-abstract.md`.

### N4. Fernández-Delgado–de la Salle is cited slightly below its strength and without its optimality remark

`SUMMARY.md` says the construction gives $|N_\delta(K)|\lesssim_n[\log(1/\delta)]^{-(n-1)}$ "for small $\delta$". Theorem 1.3 states it for every $\delta\in(0,1)$ with a fixed constant. The paper also says this order is conjecturally optimal and that Carbery's conjecture would give the matching lower bound; Corollary 4 here is precisely that lower bound. This deserves a sentence, phrased as a consequence of the formal theorem plus the written Hölder step.
**Proposed fix:** quote the theorem's quantifiers and add the sentence; see `proposed-summary.md`.

### N5. `TRACE_METHOD.md` contradicts the current state in two places

Line 7: "The matching logarithmic lower bound remains unfinished." `STATEMENT_AND_OPTIMALITY.md` now contains a written lower bound. Section "Finite covering and the normalized tube bound": "Fix $m\ge2$", and the scale identity is stated with the natural exponent $\delta^{m-2}$ (valid only for $m\ge2$), while the live Lean chain uses the real-exponent identity `output_delta_power_real` with `1 ≤ m` (`KakeyaSharp/Packet/OutputScaling.lean`), so dimension two is included. `INFORMAL.md` says so correctly.
**Proposed fix:** add a header line to `TRACE_METHOD.md`: "Historical note for checkpoints 0.14.0–0.18.0; the current chain includes $m=1$ and the lower bound is now written in `STATEMENT_AND_OPTIMALITY.md`", and change "Fix $m\ge2$" to "Fix $m\ge1$" with the exponent written as a real power.

### N6. Build evidence is described more strongly than the artifact supports

`CLAIMS.md` ("Full module-port build: Passed"), `README.md` ("The candidate's full build passed"), and `VALIDATION.json` point to `provenance/module-port-lean434-build.log`. That file is a tail excerpt: it begins at job 9396 of 10819 and records 113 "Built" lines, with the first 9395 jobs (mathlib replays and the earlier local modules) absent. The compiled modules do exist and the present review recompiled the local modules from source (see `formal-review.md`), so nothing suggests the build did not pass, but the ledger should say "tail of the build log" or the complete log should be retained.
**Proposed fix:** amend the three descriptions, or replace the log with the complete one from the Lean 4.35.0 rebuild that is required anyway.

### N7. Smaller points

- `SUMMARY.md`, Corollary 3 proof: say explicitly that Theorem 2 is applied to the radius-$2\delta$ tubes, which dominate $M$ pointwise.
- `SUMMARY.md`, Corollary 4: define "Kakeya set" where it is first used (a set containing a unit segment in every direction), and say that antipodal directions give the same segment, which is harmless.
- `INFORMAL.md`: "Admissibility means smoothness near the closed ball" should read "$C^3$ near the closed ball"; the Lean predicate `ThinAdmissibleAt` records `ContDiffAt ℝ 3` only (as `TRACE_METHOD.md` says).
- `ABSTRACT.md`: "neighborhoods of every Kakeya set" should be "$\delta$-neighbourhoods of every Kakeya set".
- `ABSTRACT.md` and `SUMMARY.md`, verification status: after this review the sentence "Claude's review has been prepared but has not run" is out of date. Replace by a sentence that names this run directory, says that it is an AI review, and that it found no issue with the two statements and recompiled the local modules in Lean 4.34.1, with the Lean 4.35.0 build, Comparator, independent replay, and human review still pending.
- `README.md`, "Reproduction": `lake comparator --config comparator.json` was not checked by this review; if it is a Palomar-provided command, say where it comes from.
- `formalization.yaml`, `fidelity.divergences`: accurate. `review.status: self-assessed`: accurate until a human review exists; after integrating this run it could read "self-assessed; AI reviewed (Claude, 14 November 2026)".
- `SUMMARY.md` dimension table: add the remark that the $n=2$ row is Córdoba's bound, which anchors the reader.
- Style (requested): define $L$, $M$, $U$, $A$, $q$ where first used in each proof; the current `SUMMARY.md` does this well. Several sentences carry two ideas ("This explains the correspondence ..."); the proposed texts split them and put one sentence per line.

## Claim-by-claim correspondence

| Claim in narrative | Where | Lean or source | Status |
| --- | --- | --- | --- |
| Strong $L^n\to L^n(S^{n-1})$ bound with $[\log(2/\delta)]^{(n-1)/n}$, all $n\ge2$, $0<\delta\le1$ | ABSTRACT, SUMMARY Thm 1, README | `KakeyaPalomar.sharpMaximalBound` | Matches exactly; $C$ quantified before $\delta$, $f$ |
| Supremum over all centers, average of $\lvert f\rvert$, actual volume with end caps | ABSTRACT, SUMMARY Defs | `kakeyaMaximal`, `tube` | Matches |
| Membership $K_\delta f\in L^n(S^{n-1})$ is part of the conclusion | SUMMARY, README, STATEMENT | `MemLp (kakeyaMaximal δ f) n (sphereMeasure n)` | Matches |
| Surface measure is the usual unnormalized one, mass $n\kappa_n$ | SUMMARY, STATEMENT | `sphereMeasure` = `volume.toSphere.map Subtype.val`; mathlib `toSphere_apply_univ` | Matches |
| Complex-valued $f\in L^n$, no support restriction | SUMMARY, README | `f : Space n → ℂ`, `MemLp f n volume` | Matches |
| Weighted tube bound, $q=n/(n-1)$, one logarithm, $\delta^{n-1}\sum a_i^q$ | SUMMARY Thm 2, README | `KakeyaPalomar.sharpTubeBound` | Matches |
| Radius $2\delta$ in the formal statement | SUMMARY, README, REQUEST | `tube (2 * δ)` | Matches; absent from ABSTRACT (N3) |
| $\delta$-separated unit directions, arbitrary centers, nonnegative real weights | SUMMARY | `‖v i‖ = 1`, `δ ≤ dist (v i) (v j)`, `x` free, `0 ≤ a i` | Matches; ABSTRACT says only "separated" (N3) |
| Radius-$\delta$ version by domination | SUMMARY | not formalized | Correct deduction |
| Corollary 3 union bound | ABSTRACT, SUMMARY, README | written; not a Lean target | Verified (item 3) |
| Corollary 4 neighbourhood bound | ABSTRACT, SUMMARY, README | written; not a Lean target | Verified (item 4) |
| Matching construction, every dimension | ABSTRACT, SUMMARY, CLAIMS | arXiv:2607.14824 Thm 1.3 | Verified against primary source (item 1); quantifiers can be stated more precisely (N4) |
| Radial matching maximal lower bound, no iterated-log improvement | ABSTRACT, STATEMENT, README | written; not formalized | Verified (item 5) |
| One-log tube lower bound | STATEMENT, SUMMARY | written; not formalized | Verified (item 6) |
| Upstream power $2(n-1)/n$ and its radial paragraph | SUMMARY refs, STATEMENT | OpenAI `kakeya.tex` | Verified (item 2) |
| Three exponents $(n-1)/n$, $1$, $-(n-1)$ | SUMMARY table | `SharpTransfer.lean`, `Definitions.lean`, Hölder | Verified (item 7) |
| No optimal constants, no sharp Hausdorff gauge, no priority claim | SUMMARY, CLAIMS, yaml | — | Accurate; but consequences omitted (N1) |
| Lean 4.34.1 checks passed; 4.35.0, Comparator, replay pending | ABSTRACT, SUMMARY, VALIDATION | rerun in this review | Accurate; build log is a tail (N6) |
| "Sharp" estimates formalized | ABSTRACT first line, yaml name | — | Ambiguous (N2) |
| Dimension two included | INFORMAL, yaml fidelity | `sharpTubeBound_of_two_le (hn : 2 ≤ n)`, `1 ≤ m` chain | Matches; TRACE_METHOD says $m\ge2$ (N5) |
| Lower bound "remains unfinished" | TRACE_METHOD line 7 | — | Stale (N5) |
| AI assistance and no human review disclosed | ABSTRACT, yaml | — | Accurate and clear |

## Proposed prose

`proposed-abstract.md` and `proposed-summary.md` in this directory contain full replacement texts.
Both keep every factual claim of the current files, add the consequences paragraph (N1), fix N2–N4 and N7, and are written with one sentence per line, symbols defined on introduction, and theorem/proof structure.
`README.md`, `STATEMENT_AND_OPTIMALITY.md`, and `INFORMAL.md` can stand with the small edits listed under N5–N7; no replacement text is proposed for them.
