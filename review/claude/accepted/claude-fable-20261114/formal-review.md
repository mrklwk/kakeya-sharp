# Formal review: Lean statements and proof evidence

Run `claude-fable-20261114`, 14 November 2026.
Reviewer: Claude (model `claude-fable-5-1`, Claude Code desktop session on the preparation Mac). This is an AI review. It is not an independent human mathematical review, not the Palomar Comparator, and not an independent kernel replay.

## Source identity

| Item | Value |
| --- | --- |
| Git commit of the candidate | `f23da3e966c49a2ffba03d933aabb7521daedcd9` (working tree clean apart from the git-ignored `review/claude/runs/`) |
| Lean source identity (SHA-256 over the 1895 `.lean` hashes in `SOURCE_SHA256.json`, as computed by `scripts/review_local_434.py`) | `1fec6ac9cb78d62dd06e6dd9aa696246f201e56d74258400e2369ef630b4a411` (identical to the preparation run) |
| `Challenge.lean` | `1a6b4fbdcab5148f254ae726ca6259877e401d218b969891f9e0fd44bb606cf3` |
| `Solution.lean` | `73f2703c1ff28ef2a59ad02d94b0de0c449965b05199501853b94cb464b78fce` |
| `KakeyaSharp/Definitions.lean` | `6dcf64e0c73e840a12f06a0f70f4dde23f5868eb4fcb10aba0c003c354aec49c` |
| `KakeyaSharp/SharpTheorem.lean` | `068907c719eed4d32b7031a094df7988dab9d034aceafcd9a2d01d4678edd373` |
| Toolchain actually used | Lean 4.34.1 (`arm64-apple-darwin24.6.0`, commit `5045d0056413266e57c625dcd7c365b10e377c52`), from `~/.elan/toolchains`; `lean`, `lake`, `elan` are not on `PATH` |
| mathlib actually used | `d13f23b723b8a846827a245b89c10fc7d3f11612` (compiled in `../kakeya_sharp/.lake/packages/mathlib`, clean Git tree, verified by the driver) |
| Target configuration | Lean 4.35.0, mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`): **not run**; no 4.35.0 toolchain is installed here and the review did not install one |

## Verdict

**Statements: faithful.** Both `KakeyaPalomar.sharpMaximalBound` and `KakeyaPalomar.sharpTubeBound` in `Solution.lean` (and identically in `Challenge.lean`) encode exactly the two intended theorems of `review/claude/REQUEST.md`, with canonical mathlib notions throughout. I found no missing hypothesis, changed definition, circular assumption, vacuous norm or measure, wrong exponent, or quantifier misorder.

**Proofs: kernel-checked in Lean 4.34.1, re-established here from source for all local modules.** In this review every one of the 207 `KakeyaSharp` modules, plus `KakeyaSharp.lean`, `Solution`, `Challenge`, `SubmissionAudit`, and `SemanticAudit` (212 files), was recompiled from the current source bytes with the Lean 4.34.1 compiler in dependency order into a separate directory, against the cached compiled artifacts of the 1682 vendored `OAI` upstream modules and of mathlib. All 212 compiled; the only diagnostics were the two deliberate `sorry` warnings in `Challenge.lean`. The axiom reports produced from these freshly compiled modules list exactly `propext`, `Classical.choice`, `Quot.sound` for both theorems and for the eleven semantic-audit declarations.

**Independently verified** (by my own runs on this machine): the two target statements elaborate to the same expressions in a mathlib-only environment and in the proof environment; the local proof modules compile from source; the final axiom footprint; the semantic audit; the source manifest hashes.
**Checked by reading, not independently executed**: the 1682 upstream `OAI` modules (loaded from cache, not recompiled), the full Lean 4.34.1 build log (a tail excerpt only; see issue F1), and the mathematics inside the proof chain (three delegated read-only sub-reviews, `proof-route-subreviews.md`, found no semantic gap).
**Not verified and pending**: the Lean 4.35.0 build, official Palomar Comparator, independent kernel replay, and any human review.

## The two statements, read literally

`Space n := EuclideanSpace ℝ (Fin n)` (mathlib's `PiLp 2`, Euclidean norm and distance; `volume` is mathlib's Lebesgue measure on it; `space_dimension` confirms real dimension `n`).

`sphereMeasure n := (volume : Measure (Space n)).toSphere.map Subtype.val`. In mathlib (`Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`) `μ.toSphere s = finrank ℝ E • μ(Ioo 0 1 • s)`, so for Lebesgue measure it is the unnormalized surface measure, with `toSphere_apply_univ : μ.toSphere univ = dim E * μ (ball 0 1)`, that is $\sigma(S^{n-1})=n\kappa_n$. `Subtype.val` is measurable, so `Measure.map` is the genuine pushforward (not the zero measure that `map` returns for non-measurable maps); `sphere_mass_positive` and `sphere_mass_finite` in `SemanticAudit.lean` confirm $0<\sigma(\mathbb R^n)<\infty$, and `sphere_supported_on_unit_vectors` confirms a.e. support on unit vectors. Hence `kakeyaMaximal δ f`, although defined for every `ω : Space n`, is integrated only over unit directions.

`tube δ ω x := ⋃ t ∈ Icc (-1/2) (1/2), Metric.ball (x + t • ω) δ`: the open $\delta$-neighbourhood of the unit segment centered at `x` in direction `ω` (for `‖ω‖ = 1`), end caps included. Open, hence measurable. `actual_tube_volume_positive_finite` gives $0<|T|<\infty$ for $\delta>0$, so the `ℝ≥0∞` division in `kakeyaMaximal` never meets $0$ or $\infty$ in the denominator.

`kakeyaMaximal δ f ω := ⨆ x, (∫⁻ y in tube δ ω x, ‖f y‖ₑ) / volume (tube δ ω x)`: supremum over all centers of the average of $|f|$ (complex absolute value as `‖·‖ₑ`) with the actual volume. The lower integral needs no measurability hypothesis and is never vacuous. `includes_every_center` and `indicator_of_tube_is_nontrivial` show it is the intended operator and is not trivially zero.

**`sharpMaximalBound (hn : 2 ≤ n)`**: `∃ C : ℝ, 0 < C ∧ ∀ δ, 0 < δ → δ ≤ 1 → ∀ f : Space n → ℂ, MemLp f n volume → MemLp (kakeyaMaximal δ f) n (sphereMeasure n) ∧ eLpNorm (kakeyaMaximal δ f) n (sphereMeasure n) ≤ ENNReal.ofReal (C * Real.log (2 / δ) ^ (((n:ℝ) - 1) / n)) * eLpNorm f n volume`.
- Quantifier order $\forall n\,\exists C\,\forall\delta\,\forall f$: correct; `C` cannot depend on $\delta$, $f$, centers, or directions.
- Exponent `n : ℕ` cast to `ℝ≥0∞`; `MemLp f n volume` is strong $L^n(\mathbb R^n)$; the conclusion includes `MemLp` of the maximal function, i.e. a.e. strong measurability and finite norm, so this is strong $L^n(S^{n-1})$ control, not an a priori estimate on a restricted class.
- `eLpNorm` of an `ℝ≥0∞`-valued function uses `‖a‖ₑ = a` (mathlib `enorm_eq_self`, `rfl`; `extended_output_norm_is_identity`), so the left side is $(\int K_\delta f^n\,d\sigma)^{1/n}$.
- `Real.log (2/δ) ^ (((n:ℝ)-1)/n)` is `Real.rpow` of a positive base (for $\delta\le1$, $\log(2/\delta)\ge\log2>0$); parsed as $(\log(2/\delta))^{(n-1)/n}$ since application binds tighter than `^`. `literal_maximal_statement` restates the theorem with `Real.rpow` and all mathlib names written out and closes by `exact`, so the elaborations agree.
- Dimension two is included (`2 ≤ n`).

**`sharpTubeBound (hn : 2 ≤ n)`**: `∃ C, 0 < C ∧ ∀ (m : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 → ∀ v x : Fin m → Space n, (∀ i, ‖v i‖ = 1) → (∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) → ∀ a : Fin m → ℝ, (∀ i, 0 ≤ a i) → (∫ y, (∑ i, (tube (2 * δ) (v i) (x i)).indicator (fun _ ↦ a i) y) ^ ((n:ℝ) / ((n:ℝ) - 1))) ≤ C * Real.log (2 / δ) * δ ^ (n - 1) * ∑ i, a i ^ ((n:ℝ) / ((n:ℝ) - 1))`.
- Radius exactly `2 * δ`; directions unit, $\delta$-separated in Euclidean distance; centers `x` arbitrary; coefficients real and nonnegative; $q=n/(n-1)>1$ as a real power of a nonnegative sum; `δ ^ (n - 1)` is a natural power with `n - 1 ≥ 1`.
- The integral is a Bochner integral of a real function. It is **not vacuous**: the integrand is a finite sum of indicators of bounded open sets times nonnegative constants, raised to a real power, hence bounded, measurable, and compactly supported, so it is integrable and the Bochner integral is the Lebesgue integral. (`memLp_weighted_tubes` in `SharpTransfer.lean` and `weightedTubeOverlap_power_integrable` in the chain prove integrability where the proofs need it; the statement itself does not need to assume it.) A lower integral would remove even the appearance of this concern; see F3.
- Right side is a real number; the inequality is in `ℝ`.

**Correspondence of the two environments.** `scripts/audit_statement_bindings.py` (read in full) loads `Challenge` (imports only `Mathlib`) and `Solution` (imports `KakeyaSharp`) in separate Lean processes, exports the elaborated `type` of both theorems and the `type` and `value` of `Space`, `sphereMeasure`, `tube`, `kakeyaMaximal` as `Expr` representations, normalizes only binder names and `mdata`, and requires byte equality. Because instance constants are part of the `Expr`, this also rules out any global instance in `KakeyaSharp`/`OAI` (for `MeasureSpace`, `Norm`, `Dist`, `Inner`, ...) altering the meaning of the statement: I re-ran it and all 10 comparisons passed. Independently, `grep` found exactly one global `instance` in `KakeyaSharp` (`sphereMeasure_isFinite`, proved by `infer_instance`) and no instance in `OAI` on a standard mathlib type; the `OAI` instances are on its own structures, and the vast majority are `local instance`.

`Solution.lean` proves each theorem by `change KakeyaSharp.SharpMaximalBound n; exact ...` and `change KakeyaSharp.SharpTubeBound n; exact ...`. `change` succeeds only up to definitional equality, so the `KakeyaSharp` targets in `Definitions.lean` are definitionally the same propositions (they differ only by the abbreviations `overlapExponent n` and `logLoss n δ`). `Solution` does not import `Challenge` (verified).

## Checks run in this review

| Check | Command or method | Result | Log |
| --- | --- | --- | --- |
| Short local audits on existing artifacts | `python3 scripts/review_local_434.py --output review/claude/runs/claude-fable-20261114/local-434` | passed: `SubmissionAudit` 2 reports, `SemanticAudit` 11 reports, all within the allowlist; 10 binding comparisons equal; source manifest matches; mathlib checkout clean at `d13f23b…` | `local-434/result.json`, `local-434/*.log`, `local-434/bindings.json`, `local-434-driver.log` |
| From-source recompile of all local modules | `local-rebuild-434/rebuild_local.py`: 212 files (`KakeyaSharp/**`, `KakeyaSharp.lean`, `Solution`, `Challenge`, `SubmissionAudit`, `SemanticAudit`) compiled with `~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -o` in import order, 4 workers, output in a separate scratch directory placed first on `LEAN_PATH`; `OAI` and dependency `.olean`s from the existing caches | 212/212 compiled, 0 failures, 348 s wall, longest module 15.2 s; diagnostics only the two intended `sorry` warnings in `Challenge.lean`; axiom reports from the fresh `Solution` identical to the allowlist | `local-rebuild-434/rebuild-summary.json` (per-module return code, seconds, source SHA-256, output), `local-rebuild-434/rebuild.log` |
| Source scan | `grep` over `KakeyaSharp`, `OAI`, `Solution.lean`, `Challenge.lean` for `axiom`, `sorry`, `native_decide`, `implemented_by`, `@[extern`, `unsafe`, `partial`, `opaque`, `Lean.ofReduceBool`, `attribute [... instance`, `instance` | only `sorry` at `Challenge.lean:42,56`; no axioms; no unsafe/extern/implemented_by; `maxHeartbeats`/`synthInstance.maxHeartbeats` raised in 109 files (elaboration budget only) | this file |
| Full 587-declaration axiom audit | re-parsed `provenance/module-port-lean434-full-audit.txt` with a multi-line-aware regex | 587 reports, 0 with axioms outside the allowlist | this file |
| Migration patch | read every `+`/`-` line of `provenance/module-port.patch` (684 lines) | changes are: header comments, `private` → public on 8 declarations, `set_option synthInstance.maxHeartbeats 200000` (22 files) and one `maxHeartbeats 1000000`, `import all Mathlib.Analysis.Calculus.Implicit` (3 files), explicit `(𝕜 := ℝ)`, `(C := C)`, `(C := ‖f‖)`, `(M := 1)` arguments. No hypothesis, axiom, or proof body changed. `MODULE_MIGRATION.json` lists the same 34 files under `additional_changes` | this file |
| mathlib definitions | read `Measure.toSphere`, `toSphere_apply_univ`, `enorm_eq_self` in the checked-out mathlib | as described above | this file |
| Final deduction | read `KakeyaSharp/SharpTransfer.lean` in full, with the statements of `lintegral_kakeya_le_net`, `packetCap`, `unit_sphere_finite_separated_net`, `finite_kakeya_moment_of_integral_bound`, `exists_volume_tube_real_lower`, `packetCap_real_upper_all_scales` | see "Proof route" | this file |
| Proof route | three delegated read-only sub-reviews | no semantic gap found | `proof-route-subreviews.md` |

## Proof route (read, not executed)

`sharpTubeBound_of_two_le` (`SharpTheorem.lean`) sets $n=m+1$, $m\ge1$, and unfolds `Graph.exists_allDirectionTube_constant` (`AllDirectionTubes.lean`), whose statement is literally the tube theorem with `inputExponent m = (m+1)/m` and `δ^m`. From there (sub-review C) finitely many rotated charts, each a $1/16$-cap around a unit vector, cover $S^{n-1}$ with a number of charts $J$ fixed before all data; within a chart the tubes are grouped by a $2$-separated net of the centers (Hölder factor $(8^{n})^{q-1}$) and translated, so centers are unrestricted; the full open Euclidean radius-$2\delta$ tube, caps included, is contained in a graph tube of transverse radius $4\delta$ in packet coordinates (`tube_near_north_in_graph`); unit-vector separation $\delta$ becomes slope separation $\delta/2$ (`slope_separated`); the closed scale $\delta=1$ is handled by a crude packing bound. All constants are built from $m$ and fixed net cardinalities.

Below the graph-tube layer (sub-review B) the chain is: input estimate with one $\log(2/\delta)$ from the barrier height at $h=\delta^4$ (`inputBarrier_value_le_log`, `kakeyaPacketFamily_input_estimate`), propagation of a weakly superharmonic value function losing one more logarithm (`exists_weak_singleLog_cylinder_constant`, total $\log^2$ at `exists_kakeyaPacketFamily_output_upper_constant`), and the logarithmic thin-source lower bound at the output recovering one logarithm (`thinSource_realValue_lower_scaled` with $\log(10/\delta)\ge\log(2/\delta)$), divided out in `exists_normalizedTube_constant`; the net power is exactly one. The weighted trace argument (`thinDet_smooth_comparison`, `thinDet_sublevel_bound`, `ThinAdmissibleAt.trace_bound`, `thinValueRealAt_weighted_bound`) has every hypothesis discharged downstream, with constants $3^{m+1}(m+1)$ and $\frac m{m+1}(3^{m+1}(m+1))^{1/m}$ as `TRACE_METHOD.md` states. Finiteness of the `EReal` variational value is proved before `toReal` is taken, so no bound is trivially $0$.

The logarithmic test (sub-review A) is `thinProfile η z = log((η²+‖P‖²)/(η²+1−‖x‖²))`, with PSD (indeed positive definite) quaternionic Hessian, zero boundary values, depth $\ge\log(1/\eta)$ on the core, and determinant energy $\le$ `thinEnergyConstant m · log(1/η)` for all $m\ge1$ (`thinEnergy_le_log`). The planar case uses `spatial_boundary_integral_log_of_one_le` in `EnergyBoundaryAllDimensions.lean` (the `2 ≤ m` lemma in `EnergyBoundary.lean` is dead code), and the scale identity with the negative real exponent $\delta^{m-2}$ at $m=1$ is `output_delta_power_real` (`Packet/OutputScaling.lean`), the version actually used.

Maximal deduction (`SharpTransfer.lean`, read in full): $q$-th root of the tube bound gives `TubeNormBound` with loss `logLoss n δ = log(2/δ)^((n-1)/n)`; duality over finite center selections (`finite_kakeya_moment_of_integral_bound`, with the real tube-volume lower bound $c\delta^{n-1}$) gives $\sum_i K_{2\delta}f(v_i)^n$ for a $\delta$-separated $\delta$-net $v_i$; `lintegral_kakeya_le_net` dominates $K_\delta f(\omega)^n$ for $\omega$ within $\delta$ of $v_i$ by $4^{n^2}K_{2\delta}f(v_i)^n$ (a radius-$\delta$ tube in a direction within $\delta$ of $v_i$ lies in the radius-$2\delta$ tube in direction $v_i$ with the same center); cap measure $\le U(32\delta)^{n-1}$ for `packetCap (32δ) v = {‖ω‖=1, ‖ω−v‖ ≤ δ}`; `critical_scale_identity` cancels all powers of $\delta$ exactly; `maximal_norm_of_moment` takes the $n$-th root and proves `MemLp` via `measurable_kakeyaMaximal`. Each step matches `INFORMAL.md`.

## Issues, ordered by severity

**F1 (medium; evidence, not mathematics). The recorded "full build" log is a tail excerpt.** `provenance/module-port-lean434-build.log` starts at job `[9396/10819]` and contains 113 `Built` lines; `CLAIMS.md`, `README.md`, and `VALIDATION.json` describe it as a passed full build. The compiled `.olean`s exist and my from-source recompile of all local modules succeeded, so there is no indication of a problem, but the ledger overstates the artifact. Keep the complete log of the next (4.35.0) build, or describe this one as a tail.

**F2 (medium; scope of this review). The 1682 upstream `OAI` modules were loaded from cache, not recompiled.** Their `.olean`s in `.lake/build/lib/lean/OAI` (786 MB) were produced by the earlier Lake build; this review did not re-elaborate them (disk: 3.1 GiB free; the request asked to inspect existing evidence before a fresh rebuild). Lean's import of `.olean` files does not re-verify source hashes, and Lake's `.trace` files record output hashes rather than a recomputable source hash. Consequently the statement "the current `OAI` source bytes are what was compiled" rests on `SOURCE_SHA256.json` plus `MODULE_MIGRATION.json`, not on recompilation. The Lean 4.35.0 build on a host with that toolchain will close this gap; the independent kernel replay closes the trust gap in the kernel itself.

**F3 (low; robustness of statement). Bochner integral in `sharpTubeBound`.** As argued above the integrand is always integrable, so the statement is not vacuous. If the statement is ever revised, `∫⁻ y, ENNReal.ofReal (...)` or an explicit `Integrable` conjunct would make this evident to a reader who does not want to reason about integrability; no change is required for correctness.

**F4 (low; hygiene). Dead lemmas with `2 ≤ m` hypotheses** (`spatial_boundary_integral_log`, `spatial_log_integral`, `output_delta_power`, `output_lower_scaling`, `thinEnergy_log_bound`) remain in the sources beside the `1 ≤ m` versions actually used. They do not affect the theorem but could mislead a reader about dimension two. `TRACE_METHOD.md` still says "Fix $m\ge2$" in one section (see `narrative-review.md`, N5).

**F5 (low; elaboration budget).** 109 files raise `maxHeartbeats` (up to 1 000 000) or `synthInstance.maxHeartbeats` (200 000). This has no soundness effect; it is noted because Palomar's execution profile may impose its own limits.

**F6 (information). `lakefile.toml` default targets include `Challenge`**, so any `lake build` emits the two intended `sorry` warnings. Harmless; mention it in `README.md` if the Comparator run is noisy.

**F7 (information). Trust base.** The theorems as stated imply the Kakeya maximal function conjecture in every dimension (see `narrative-review.md`, N1). Their truth therefore rests on: the Lean 4 kernel, mathlib at `d13f23b…`, the 1682 vendored upstream modules compiled under the same kernel, the local modules recompiled here, and the toolchain binary from `elan`. This review found nothing wrong at any of these layers, but for a result of this significance the pending independent replay and a second toolchain build are the right next steps, not optional ones.

No issue of higher severity was found. In particular: no circularity (the only analytic hypothesis of `sharpMaximal_of_sharpTube` is the tube bound, discharged by `sharpTubeBound_of_two_le`); no δ- or data-dependent constants; no restriction of centers or directions surviving to the final statement; no vacuous measure or norm.

## Limits of verification

- Lean 4.35.0 with mathlib `56a0058…`: not run (toolchain not installed; not installed by this review). A passing 4.34.1 build is not a passing Palomar run.
- Official Palomar Comparator, `lake comparator --config comparator.json`, and independent kernel replay: not run.
- Upstream `OAI` modules: compiled artifacts reused, sources not re-elaborated (F2); their mathematical content was reviewed only at the level of the statements the local chain invokes (`cylinderAverage_logarithmic_lower_on`, `cylinderTimeTrace_le_average_on`, the Dirichlet/comparison lemmas named in `TRACE_METHOD.md`), not line by line.
- `unitPacketFamily_weakSuperharmonic` and the `Packet/Smooth`/`Dirichlet` chain that discharges the weak superharmonicity hypothesis of the propagation step were not read.
- The three sub-reviews are themselves AI output; their line references were spot-checked, not all re-verified.
- No human mathematician has reviewed the mathematics; this review does not change that.

## Files in this run directory

`formal-review.md` (this file), `narrative-review.md`, `proposed-abstract.md`, `proposed-summary.md`, `proof-route-subreviews.md`, `verdict.json`, `local-434/` (driver output), `local-434-driver.log`, `local-rebuild-434/` (from-source recompile script, log, per-module summary), `proposed-QUEUE.json` (the queue entry as it would read after integrating this review; `review/claude/QUEUE.json` itself was left unchanged, as were all candidate files).
