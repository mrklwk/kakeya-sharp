# Delegated read-only sub-reviews of the proof route

These are the reports of three read-only subagents (same model family as the main reviewer) that read the Lean sources of the proof route without building anything.
They are AI output, retained verbatim as evidence of what was read and what was concluded.
The main reviewer cross-checked the final-chain statements quoted here against the sources (`SharpTheorem.lean`, `SharpTransfer.lean`, `AllDirectionTubes.lean`, `Definitions.lean`, `Caps.lean`, `DirectionIntegral.lean`, `DirectionNets.lean`, `Discrete.lean`, `Volume.lean`, `Geometry.lean`) and did not re-verify every line reference below.

---

## A. Logarithmic variational test and its energy

Scope: `ThinProfile`, `ThinHessian`, `ThinDeterminant`, `ThinEnergy`, `EnergyBoundary`, `EnergyBoundaryAllDimensions`, and their local imports.

### 1. The explicit test, its PSD Hessian, boundary values, energy bound

**Definition** — `KakeyaSharp/ThinProfile.lean:23-30`: `thinNumerator η z = η^2 + ‖z.2‖^2`, `thinDenominator η z = η^2 + 1 - ‖z.1‖^2`, `thinProfile η z = Real.log (thinNumerator/thinDenominator)`. This is exactly v_η(x,P) = log((η²+|P|²)/(η²+1−|x|²)) on `ThinSpace m = Space m × EuclideanSpace ℝ (Fin m × Fin 2)` (dim 3m).

**Sign / boundary / depth** — `thinProfile_nonpos` (:42), `thinProfile_boundary` (:51, `‖x‖²+‖P‖²=1 → v=0`), `thinProfile_core_depth` (:60): `0<η → η≤1/10 → ‖x‖≤1/2 → ‖P‖≤η → log(1/η) ≤ -v`. Arithmetic checked (ratio ≤ 8η²/3 ≤ η).

**Hessian** — `HessianCalculus.lean:111 thinProfile_hessian` gives the genuine second Fréchet derivative; `ThinHessian.lean:51 thinProfile_quaternionHessian` packages it as `(4/N)•1 − (1/N²)•outer G + (2/D)•1 + (4/D²)•outer X`. Re-derived the real Hessian and the slot sum: consistent. **PSD**: `ThinPositive.lean:34 thinProfile_quaternionHessian_lower`: `(4η²/N² + 2/D)·quaternionSize w ≤ quaternionForm (Hess) w`, and `:63 thinProfile_quaternionHessian_positive` (strict for w ≠ 0). Hypotheses: `0<η`, `z` in the closed ball only. Admissibility is assembled in `VariationalTest.lean:56 thinProfile_admissible`.

**Determinant** — `ThinDeterminant.lean:72 thinProfile_determinant_bound` (hm : 1 ≤ m): `mooreDet ≤ 4·6^(m-1)·(η²/N^(m+1) + 1/(D·N^(m-1)) + ‖x‖²/(D²·N^(m-1)))`, via `Moore/RankTwoBound.lean:122 mooreDet_rankTwo_bound` and `N ≤ D` on the ball. `mooreDet` is a genuine def (`Moore/Basic.lean:144`).

**Energy bound** — `ThinEnergy.lean:24-26`:
```
theorem thinEnergy_le_log {m : ℕ} (hm : 1 ≤ m) {η : ℝ} (hη : 0 < η) (hη10 : η ≤ 1 / 10) :
    thinEnergy m η ≤ thinEnergyConstant m * Real.log (1 / η)
```
with `thinEnergy m η = ∫_{thinBall m} (−v)·mooreDet(Hess v)` (`EnergyIntegrability.lean:24-28`) and `thinEnergyConstant m = 1 + 4·6^(m-1)·(m·transverseVolume m)·spatialVolume m·(6+6m)` (`ThinEnergy.lean:16`). The constant depends only on m. Positivity: `thinEnergyConstant_pos` (:20). Proof chain: `thinEnergyDensity_le_majorant` (`EnergySlices.lean:42`) → radial integration in R^{2m} (`RadialVolume.lean:65`) → `EnergyKernels.lean:70 radial_energy_slice_le` → `thinSliceEnergy_le` (`EnergySlices.lean:71`) → Fubini `thinEnergy_eq_slices` (`EnergyFubini.lean:50`) → the spatial integral of `boundaryKernel`. Kernel algebra checked. Logarithms: one `log((η²+s)/η²) ≤ 6 log(1/η)` (`EnergyBoundary.lean:63`) and one from `∫₀¹ 1/(a+s) = log((a+1)/a)` (`BoundaryIntegrals.lean:31`); no second log is generated.

**m = 1 (planar case)**: `EnergyBoundary.lean:45 spatial_boundary_integral_log` needs `hm : 2 ≤ m` and is dead code. `ThinEnergy.lean:63` uses `EnergyBoundaryAllDimensions.lean:25 spatial_boundary_integral_log_of_one_le` (hm : 1 ≤ m), which keeps the radius variable, bounds `r^(m-1)·boundaryKernel(1−r²) ≤ 1 + 1/(η² + (1−r))` (`:41`), and integrates to `1 + log((η²+1)/η²) ≤ 6 log(1/η)`. Valid for every m ≥ 1. So the energy bound genuinely covers n = 2.

**"Negative scale exponent in transverse dimension one"**: `Packet/OutputScaling.lean:91 output_delta_power_real` (hm : 1 ≤ m): `δ^(3m)·δ^(4(2m+2))·(δ^(−10m))^(inputExponent m) = δ^((m:ℝ)−2)` (rpow, = δ^(−1) at m = 1), used by `output_lower_scaling_real` (:103), which `Packet/OutputSlice.lean:73` calls. The ℕ-exponent variants (hm : 2 ≤ m, `:51/:66`) are dead. Exponent bookkeeping checked: R = δ³/100, ε = δ⁴/1000, a = δ^(−10m)M gives δ^(m−2)·M^((m+1)/m) and log(R/ε) = log(10/δ) ≥ log(2/δ).

### 2. The logarithmic lower bound on thin sources

`ThinVariational.lean:102 thinSource_variational_lower`:
```
(hm : 1 ≤ m) (hη : 0 < η) (hη10 : η ≤ 1/10) (ha : 0 ≤ a)
(hμ : ContinuousOn μ (thinClosedBall m)) (hμ0 : ∀ z ∈ thinBall m, 0 ≤ μ z)
(hμa : ∀ z ∈ thinCore m η, a ≤ μ z) :
∃ v, ThinAdmissible v ∧ thinLowerConstant m * a^(((m:ℝ)+1)/m) * η^(2m+2) * log(1/η) ≤ thinFunctional μ v
```
`thinCore m η = ball 0 (1/2) ×ˢ ball 0 η` (`ThinSource.lean:16`); `thinFunctional μ f = ∫(−f)μ − determinantEnergy f/(m+1)` (`VariationalTest.lean:21`), matching J_μ in INFORMAL.md. Mechanism: `thinSource_integral_lower` (`ThinSource.lean:74`) and `thinEnergy_le_log`, both carrying `log(1/η)`, so the amplitude optimisation (`thinFunctional_lower :54`, `thinSource_test_power :72`) keeps the log. `thinLowerConstant m` (:19) depends only on m.

Scaled/positioned versions: `ScaledVariational.lean:92 thinSource_variational_lower_scaled` → `VariationalValue.lean:21 thinSource_value_lower_scaled` → `VariationalStructure.lean:174 thinSource_realValue_lower_scaled`. Rescaling exponents (`SpatialScaling.lean:122`) are dimensionally consistent.

**Discharge downstream**: `VariationalLocalization.lean:99`, `Packet/OutputLocalization.lean:64`, `Packet/OutputSlice.lean:65-73` (R = δ³/100, ε = δ⁴/1000, so ε ≤ R/10 ⇔ δ ≤ 10), feeding `SharpTheorem.lean:17 sharpTubeBound_of_two_le (hn : 2 ≤ n)` with m = n−1. The packet-density hypotheses inside OutputSlice/OutputLocalization were not verified by this sub-review.

### 3. Unnatural / hard hypotheses
None found in scope. `η ≤ 1/10` is a fixed threshold, satisfied downstream as η = δ/100. No hypothesis forces μ ≡ 0; all constants are proved positive.

### 4. Docstring vs statement
- INFORMAL.md says admissibility means "smoothness near the closed ball"; the Lean predicate `ThinAdmissible` (`VariationalTest.lean:24`) requires only `ContDiffAt ℝ 3`. Harmless for the lower bound; the trace side is proven for this C³ class (see sub-review B).
- `ScaledVariational.lean:91` docstring "A smooth admissible test": witness is C^∞, predicate records C³. Cosmetic.

### 5. Red-flag scan
In the 18 in-scope files: no `axiom`, `sorry`, `native_decide`, `unsafe`, `implemented_by`, `opaque`, `extern`, `instance`, `admit`. Only `set_option maxHeartbeats` (`EnergyBoundaryAllDimensions.lean:13`). Whole `KakeyaSharp/` + bridges: only `instance` is `Definitions.lean:24 sphereMeasure_isFinite`; `sorry` only in `Challenge.lean:42,56`.

### Minor observations
Dead code with stricter `2 ≤ m` hypotheses (`spatial_boundary_integral_log`, `spatial_log_integral`, `output_lower_scaling`/`output_delta_power`, `thinEnergy_log_bound`) could mislead a reader into thinking n = 2 is excluded; the live chain uses the `1 ≤ m` versions throughout.

---

## B. Trace, input, propagation, output chain

### 1. The five trace theorems (all hypotheses discharged downstream)

**`thinDet_smooth_comparison`** — `KakeyaSharp/Trace/Comparison.lean:104-112`: for `0 < R`, `u v` `ContDiff ℝ 3`, `χ` `ContDiff ℝ 1` and `Monotone`, `χ (v z - u z) = 0` on the sphere, PSD quaternionic Hessians on the open ball: `∫ χ(v-u)·mooreDet(Hess v) ≤ ∫ χ(v-u)·mooreDet(Hess u)` over `thinBallAt R o`. Proof via `hasDerivAt_weighted_thinDet` (:19) and `thinCofactor_composition_nonpos` (:90). Used only by `thinDet_sublevel_bound` (Sublevel.lean:69).

**`thinDet_sublevel_bound`** — `Trace/Sublevel.lean:34-43`: `(t/H)^m * ∫ (if 3t < -u then det Hess φ else 0) ≤ ∫ (if t < -u then det Hess u else 0)`. Used at Estimate.lean:63. The three pointwise facts (χ=0 on boundary; χ=1 on {3t<−u}; det Hess w = (t/H)^m det Hess φ) checked.

**`ThinAdmissibleAt.trace_bound`** — `Trace/Estimate.lean:123-130`: `∫ (-u)^(m+1) * det Hess φ ≤ thinTraceConstant m * H^m * determinantEnergyAt R o u`, `thinTraceConstant m = 3^(m+1)(m+1)` (:21). Layer-cake arithmetic checked (`LayerCake.lean:17`). `u ≤ 0` from `hu.nonpos hm hR` (maximum principle; uses `1 ≤ m`). One-sided limit H+ε→H. Used at Weighted.lean:90.

**`thinValueRealAt_weighted_bound`** — `Trace/Weighted.lean:131-142`: `thinValueRealAt R o ρ ≤ thinWeightedConstant m * H * ∫ (b z)^((m+1)/m) * det Hess φ`, `thinWeightedConstant m = m/(m+1)·(3^{m+1}(m+1))^{1/m}` (:20). Uses `thinValueRealAt_le` (VariationalStructure.lean:42, needs `thinVariationalValueAt_finite`, so `toReal` is not a trivial 0) and Young (`A·K_m H^m E = E/(m+1)` cancels exactly). Used at InputBarrier.lean:187.

**`inputBarrier_value_le_log`** — `Packet/InputBarrier.lean:219-228`: `thinValueRealAt R 0 μ ≤ (thinWeightedConstant m * inputLogConstant R) * Real.log (2/δ) * ∫ (w z)^((m+1)/m) * (8^m δ^4/(δ^4+inputQuadratic a b z)^(m+1))`. Barrier `inputBarrier h R a b = log(h+q_0) − log(h+2R^2)` (:125); determinant `8^m h/(h+q_0)^{m+1}` (:148, via `LogBarrier.lean:95`, `Hess q_0 = 8·I` (:63), `|G q_0|^2 = 8 q_0` (:99)). Height `inputBarrier_height_le_log` (:201): `log((δ^4+2R^2)/δ^4) ≤ (4 + log(1+2R^2)/log 2)·log(2/δ)`, arithmetic checked. Used at InputEstimate.lean:141.

### 2. Input estimate
`kakeyaPacketFamily_input_estimate` — `Packet/InputEstimate.lean:124-132`: `thinValueRealAt R 0 (thinSlice (currentDensity (kakeyaPacketFamily δ a v weights)) p) ≤ inputEstimateConstant m A R * Real.log (2/δ) * δ^m * ∑ l, (weights l)^(inputExponent m)`. The single `log(2/δ)` enters only through the barrier height with `h = δ^4`. The weighted integral (`kakeya_input_weighted_integral_le`, :90) gives `inputIntegralConstant m A * δ^m * Σ w^q` with no log. Constant (:25-30) depends only on `m, A, R`; R is later fixed to `propagationOuterRadius A V`. Domination: `kakeyaPacketFamily_input_domination` (InputDomination.lean:81); `∫ w^q ≤ (8^m)^{q−1} 3^m |B^m_1| δ^m Σ w_l^q` is `directionWeight_rpow_integral_le` (DirectionIntegral.lean:128) using `direction_cap_card_le`.

### 3. Propagation step
- Smooth: `Propagation.exists_singleLog_cylinder_constant` (SingleLog.lean:43-49): `∫_1^2∫_0^{2π} f ≤ C(1+|log ρ|) f(cylinderPoint 0 1 θ)` for `0<ρ<1`, f smooth, nonnegative, superharmonic on `cylinderDomain ρ`. Exactly one log loss. Imports OAI `cylinderAverage_logarithmic_lower_on`, `cylinderTimeTrace_le_average_on`.
- Weak: `exists_weak_singleLog_cylinder_constant` (WeakSingleLog.lean:78-84): f only `ContinuousOn Ω`, `Green.WeakSuperharmonicOn Ω f`. Removal of smoothness via `exists_local_superharmonic_approximation` (LocalApproximation.lean:19), `mollified_laplacian_nonpos` (Mollifier.lean:74), `cylinderTrace_tendsto` (WeakSingleLog.lean:43), two dominated-convergence applications.
- Application: `exists_kakeyaPacketFamily_propagation_constant` (Packet/Propagation.lean:20-30) and `exists_kakeyaPacketFamily_output_upper_constant` (:63-73) at `ρ = δ^4` with `propagationLog_le`: `1+|log δ^4| ≤ 6 log(2/δ)`, giving **`C·log(2/δ)^2·δ^m Σ w^q`**.
- NOT verified: `kakeyaPacketFamily_propagation_weakSuperharmonic` (PropagationDomain.lean:75) reduces to `unitPacketFamily_weakSuperharmonic` (Packet/Smooth/Dirichlet chain). This is the real analytic input of propagation; its discharge chain exists but was not audited.

### 4. Output scaling and log recovery
- `outputDensityScale m δ = outputDensityConstant m · δ^{−10m}` (OutputScaling.lean:22).
- `output_delta_power_real` (:89, `1 ≤ m`): exponent 3m+8m+8−10m−10 = m−2, real rpow. ℕ-variant (`2 ≤ m`) unused downstream.
- `output_lower_scaling_real` (:100): `outputLowerConstant m r₀ ε₀ · δ^{m−2} · M^q · log(r₀/(ε₀δ))`.
- Log recovery: `thinSource_realValue_lower_scaled` (VariationalStructure.lean:174) with `r₀=1/100, ε₀=1/1000` (OutputSlice.lean:17-18) gives `log(10/δ) ≥ log(2/δ)` (OutputSlice.lean:79). Summed over disjoint balls by `thinValueRealAt_localized_thin_lower` (VariationalLocalization.lean:89) → `kakeyaPacketFamily_localized_output_lower` (OutputLocalization.lean:53).
- Time change: `kakeyaPacketFamily_output_slice_lower` (OutputSlice.lean:23-32) has `δ^2 · δ^{(m:ℝ)−2} = δ^m`; `kakeyaPacketFamily_output_integral_lower` (NormalizedTubes.lean:23-31), interval [1,1+δ^2] ⊆ [1,2].
- Cancellation: `exists_normalizedTube_constant` (NormalizedTubes.lean:87-95): `2π c_m log(2/δ) · normalizedTubeMoment δ ≤ C log(2/δ)^2 δ^m Σw^q`, divided by `log(2/δ) > 0` (requires `δ<1`).
- **Log count:** input +1, propagation +1 (= log²), output lower bound +1 on the left; net **log(2/δ)^1** at `exists_normalizedTube_constant`, preserved by `exists_enlargedGraphTube_constant` (EnlargedGraphTubes.lean:20-28), whose constant is `J^{q−1}·J·C` with J a fixed 1/64-net size (dimension only), A replaced by 2A+8.

### 5. Exponent `inputExponent m = (m+1)/m`
Defined InputEstimate.lean:18; `inputExponent_ge_one` (:20) needs `1 ≤ m`. Young (`thin_scaled_young`, Weighted.lean:28) uses `HolderConjugate (m+1) ((m+1)/m)` valid for all `m ≥ 1`. For m = 1, q = 2 is treated by the same real-exponent code.

### 6. δ-dependence of hypotheses
- Input: `δ ≤ 1`. Propagation at `ρ = δ^4`: needs `δ < 1` (strict). `exists_normalizedTube_constant` and `exists_enlargedGraphTube_constant` assume `δ < 1`.
- Closed range: `Packet/GraphEndpoint.lean`: `normalizedTubeMoment_coarse_bound` (:44) for `1/2 ≤ δ ≤ 1` via `N ≤ 8^m` packing and `log 2 ≤ log(2/δ)`; `exists_globalGraphTube_closedScale_constant` (:82) does `by_cases δ < 1`. Uniform over `0 < δ ≤ 1`.
- The only other scale constraint is `|v_l|^2 ≤ 1/16`, supplied by the chart reduction (sub-review C).

### 7. Red-flag scan
In scope (Trace/*, Packet/*, Propagation/*): no `axiom`, `sorry`, `native_decide`, `unsafe`, `implemented_by`, `opaque`, `admit`, no `instance` declarations, no `set_option` other than `maxHeartbeats`/`synthInstance.maxHeartbeats`. One local `let : IsAddHaarMeasure` inside a proof (Comparison.lean:52) — harmless.

### Could not determine
- Actual axiom footprint (no build in this sub-review; see main review).
- Correctness of upstream pieces relied on here: `unitPacketFamily_weakSuperharmonic`, `thinSource_variational_lower_scaled` (sub-review A), `thinValueRealAt_localization`, OAI cylinder lemmas' proofs, and the chart/rotation reduction (sub-review C).

No semantic defects found in the reviewed chain: constants depend only on `m, A, R(A,V)` (then dimension), the log power is exactly 1 at `exists_enlargedGraphTube_constant`, and no definition makes a quantity trivially zero or infinite (finiteness of the EReal value is proved before `toReal` is used in both directions).

---

## C. Chart and tube chain

### Chain
`Solution.lean:48 sharpTubeBound` → `KakeyaSharp/SharpTheorem.lean:17 sharpTubeBound_of_two_le` (n = m+1, `inputExponent m = (m+1)/m` ≡ `overlapExponent n`, `δ^m` ≡ `δ^(n-1)`) → `AllDirectionTubes.lean:47 exists_allDirectionTube_constant` → `GlobalChartTubes.lean:17 exists_globalChartTube_constant` → `ChartTubes.lean:107 exists_chartTube_constant` → `ChartTubes.lean:74 exists_chart_graph_window_constant` → `Packet/BroadGraphTubes.lean:79` → `:46` → `Packet/GraphEndpoint.lean:82` → `Packet/GlobalGraphTubes.lean:17` → `Packet/EnlargedGraphTubes.lean:20` → `Packet/NormalizedTubes.lean:87 exists_normalizedTube_constant` → PDE/packet core (sub-review B).

### 1. `exists_finite_direction_charts` (`DirectionCharts.lean:24`)
`∃ (J : ℕ) (R : Fin J → Space (m+1) ≃ₗᵢ[ℝ] Space (m+1)), ∀ v, ‖v‖=1 → ∃ j, dist (R j v) (north m) ≤ 1/16`. J comes from `unit_sphere_finite_separated_net (n := m+1) (1/16)`, chosen before N, δ, v, c, weights: **J depends only on m**. Each chart covers the cap `{v : ‖v‖=1, dist v (b j) ≤ 1/16}`; `R j = chartRotation (b j)` = reflection sending `b j ↦ north`. Every unit vector is covered. Rotations preserve tubes exactly (`rotated_tube_preimage`, :36), integrals, norms and separation. In `AllDirectionTubes.lean:61–83` each tube is assigned an `owner` chart, Hölder gives `(J+1)^(q-1)`, each class is rotated and reindexed. No restriction remains.

### 2. `exists_globalChartTube_constant` (`GlobalChartTubes.lean:17`)
Hypotheses: `1 ≤ m`, `0<δ≤1`, `‖v l‖=1`, `dist (v l) (north m) ≤ 1/16`, separation, weights ≥ 0; centers unrestricted. Constant `tubeGroupFactor (m+1) q * C_chart`, `tubeGroupFactor n q = (8^n)^(q-1)`.

Bounded-center removal: a 2-separated net `b` of `range c`; `weightedTubeOverlap_group_near` (`TubeGroups.lean:87`): a point of a group-j tube is within `2 + (2δ + 1/2) ≤ 6` of `b j` (uses `tube_subset_ball`, so **end caps are included**). `direction_cap_card_le` (`Packet/DirectionPacking.lean:35`) bounds groups touching any point by `8^(m+1)`. Each group is translated by `−b j` exactly; new centers have norm ≤ 2, head coordinate in `[-2,2]`, the hypothesis of `exists_chartTube_constant`. J depends on the centers but the constant does not.

Euclidean tube ⊆ graph tube (`weightedTubeOverlap_power_le_window`, `ChartTubes.lean:35`): `(Σ a_l 1_{tube(2δ)})^q ≤ powerWindow (256δ) intercept slope w (-5) 5 (coordinates y)`; `sliceOverlap r` counts `l` with `dist x (graphAxis (a l) (v l) t) ≤ r/64`, so radius `256δ/64 = 4δ`. `tube_near_north_in_graph` (`GraphTubeGeometry.lean:64`): for `y ∈ tube (2δ) v c`, `dist v north ≤ 1/16`, `c₀∈[-2,2]`, δ≤1: `y₀ ∈ [-5,5]` (caps inside the time window) and transverse error `< 5δ/2 ≤ 4δ`. The full open Euclidean tube including caps is inside the graph tube. `coordinates` is measure preserving (`GraphCoordinates.lean:69`).

Radius bookkeeping, all compensated by fixed constants: 2δ → graph 4δ (containment); `exists_chart_graph_window_constant` at scale `δ/2`, `log(2/(δ/2)) ≤ 2 log(2/δ)`, constant `20·C`; 512δ → 128δ via a fixed 1/64-net, constant `J^(q-1)·J·C`; spatial localization of intercepts (`Packet/SpatialLocalization.lean`, factor `(8^m)^(q-1)`), Σa² ≤ 4; `exists_enlargedGraphTube_constant` 128δ → δ by another fixed net, Σa² ≤ 2A+8 = 16. None depends on δ, N, weights, centers.

### 3. Direction separation
Euclidean `δ ≤ dist (v i) (v j)` on unit vectors is kept through rotation and spatial grouping, then converted once in `slope_separated` (`GraphSlopes.lean:101`): `δ/2 ≤ dist (slope (v i)) (slope (v j))`, via `direction_dist_le_slope_dist` (:65) `dist v w ≤ 2·dist (slope v) (slope w)`. Uniform factor 2; slope bound `Σ slope² ≤ 1/16` (`slope_sq_sum_of_near_north`) matches the packet hypothesis.

### 4. Large-scale range
`exists_globalGraphTube_closedScale_constant` (`GraphEndpoint.lean:82`) splits `δ<1` from `δ=1` (`normalizedTubeMoment_coarse_bound`, :44, valid for `1/2 ≤ δ ≤ 1`, N ≤ 8^m, `log 2 ≤ log(2/δ)`); constant `coarseGraphConstant m` dimension-only. In the Euclidean chain the packet scale is δ/2 ≤ 1/2, so the coarse branch is only needed for the module's own generality. Uniform.

### 5. `weightedTubeOverlap` / `weightedTubeMoment_rotation`
`ChartTubes.lean:20`: `weightedTubeOverlap δ v c weights y = ∑ l, (tube (2*δ) (v l) (c l)).indicator (fun _ => weights l) y`, with `tube` = `KakeyaSharp.tube` of `Definitions.lean:32`. Radius factor 2 matches `SharpTubeBound` exactly; `SharpTheorem.lean:25` unfolds it by `simpa only`. `weightedTubeMoment_rotation` (`TubeReindex.lean:65`) correct. `Solution.lean` restates `tube`, `kakeyaMaximal`, `sphereMeasure` verbatim and closes by `change`, so definitional agreement with `KakeyaSharp` is kernel-checked.

### 6. Red-flag scan (whole repo outside `.lake`)
- `sorry`: only `Challenge.lean:42,56`. Nothing imports `Challenge`.
- `axiom`, `native_decide`, `unsafe`, `implemented_by`, `opaque`, `extern`, `partial`: none (word hits only in doc comments / lemma names). `decide` only on `Fin`/`Perm` facts.
- Global `instance`s: `Definitions.lean:24 sphereMeasure_isFinite` (benign); in vendored `OAI/...` several instances on Hölder spaces and lattices (new structures, not overriding Mathlib instances on standard types, as far as names indicate). Not inspected in depth.
- `set_option`: only `maxHeartbeats` (≤ 1000000).

### Could not determine
- Everything below `exists_normalizedTube_constant` (sub-review B covers the statements; the PDE value function `kakeyaPacketFamily = unitPacketFamily (δ²) (δ⁴) …` was not reviewed).
- `SharpTransfer.lean` beyond its statement (the main reviewer read it in full).

Net: in the chart/tube layer no semantic gap — tubes are the exact Euclidean radius-2δ tubes with caps, separation is unit-vector separation converted by a uniform factor 2, all centers and all directions are covered, and all constants depend only on m.
