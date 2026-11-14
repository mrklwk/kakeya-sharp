/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp
public import KakeyaSharp.ThinProfile

@[expose] public section

-- The earlier conditional transfer; unconditional n >= 3 theorems appear below.
#check KakeyaSharp.sharpMaximal_of_sharpTube
#print KakeyaSharp.SharpTubeBound
#print KakeyaSharp.SharpMaximalBound
#print axioms KakeyaSharp.sharpMaximal_of_sharpTube
#print axioms KakeyaSharp.thinProfile_core_depth
#print axioms KakeyaSharp.thinProfile_smooth
#print axioms KakeyaSharp.radial_kernel_integral_le
#print axioms KakeyaSharp.weighted_log_kernel_integral_le

-- Actual derivatives and the signed Pfaffian-defined Moore determinant.
#check KakeyaSharp.thinProfile_quaternionHessian
#check KakeyaSharp.thinProfile_quaternionHessian_positive
#check KakeyaSharp.thinProfile_determinant_bound
#print axioms KakeyaSharp.thinProfile_hessian
#print axioms KakeyaSharp.thinProfile_quaternionHessian
#print axioms KakeyaSharp.thinProfile_quaternionHessian_positive
#print axioms KakeyaSharp.Moore.mooreDet_scalar_outer
#print axioms KakeyaSharp.Moore.mooreDet_rankTwo_bound
#print axioms KakeyaSharp.thinHessianBase_determinant
#print axioms KakeyaSharp.thinProfile_determinant_bound
#print axioms KakeyaSharp.boundary_kernel_integral_log

-- The actual volume integral, amplitude optimization, and spatial scaling.
#check KakeyaSharp.thinEnergy_le_log
#check KakeyaSharp.thinSource_variational_lower_scaled
#check KakeyaSharp.thinSource_value_lower_scaled
#print KakeyaSharp.ThinAdmissibleAt
#print KakeyaSharp.thinVariationalValueAt
#print axioms KakeyaSharp.integral_ball_norm_sq_even
#print axioms KakeyaSharp.thinEnergyDensity_integrableOn
#print axioms KakeyaSharp.thinEnergy_eq_slices
#print axioms KakeyaSharp.thinEnergy_le_log
#print axioms KakeyaSharp.thinEnergyConstant_pos
#print axioms KakeyaSharp.determinantEnergy_smul
#print axioms KakeyaSharp.thinSource_variational_lower
#print axioms KakeyaSharp.integral_rescale
#print axioms KakeyaSharp.determinantEnergyAt_rescale
#print axioms KakeyaSharp.ThinAdmissibleAt.energy_integrableOn
#print axioms KakeyaSharp.ThinAdmissibleAt.source_integrableOn
#print axioms KakeyaSharp.thinLowerConstant_pos
#print axioms KakeyaSharp.thinSource_variational_lower_scaled
#print axioms KakeyaSharp.thinSource_value_lower_scaled

-- Actual cofactor, divergence, zero-boundary Green identity, and first variation.
#check KakeyaSharp.thinCofactor_divergence
#check KakeyaSharp.thinCofactor_selfAdjoint
#check KakeyaSharp.hasDerivAt_determinantEnergyAt
#check KakeyaSharp.hasDerivAt_thinFunctionalAt
#check KakeyaSharp.thinFunctional_stationary_of_detEquation
#print axioms KakeyaSharp.Moore.mooreCofactor_pairing
#print axioms KakeyaSharp.Moore.mooreCofactor_fderiv_outer_vecMul
#print axioms KakeyaSharp.QuaternionAlgebra.mooreCofactor_directionalHessian_divergence
#print axioms KakeyaSharp.Green.integral_directional_by_parts_zero_boundary
#print axioms KakeyaSharp.Green.moore_cofactor_green_bounded
#print axioms KakeyaSharp.thinBallAt_null_frontier
#print axioms KakeyaSharp.thinCofactor_divergence
#print axioms KakeyaSharp.thinCofactor_euler
#print axioms KakeyaSharp.thinCofactor_selfAdjoint
#print axioms KakeyaSharp.thinEnergy_linearization
#print axioms KakeyaSharp.hasDerivAt_setIntegral_compact
#print axioms KakeyaSharp.hasDerivAt_determinantEnergyAt
#print axioms KakeyaSharp.hasDerivAt_thinFunctionalAt
#print axioms KakeyaSharp.thinFunctional_stationary_of_detEquation

-- Positivity, concavity, the full admissible class, and unconditional finiteness.
#check KakeyaSharp.ThinAdmissibleAt.supporting_inequality
#check KakeyaSharp.thinVariationalValueAt_PDE_representation
#check KakeyaSharp.thinVariationalValueAt_finite
#check KakeyaSharp.thinValueRealAt_smul
#check KakeyaSharp.thinSource_realValue_lower_scaled
#print axioms KakeyaSharp.Moore.mooreDet_pos_of_complexify_posDef
#print axioms KakeyaSharp.Moore.mooreDifferential_nonneg_of_posSemidef
#print axioms KakeyaSharp.Moore.mooreCofactor_posSemidef
#print axioms KakeyaSharp.Moore.mooreCofactor_quaternionForm_nonneg
#print axioms KakeyaSharp.Green.realCoefficients_quadratic
#print axioms KakeyaSharp.thinCofactor_energy_identity
#print axioms KakeyaSharp.thinCofactor_energy_nonneg
#print axioms KakeyaSharp.hasDerivAt_thinFunctionalAt_line
#print axioms KakeyaSharp.hasDerivAt_thinLineDerivative
#print axioms KakeyaSharp.thinFunctional_concave_line
#print axioms KakeyaSharp.exists_global_C3_extension
#print axioms KakeyaSharp.ThinAdmissibleAt.supporting_inequality
#print axioms KakeyaSharp.ThinAdmissibleAt.maximizes_of_detEquation
#print axioms KakeyaSharp.thinVariationalValueAt_PDE_representation
#print axioms KakeyaSharp.thinQuadraticAt_hessian
#print axioms KakeyaSharp.ThinAdmissibleAt.nonpos
#print axioms KakeyaSharp.thinFunctionalAt_le_constant_quadratic
#print axioms KakeyaSharp.thinVariationalValueAt_finite
#print axioms KakeyaSharp.coe_thinValueRealAt
#print axioms KakeyaSharp.thinValueRealAt_mono
#print axioms KakeyaSharp.thinValueRealAt_smul
#print axioms KakeyaSharp.thinValueRealAt_convex
#print axioms KakeyaSharp.thinValueRealAt_relative_stability
#print axioms KakeyaSharp.thinSource_realValue_lower_scaled

-- Source regularization and the current calculus; solution families remain explicit proof work.
#check KakeyaSharp.thinValueRealAt_lipschitz_bound
#check KakeyaSharp.thinValueRealAt_regularization
#check KakeyaSharp.thinCofactor_three_pairings
#check KakeyaSharp.current_double_conservation
#check KakeyaSharp.thinCurrent_energy_le_stress
#print axioms KakeyaSharp.thinValueRealAt_lipschitz_bound
#print axioms KakeyaSharp.thinValueRealAt_regularization
#print axioms KakeyaSharp.Green.quaternion_hessian_contraction
#print axioms KakeyaSharp.Green.quaternion_current_pairing_bounded
#print axioms KakeyaSharp.Green.moore_cofactor_pairing_bounded
#print axioms KakeyaSharp.thinCofactor_tested_pairing
#print axioms KakeyaSharp.thinCofactor_three_pairings
#print axioms KakeyaSharp.Current.double_conservation
#print axioms KakeyaSharp.realColumnConservation_of_strong
#print axioms KakeyaSharp.current_mass_conservation
#print axioms KakeyaSharp.current_momentum_conservation
#print axioms KakeyaSharp.current_double_conservation
#print axioms KakeyaSharp.Green.integral_directional_by_parts_bounded
#print axioms KakeyaSharp.Green.integral_second_derivative_transfer
#print axioms KakeyaSharp.current_square_identity
#print axioms KakeyaSharp.current_square_nonneg
#print axioms KakeyaSharp.thinParameterGradient_flux
#print axioms KakeyaSharp.thinCofactor_cross_pairing
#print axioms KakeyaSharp.thinCurrent_energy_le_stress

-- Actual parameter derivatives and the conditional Laplacian estimate for the supremum.
#check KakeyaSharp.thinSolution_linearized
#check KakeyaSharp.thinSolution_current_energy
#check KakeyaSharp.hasDerivAt_thinValueRealAt_parameter
#check KakeyaSharp.hasDerivAt_thinValueRealAt_parameter_deriv
#check KakeyaSharp.thinValueRealAt_current_laplacian_nonpos
#print axioms KakeyaSharp.Calculus.secondDerivative_slice_right
#print axioms KakeyaSharp.Calculus.secondDerivative_directionalDerivative
#print axioms KakeyaSharp.Calculus.fderiv_directionalHessian_apply
#print axioms KakeyaSharp.fderiv_mooreDet_apply
#print axioms KakeyaSharp.thinSolution_linearized
#print axioms KakeyaSharp.thinParameterDerivative_boundary
#print axioms KakeyaSharp.thinSolution_current_law
#print axioms KakeyaSharp.thinSolution_current_energy
#print axioms KakeyaSharp.hasDerivAt_thinParameterIntegral
#print axioms KakeyaSharp.thinSolution_source_linearization
#print axioms KakeyaSharp.hasDerivAt_thinValueRealAt_parameter
#print axioms KakeyaSharp.hasDerivAt_thinValueRealAt_parameter_deriv
#print axioms KakeyaSharp.thinValueRealAt_parameter_curvature
#print axioms KakeyaSharp.Green.integral_double_divergence_transfer
#print axioms KakeyaSharp.thinCurrent_stress_transfer
#print axioms KakeyaSharp.thinValueRealAt_current_laplacian_nonpos

-- Joint parameter regularity, the usual Laplacian, and the positive-source limit.
#print KakeyaSharp.Green.WeakSuperharmonicOn
#check KakeyaSharp.thinValueRealAt_contDiff_two_of_solution
#check KakeyaSharp.thinValueRealAt_current_weakSuperharmonic
#check KakeyaSharp.thinValueRealAt_weakSuperharmonic_regularization
#check KakeyaSharp.thinValueRealAt_current_weakSuperharmonic_of_regularized_solutions
#print axioms KakeyaSharp.continuous_setIntegral_compact
#print axioms KakeyaSharp.hasFDerivAt_setIntegral_compact
#print axioms KakeyaSharp.contDiff_two_setIntegral_compact
#print axioms KakeyaSharp.Green.laplacian_space_eq_sum
#print axioms KakeyaSharp.Green.secondDeriv_line
#print axioms KakeyaSharp.Green.integral_laplacian_test
#print axioms KakeyaSharp.Green.weakSuperharmonicOn_of_laplacian_nonpos
#print axioms KakeyaSharp.thinValueRealAt_contDiff_two_of_solution
#print axioms KakeyaSharp.thinValueRealAt_current_weakSuperharmonic
#print axioms KakeyaSharp.Green.weakSuperharmonicOn_of_tendsto
#print axioms KakeyaSharp.thinValueRealAt_weakSuperharmonic_regularization
#print axioms KakeyaSharp.regularizedCurrent_isHermitian
#print axioms KakeyaSharp.currentDensity_regularized
#print axioms KakeyaSharp.currentFlux_regularized
#print axioms KakeyaSharp.currentStress_regularized
#print axioms KakeyaSharp.regularizedCurrent_conservation
#print axioms KakeyaSharp.regularizedCurrent_mass
#print axioms KakeyaSharp.currentDensity_regularized_pos
#print axioms KakeyaSharp.regularizedCurrent_flux
#print axioms KakeyaSharp.regularizedCurrent_stress
#print axioms KakeyaSharp.thinValueRealAt_current_weakSuperharmonic_of_regularized_solutions

-- Local current equations, local smooth representatives, and the local weak limit.
#check KakeyaSharp.thinValueRealAt_current_weakSuperharmonic_of_local_smoothness
#check KakeyaSharp.thinValueRealAt_current_weakSuperharmonic_of_local_regularized_solutions
#print axioms KakeyaSharp.exists_global_contDiff_extension
#print axioms KakeyaSharp.exists_global_contDiff_extension_near_slice
#print axioms KakeyaSharp.Current.double_conservation_on
#print axioms KakeyaSharp.current_mass_conservation_on
#print axioms KakeyaSharp.current_momentum_conservation_on
#print axioms KakeyaSharp.current_double_conservation_on
#print axioms KakeyaSharp.thinSolution_linearized_on
#print axioms KakeyaSharp.thinParameterDerivative_boundary_on
#print axioms KakeyaSharp.thinSolution_source_linearization_on
#print axioms KakeyaSharp.hasDerivAt_thinValueRealAt_parameter_on
#print axioms KakeyaSharp.hasDerivAt_thinValueRealAt_parameter_deriv_on
#print axioms KakeyaSharp.thinValueRealAt_parameter_curvature_on
#print axioms KakeyaSharp.thinSolution_current_law_on
#print axioms KakeyaSharp.thinSolution_current_energy_on
#print axioms KakeyaSharp.thinCurrent_stress_transfer_on
#print axioms KakeyaSharp.thinValueRealAt_current_laplacian_nonpos_on
#print axioms KakeyaSharp.Green.secondDeriv_line_of_contDiffAt
#print axioms KakeyaSharp.Green.weakSuperharmonicOn_of_contDiffOn_laplacian_nonpos
#print axioms KakeyaSharp.thinValueRealAt_contDiffOn_two_of_solution
#print axioms KakeyaSharp.thinValueRealAt_current_weakSuperharmonic_on
#print axioms KakeyaSharp.regularizedCurrent_conservation_on
#print axioms KakeyaSharp.thinValueRealAt_current_weakSuperharmonic_of_regularized_solutions_on
#print axioms KakeyaSharp.ThinAdmissibleAt.congr_nhds
#print axioms KakeyaSharp.thinValueRealAt_congr_source
#print axioms KakeyaSharp.RealColumnConservationOn.congr_nhds
#print axioms KakeyaSharp.thinValueRealAt_current_local_regular
#print axioms KakeyaSharp.thinValueRealAt_current_weakSuperharmonic_of_local_smoothness
#print axioms KakeyaSharp.Green.weakSuperharmonicOn_of_tendsto_on
#print axioms KakeyaSharp.thinValueRealAt_weakSuperharmonic_regularization_on
#print axioms KakeyaSharp.thinValueRealAt_current_weakSuperharmonic_of_local_regularized_solutions

-- Explicit packet phase, transport, orientation algebra, local smoothness and cutoff.
#print axioms KakeyaSharp.Packet.center_equations
#print axioms KakeyaSharp.Packet.scalarEnergy_gap
#print axioms KakeyaSharp.Packet.scalarEnergy_eq_phase_iff
#print axioms KakeyaSharp.Packet.scalarPhase_completed_square
#print axioms KakeyaSharp.Packet.energy_gap
#print axioms KakeyaSharp.Packet.phase_unique_minimizer
#print axioms KakeyaSharp.Packet.phase_completed_square
#print axioms KakeyaSharp.Packet.phase_controls_deviations
#print axioms KakeyaSharp.Packet.column_phase_tangency
#print axioms KakeyaSharp.Packet.column_sandwich
#print axioms KakeyaSharp.Packet.column_commutator
#print axioms KakeyaSharp.Packet.column_mixed_product
#print axioms KakeyaSharp.Packet.column_phaseGradient_tangency
#print axioms KakeyaSharp.Packet.hasDerivAt_center_curve
#print axioms KakeyaSharp.Packet.hasDerivAt_residual_curve
#print axioms KakeyaSharp.Packet.center_x
#print axioms KakeyaSharp.Packet.residual_x
#print axioms KakeyaSharp.Packet.center_alpha
#print axioms KakeyaSharp.Packet.residual_alpha
#print axioms KakeyaSharp.Packet.center_transport
#print axioms KakeyaSharp.Packet.residual_transport
#print axioms KakeyaSharp.Packet.hasDerivAt_energy_at_center
#print axioms KakeyaSharp.Packet.hasDerivAt_scalarPhase_curve
#print axioms KakeyaSharp.Packet.prefactor_pos
#print axioms KakeyaSharp.Packet.hasDerivAt_prefactor_curve
#print axioms KakeyaSharp.Packet.prefactor_tau
#print axioms KakeyaSharp.Packet.prefactor_s
#print axioms KakeyaSharp.Packet.columnContraction_outer
#print axioms KakeyaSharp.Packet.strongDivergence_smul
#print axioms KakeyaSharp.Packet.strongDivergence_cutoff_rankOne
#print axioms KakeyaSharp.Packet.realColumnConservationOn_cutoff_rankOne
#print axioms KakeyaSharp.Packet.physicalFrame_unit
#print axioms KakeyaSharp.Packet.physicalPhase_nonneg
#print axioms KakeyaSharp.Packet.rawPacket_isHermitian
#print axioms KakeyaSharp.Packet.rawPacket_density
#print axioms KakeyaSharp.Packet.rawPacket_flux
#print axioms KakeyaSharp.Packet.rawPacket_stress
#print axioms KakeyaSharp.Packet.rawPacket_density_nonneg
#print axioms KakeyaSharp.Packet.physicalPhase_contDiffAt
#print axioms KakeyaSharp.Packet.physicalColumn_contDiffAt
#print axioms KakeyaSharp.Packet.rawPacket_contDiffAt
#check KakeyaSharp.Packet.rawPacket_contDiffAt
#check KakeyaSharp.Packet.realColumnConservationOn_cutoff_rankOne

-- Actual physical packet conservation, support, finite families and scalar transfer.
#print axioms KakeyaSharp.Packet.hasDerivAt_radius_line
#print axioms KakeyaSharp.Packet.hasDerivAt_ratioRe_line
#print axioms KakeyaSharp.Packet.hasDerivAt_ratioIm_line
#print axioms KakeyaSharp.Packet.hasDerivAt_scalarPhysicalPhase_line
#print axioms KakeyaSharp.Packet.physicalPhase_fderiv
#print axioms KakeyaSharp.Packet.physicalPhase_gradient
#print axioms KakeyaSharp.Packet.physicalColumn_tangency
#print axioms KakeyaSharp.Packet.hasDerivAt_centers_line
#print axioms KakeyaSharp.Packet.hasDerivAt_residuals_line
#print axioms KakeyaSharp.Packet.hasDerivAt_physicalColumn_line
#print axioms KakeyaSharp.Packet.physicalColumn_fderiv
#print axioms KakeyaSharp.Packet.columnRate_eq_entryJet
#print axioms KakeyaSharp.Packet.spaceJet_divergence
#print axioms KakeyaSharp.Packet.entryJet_acceleration
#print axioms KakeyaSharp.Packet.physicalColumn_parameter_fderiv
#print axioms KakeyaSharp.Packet.physicalColumn_spatial_fderiv
#print axioms KakeyaSharp.Packet.physicalColumn_spatial_divergence
#print axioms KakeyaSharp.Packet.physicalColumn_acceleration
#print axioms KakeyaSharp.Packet.fderiv_smul_outer
#print axioms KakeyaSharp.Packet.strongDivergence_smul_outer
#print axioms KakeyaSharp.Packet.baseWeight_fderiv
#print axioms KakeyaSharp.Packet.baseWeight_parameter_divergence
#print axioms KakeyaSharp.Packet.physicalColumn_weighted_divergence
#print axioms KakeyaSharp.Packet.uncutPacket_strongDivergence
#print axioms KakeyaSharp.Packet.rawPacket_strongDivergence
#print axioms KakeyaSharp.Packet.rawPacket_realColumnConservationOn
#print axioms KakeyaSharp.Packet.phase_deviation_bounds
#print axioms KakeyaSharp.Packet.phase_controls_x_distance
#print axioms KakeyaSharp.Packet.phase_controls_ratio_distance
#print axioms KakeyaSharp.Packet.ratio_reconstruction
#print axioms KakeyaSharp.Packet.physical_transverse_distance
#print axioms KakeyaSharp.Packet.physicalPhase_controls_distance
#print axioms KakeyaSharp.Packet.rawPacket_ne_zero_phase_le
#print axioms KakeyaSharp.Packet.physicalPhase_controls_spatial_norm
#print axioms KakeyaSharp.Packet.rawPacket_eq_zero_of_supportBound
#print axioms KakeyaSharp.Packet.supportBound_uniform
#print axioms KakeyaSharp.Packet.packetFamily_contDiffAt
#print axioms KakeyaSharp.Packet.packetFamily_isHermitian
#print axioms KakeyaSharp.Packet.packetFamily_strongDivergence
#print axioms KakeyaSharp.Packet.packetFamily_realColumnConservationOn
#print axioms KakeyaSharp.Packet.packetFamily_density
#print axioms KakeyaSharp.Packet.packetFamily_flux
#print axioms KakeyaSharp.Packet.packetFamily_stress
#print axioms KakeyaSharp.Packet.familyWeights_nonneg
#print axioms KakeyaSharp.Packet.packetFamily_eq_zero_of_supportBound
#print axioms KakeyaSharp.Packet.packetFamily_weakSuperharmonic_of_regularized_solutions
#check KakeyaSharp.Packet.rawPacket_strongDivergence
#check KakeyaSharp.Packet.packetFamily_weakSuperharmonic_of_regularized_solutions

-- Checkpoint twelve: actual nonlinear existence, descent, parameter
-- families and packet scalar transfer without a supplied solution family.
#check KakeyaSharp.Dirichlet.exists_thinDirichletSolution
#check KakeyaSharp.Dirichlet.exists_thinVariational_maximizer
#check KakeyaSharp.Dirichlet.exists_thinDirichlet_family
#check KakeyaSharp.Packet.packetFamily_regularized_solution_family
#check KakeyaSharp.Packet.packetFamily_weakSuperharmonic
#print axioms OAI.Analysis.PDE.Dirichlet.exists_periodic_moore_dirichlet_C4
#print axioms OAI.Analysis.Fourier.WavePackets.exists_smooth_periodic_dirichlet_family
#print axioms KakeyaSharp.Dirichlet.hessian_lift
#print axioms KakeyaSharp.Dirichlet.defining_hessian_pos
#print axioms KakeyaSharp.Dirichlet.defining_regular
#print axioms KakeyaSharp.Dirichlet.exists_periodic_ball_C4
#print axioms KakeyaSharp.Dirichlet.solution_fourth_invariant
#print axioms KakeyaSharp.Dirichlet.invariant_hessian_descends
#print axioms KakeyaSharp.Dirichlet.exists_thin_ball_C4
#print axioms KakeyaSharp.Dirichlet.exists_thinDirichletSolution
#print axioms KakeyaSharp.Dirichlet.ThinDirichletSolution.maximizes
#print axioms KakeyaSharp.Dirichlet.ThinDirichletSolution.value_eq
#print axioms KakeyaSharp.Dirichlet.exists_thinVariational_maximizer
#print axioms KakeyaSharp.Dirichlet.descendBallSolution
#print axioms KakeyaSharp.Dirichlet.ballData_locallyTrivial
#print axioms KakeyaSharp.Dirichlet.exists_thinDirichlet_family
#print axioms KakeyaSharp.Dirichlet.thinBallAt_zero_closure
#print axioms KakeyaSharp.Dirichlet.thinHessian_eqOn_closed_of_eqOn
#print axioms KakeyaSharp.Dirichlet.exists_local_joint_representative
#print axioms KakeyaSharp.Packet.packetFamily_density_slice_smooth
#print axioms KakeyaSharp.Packet.packetFamily_density_nonneg
#print axioms KakeyaSharp.Packet.packetFamily_regularized_solution
#print axioms KakeyaSharp.Packet.packetFamily_regularized_solution_family
#print axioms KakeyaSharp.Packet.packetFamily_regularized_value_local_regular
#print axioms KakeyaSharp.Packet.packetFamily_weakSuperharmonic

-- Checkpoint thirteen: exact normalization and the fixed-domain Kakeya family.
#check KakeyaSharp.Packet.integral_packetWeight
#check KakeyaSharp.Packet.packetWeight_integrable
#check KakeyaSharp.Packet.integral_normalizedPacketFamily_density
#check KakeyaSharp.Packet.kakeyaPacketFamily_mass
#check KakeyaSharp.Packet.kakeyaPacketFamily_weakSuperharmonic
#check KakeyaSharp.Packet.kakeyaPacketFamily_value_continuous
#print axioms KakeyaSharp.Packet.unpack_measurePreserving
#print axioms KakeyaSharp.Packet.integral_unpack
#print axioms KakeyaSharp.Packet.det_shapeBlock
#print axioms KakeyaSharp.Packet.det_shapeMatrix
#print axioms KakeyaSharp.Packet.scalarPhase_affine
#print axioms KakeyaSharp.Packet.physicalPhase_packetAffine
#print axioms KakeyaSharp.Packet.prefactor_jacobian
#print axioms KakeyaSharp.Packet.packetAffine_map_volume
#print axioms KakeyaSharp.Packet.integral_packetAffine
#print axioms KakeyaSharp.Packet.integrable_packetAffine_iff
#print axioms KakeyaSharp.Packet.cutoff_packetSquare_integrable
#print axioms KakeyaSharp.Packet.cutoffMass_pos
#print axioms KakeyaSharp.Packet.integral_packetWeight
#print axioms KakeyaSharp.Packet.packetWeight_integrable
#print axioms KakeyaSharp.Packet.packetMass_pos
#print axioms KakeyaSharp.Packet.packetMass_kakeya_scale
#print axioms KakeyaSharp.Packet.integral_normalizedPacket_density
#print axioms KakeyaSharp.Packet.normalizedPacketFamily_density_integrable
#print axioms KakeyaSharp.Packet.integral_normalizedPacketFamily_density
#print axioms KakeyaSharp.Packet.normalizedPacketFamily_weakSuperharmonic
#print axioms KakeyaSharp.Packet.standardCutoff_smooth
#print axioms KakeyaSharp.Packet.standardCutoff_mass_pos
#print axioms KakeyaSharp.Packet.unitPacketFamily_mass
#print axioms KakeyaSharp.Packet.unitPacketFamily_weakSuperharmonic
#print axioms KakeyaSharp.Packet.kakeyaPacketFamily_mass
#print axioms KakeyaSharp.Packet.kakeyaPacketFamily_density_integrable
#print axioms KakeyaSharp.Packet.packetDomain_isOpen
#print axioms KakeyaSharp.Packet.supportBound_fixed_radius
#print axioms KakeyaSharp.Packet.kakeyaPacketFamily_eq_zero_outside
#print axioms KakeyaSharp.Packet.kakeyaPacketFamily_weakSuperharmonic
#print axioms KakeyaSharp.thinValueRealAt_continuousOn_parameter
#print axioms KakeyaSharp.Packet.kakeyaPacketFamily_value_continuous
#print axioms KakeyaSharp.Packet.kakeyaPacketFamily_value_nonneg

-- Checkpoint fourteen: comparison, weighted trace, and the actual input barrier.
#check KakeyaSharp.ThinAdmissibleAt.trace_bound
#check KakeyaSharp.thinValueRealAt_weighted_bound
#check KakeyaSharp.Packet.inputBarrier_determinant
#check KakeyaSharp.Packet.inputBarrier_value_le_log
#print axioms KakeyaSharp.hasDerivAt_weighted_thinDet
#print axioms KakeyaSharp.thinCofactor_composition_green
#print axioms KakeyaSharp.thinCofactor_composition_nonpos
#print axioms KakeyaSharp.thinDet_smooth_comparison
#print axioms KakeyaSharp.thinTraceConstant_pos
#print axioms KakeyaSharp.thinTrace_bound_global
#print axioms KakeyaSharp.ThinAdmissibleAt.trace_bound_of_pos
#print axioms KakeyaSharp.ThinAdmissibleAt.trace_bound
#print axioms KakeyaSharp.lintegral_moment_le_of_scaled_tails
#print axioms KakeyaSharp.withDensity_ofReal_apply_eq_integral_indicator
#print axioms KakeyaSharp.lintegral_withDensity_ofReal_eq_integral
#print axioms KakeyaSharp.thinQuaternionHessian_log
#print axioms KakeyaSharp.thinLogBarrier_smooth
#print axioms KakeyaSharp.thinLogBarrier_bounds
#print axioms KakeyaSharp.thinLogBarrier_hessian
#print axioms KakeyaSharp.thinLogBarrier_hessian_lower
#print axioms KakeyaSharp.thinLogBarrier_determinant
#print axioms KakeyaSharp.thinQuaternionHessian_sub_const
#print axioms KakeyaSharp.thinDet_nonneg
#print axioms KakeyaSharp.thinDet_sublevel_bound
#print axioms KakeyaSharp.thinWeightedConstant_pos
#print axioms KakeyaSharp.thin_scaled_young
#print axioms KakeyaSharp.ThinAdmissibleAt.weighted_functional_bound_of_pos
#print axioms KakeyaSharp.ThinAdmissibleAt.weighted_functional_bound
#print axioms KakeyaSharp.thinValueRealAt_weighted_bound
#print axioms KakeyaSharp.Packet.inputReal_direction
#print axioms KakeyaSharp.Packet.inputImag_direction
#print axioms KakeyaSharp.Packet.inputQuadratic_apply
#print axioms KakeyaSharp.Packet.inputQuadratic_nonneg
#print axioms KakeyaSharp.Packet.inputQuadratic_smooth
#print axioms KakeyaSharp.Packet.inputQuadratic_hessian
#print axioms KakeyaSharp.Packet.inputQuadratic_gradient
#print axioms KakeyaSharp.Packet.inputQuadratic_gradient_size
#print axioms KakeyaSharp.Packet.inputQuadratic_le
#print axioms KakeyaSharp.Packet.inputBarrier_smooth
#print axioms KakeyaSharp.Packet.inputBarrier_bounds
#print axioms KakeyaSharp.Packet.inputBarrier_positive
#print axioms KakeyaSharp.Packet.inputBarrier_determinant
#print axioms KakeyaSharp.Packet.inputQuadratic_eq_ratios
#print axioms KakeyaSharp.Packet.inputBarrier_value_bound
#print axioms KakeyaSharp.Packet.inputLogConstant_pos
#print axioms KakeyaSharp.Packet.inputBarrier_height_le_log
#print axioms KakeyaSharp.Packet.inputBarrier_value_le_log

-- Checkpoint fifteen: normalized weighted input and single-log smooth propagation.
#print axioms KakeyaSharp.Packet.normalMass_pos
#print axioms KakeyaSharp.Packet.inputIntegralConstant_pos
#print axioms KakeyaSharp.Packet.inputEstimateConstant_pos
#check KakeyaSharp.Packet.kakeyaPacketFamily_input_estimate
#check KakeyaSharp.Propagation.exists_singleLog_cylinder_constant
#print axioms KakeyaSharp.Packet.radius_eq_one_of_unit
#print axioms KakeyaSharp.Packet.phase_controls_input_normal
#print axioms KakeyaSharp.Packet.input_phase_support
#print axioms KakeyaSharp.Packet.input_cutoff_support
#print axioms KakeyaSharp.Packet.prefactor_input_le_one
#print axioms KakeyaSharp.Packet.standardCutoff_le_one
#print axioms KakeyaSharp.Packet.directionWeight_nonneg
#print axioms KakeyaSharp.Packet.inputDensityConstant_pos
#print axioms KakeyaSharp.Packet.kakeya_scale_weight
#print axioms KakeyaSharp.Packet.kakeyaPacketFamily_density_formula
#print axioms KakeyaSharp.Packet.input_kernel_dominates_constant
#print axioms KakeyaSharp.Packet.kakeyaPacketFamily_input_domination
#print axioms KakeyaSharp.Packet.inputCoordinateMatrix_det
#print axioms KakeyaSharp.Packet.inputCoordinates_unpack
#print axioms KakeyaSharp.Packet.inputCoordinates_measurePreserving
#print axioms KakeyaSharp.Packet.inputAlpha_inputCoordinates
#print axioms KakeyaSharp.Packet.inputQuadratic_inputCoordinates
#print axioms KakeyaSharp.Packet.norm_sq_le_inputQuadratic_inputCoordinates
#print axioms KakeyaSharp.Packet.normalMass_nonneg
#print axioms KakeyaSharp.Packet.normalKernel_nonneg
#print axioms KakeyaSharp.Packet.normalKernel_continuous
#print axioms KakeyaSharp.Packet.normalKernel_ball_integral_le
#print axioms KakeyaSharp.Packet.normalKernel_integrable
#print axioms KakeyaSharp.Packet.normalKernel_integral_le
#print axioms KakeyaSharp.Packet.inputKernel_nonneg
#print axioms KakeyaSharp.Packet.inputKernel_continuous
#print axioms KakeyaSharp.Packet.inputAlpha_continuous
#print axioms KakeyaSharp.Packet.inputKernel_inputCoordinates_le
#print axioms KakeyaSharp.Packet.input_weighted_integrable
#print axioms KakeyaSharp.Packet.input_weighted_integral_le
#print axioms KakeyaSharp.Packet.directionMass_pos
#print axioms KakeyaSharp.Packet.direction_ball_volume
#print axioms KakeyaSharp.Packet.direction_closedBall_volume
#print axioms KakeyaSharp.Packet.direction_cap_card_le
#print axioms KakeyaSharp.Packet.directionWeight_measurable
#print axioms KakeyaSharp.Packet.directionMajorant_nonneg
#print axioms KakeyaSharp.Packet.directionWeight_rpow_le
#print axioms KakeyaSharp.Packet.directionMajorant_integrable
#print axioms KakeyaSharp.Packet.directionMajorant_integral
#print axioms KakeyaSharp.Packet.directionIntegralConstant_pos
#print axioms KakeyaSharp.Packet.directionWeight_rpow_integrable
#print axioms KakeyaSharp.Packet.directionWeight_rpow_integral_le
#print axioms KakeyaSharp.Packet.inputExponent_ge_one
#print axioms KakeyaSharp.Packet.inputIntegralConstant_nonneg
#print axioms KakeyaSharp.Packet.inputEstimateConstant_nonneg
#print axioms KakeyaSharp.Packet.input_direction_weight_integrable
#print axioms KakeyaSharp.Packet.input_direction_weight_measurable
#print axioms KakeyaSharp.Packet.kakeya_input_weighted_integrable
#print axioms KakeyaSharp.Packet.kakeya_input_weighted_integral_le
#print axioms KakeyaSharp.Packet.kakeyaPacketFamily_input_estimate
#print axioms KakeyaSharp.Propagation.outerBox_isOpen
#print axioms KakeyaSharp.Propagation.shell_subset_outerBox
#print axioms KakeyaSharp.Propagation.outerBox_ball_subset
#print axioms KakeyaSharp.Propagation.exists_outerBox_mixing_constant
#print axioms KakeyaSharp.Propagation.exists_outerBox_trace_constant
#print axioms KakeyaSharp.Propagation.cylinderDomain_isOpen
#print axioms KakeyaSharp.Propagation.outerBox_subset_cylinderDomain
#print axioms KakeyaSharp.Propagation.cylinderShell_subset_domain
#print axioms KakeyaSharp.Propagation.exists_singleLog_cylinder_constant

-- Checkpoint 0.16.0: actual weak propagation and localized output.
#check KakeyaSharp.Propagation.exists_weak_singleLog_cylinder_constant
#check KakeyaSharp.Packet.exists_kakeyaPacketFamily_output_upper_constant
#check KakeyaSharp.thinValueRealAt_localization
#check KakeyaSharp.Packet.kakeyaPacketFamily_localized_output_lower
#check KakeyaSharp.Packet.output_lower_scaling
#print axioms KakeyaSharp.Propagation.second_fderiv_convolution_kernel
#print axioms KakeyaSharp.Propagation.laplacian_convolution_kernel
#print axioms KakeyaSharp.Propagation.laplacian_reflect_translate
#print axioms KakeyaSharp.Propagation.mollified_smooth
#print axioms KakeyaSharp.Propagation.translated_mollifier_support
#print axioms KakeyaSharp.Propagation.mollified_laplacian_nonpos
#print axioms KakeyaSharp.Propagation.mollified_nonneg
#print axioms KakeyaSharp.Propagation.mollified_tendsto
#print axioms KakeyaSharp.Propagation.mollified_norm_le
#print axioms KakeyaSharp.Propagation.exists_local_superharmonic_approximation
#print axioms KakeyaSharp.Propagation.cylinderCompact_isCompact
#print axioms KakeyaSharp.Propagation.cylinderDomain_subset_compact
#print axioms KakeyaSharp.Propagation.tracePoint_mem_compact
#print axioms KakeyaSharp.Propagation.inputPoint_mem_compact
#print axioms KakeyaSharp.Propagation.cylinderTrace_tendsto
#print axioms KakeyaSharp.Propagation.exists_weak_singleLog_cylinder_constant
#print axioms KakeyaSharp.Packet.propagationPacketDomain_isOpen
#print axioms KakeyaSharp.Packet.propagationOuterRadius_pos
#print axioms KakeyaSharp.Packet.propagationOuterRadius_sq_gt
#print axioms KakeyaSharp.Packet.supportBound_propagation_uniform
#print axioms KakeyaSharp.Packet.kakeyaPacketFamily_propagation_weakSuperharmonic
#print axioms KakeyaSharp.Packet.kakeyaPacketFamily_propagation_density_continuous
#print axioms KakeyaSharp.Packet.kakeyaPacketFamily_propagation_value_continuous
#print axioms KakeyaSharp.Packet.kakeyaPacketFamily_propagation_value_nonneg
#print axioms KakeyaSharp.Packet.cylinderCompact_subset_propagationPacketDomain
#print axioms KakeyaSharp.Packet.exists_kakeyaPacketFamily_propagation_constant
#print axioms KakeyaSharp.Packet.propagationLog_le
#print axioms KakeyaSharp.Packet.exists_kakeyaPacketFamily_output_upper_constant
#print axioms KakeyaSharp.Dirichlet.thin_dirichlet_comparison_zero
#print axioms KakeyaSharp.Dirichlet.thinQuaternionHessian_comp_add
#print axioms KakeyaSharp.Dirichlet.thin_dirichlet_comparison
#print axioms KakeyaSharp.Dirichlet.ThinDirichletSolution.le_on_subball
#print axioms KakeyaSharp.thinValueRealAt_localization_positive
#print axioms KakeyaSharp.thinValueRealAt_localization
#print axioms KakeyaSharp.thinValueRealAt_localized_thin_lower
#print axioms KakeyaSharp.Packet.ratio_norm_identity
#print axioms KakeyaSharp.Packet.output_phase_le_half
#print axioms KakeyaSharp.Packet.output_cutoff_eq_one
#print axioms KakeyaSharp.Packet.output_prefactor_lower
#print axioms KakeyaSharp.Packet.outputDensityScale_pos
#print axioms KakeyaSharp.Packet.kakeyaPacketFamily_output_density_lower
#print axioms KakeyaSharp.Packet.output_core_error
#print axioms KakeyaSharp.Packet.kakeyaPacketFamily_density_slice_smooth
#print axioms KakeyaSharp.Packet.kakeyaPacketFamily_density_nonneg
#print axioms KakeyaSharp.Packet.kakeyaPacketFamily_localized_output_lower
#print axioms KakeyaSharp.Packet.outputDensityConstant_pos
#print axioms KakeyaSharp.Packet.outputDensityScale_eq
#print axioms KakeyaSharp.Packet.outputLowerConstant_pos
#print axioms KakeyaSharp.Packet.output_delta_power
#print axioms KakeyaSharp.Packet.output_lower_scaling

-- Checkpoint 0.17.0: actual normalized weighted tube estimate.
#check KakeyaSharp.Packet.exists_normalizedTube_constant
#check KakeyaSharp.Packet.exists_enlargedGraphTube_constant
#print axioms KakeyaSharp.Packet.sliceOverlap_nonneg
#print axioms KakeyaSharp.Packet.coverWeight_nonneg
#print axioms KakeyaSharp.Packet.sliceOverlap_le_total
#print axioms KakeyaSharp.Packet.sliceOverlap_measurable
#print axioms KakeyaSharp.Packet.sliceOverlap_le_coverWeight
#print axioms KakeyaSharp.Packet.sliceMajorant_integrable
#print axioms KakeyaSharp.Packet.sliceOverlap_power_le
#print axioms KakeyaSharp.Packet.sliceOverlap_power_integrable
#print axioms KakeyaSharp.Packet.coverMass_pos
#print axioms KakeyaSharp.Packet.coverMajorant_nonneg
#print axioms KakeyaSharp.Packet.sliceOverlap_le_coverMajorant
#print axioms KakeyaSharp.Packet.coverMajorant_integrable
#print axioms KakeyaSharp.Packet.coverMajorant_integral
#print axioms KakeyaSharp.Packet.sliceOverlap_integral_le_cover
#print axioms KakeyaSharp.Packet.graphAxis_norm_le
#print axioms KakeyaSharp.Packet.sliceOverlap_support
#print axioms KakeyaSharp.Packet.output_ball_in_outer
#print axioms KakeyaSharp.Packet.output_balls_disjoint
#print axioms KakeyaSharp.Packet.outputAxis_at_time
#print axioms KakeyaSharp.Packet.output_parameter_radius
#print axioms KakeyaSharp.Packet.outputSliceConstant_pos
#print axioms KakeyaSharp.Packet.kakeyaPacketFamily_output_slice_lower
#print axioms KakeyaSharp.Packet.sliceIntegral_nonneg
#print axioms KakeyaSharp.Packet.sliceIntegral_measurable
#print axioms KakeyaSharp.Packet.sliceMajorant_integral
#print axioms KakeyaSharp.Packet.sliceIntegral_uniform_bound
#print axioms KakeyaSharp.Packet.sliceIntegral_intervalIntegrable
#print axioms KakeyaSharp.Propagation.continuous_cylinder_trace
#print axioms KakeyaSharp.Packet.kakeyaPacketFamily_output_integral_lower
#print axioms KakeyaSharp.Packet.exists_normalizedTube_constant
#print axioms KakeyaSharp.Packet.graphAxis_shifted
#print axioms KakeyaSharp.Packet.shiftedIntercept_bound
#print axioms KakeyaSharp.Packet.graph_point_covered
#print axioms KakeyaSharp.Packet.sliceOverlap_enlarged_le_sum
#print axioms KakeyaSharp.Packet.sliceIntegral_enlarged_le_sum
#print axioms KakeyaSharp.Packet.normalizedTubeMoment_enlarged_le_sum
#print axioms KakeyaSharp.Packet.exists_enlargedGraphTube_constant

-- Checkpoint 0.18.0: arbitrary Euclidean tubes and unconditional maximal bound for n >= 3.
#check KakeyaSharp.sharpTubeBound_of_three_le
#check KakeyaSharp.sharpMaximalBound_of_three_le
#print KakeyaSharp.sharpTubeBound_of_three_le
#print KakeyaSharp.sharpMaximalBound_of_three_le
#print axioms KakeyaSharp.Graph.weightedTubeMoment_partition_le
#print axioms KakeyaSharp.Graph.exists_allDirectionTube_constant
#print axioms KakeyaSharp.Graph.weightedTubeOverlap_nonneg
#print axioms KakeyaSharp.Graph.weightedTubeOverlap_measurable
#print axioms KakeyaSharp.Graph.weightedTubeOverlap_power_le_window
#print axioms KakeyaSharp.Graph.half_scale_log_le
#print axioms KakeyaSharp.Graph.exists_chart_graph_window_constant
#print axioms KakeyaSharp.Graph.exists_chartTube_constant
#print axioms KakeyaSharp.Graph.chartRotation_center
#print axioms KakeyaSharp.Graph.exists_finite_direction_charts
#print axioms KakeyaSharp.Graph.rotated_tube_preimage
#print axioms KakeyaSharp.Graph.integral_rotation
#print axioms KakeyaSharp.Graph.rotation_preserves_separation
#print axioms KakeyaSharp.Graph.exists_globalChartTube_constant
#print axioms KakeyaSharp.Graph.insert_zero
#print axioms KakeyaSharp.Graph.insert_succ
#print axioms KakeyaSharp.Graph.tail_insert
#print axioms KakeyaSharp.Graph.insert_head_tail
#print axioms KakeyaSharp.Graph.tail_add
#print axioms KakeyaSharp.Graph.tail_sub
#print axioms KakeyaSharp.Graph.tail_smul
#print axioms KakeyaSharp.Graph.tail_zero
#print axioms KakeyaSharp.Graph.norm_sq_head_tail
#print axioms KakeyaSharp.Graph.abs_head_le_norm
#print axioms KakeyaSharp.Graph.norm_tail_le
#print axioms KakeyaSharp.Graph.dist_tail_le
#print axioms KakeyaSharp.Graph.norm_insert_zero
#print axioms KakeyaSharp.Graph.coordinates_measurePreserving
#print axioms KakeyaSharp.Graph.integral_coordinates
#print axioms KakeyaSharp.Graph.norm_north
#print axioms KakeyaSharp.Graph.norm_insert_one_ge_one
#print axioms KakeyaSharp.Graph.normalize_sub_le
#print axioms KakeyaSharp.Graph.insert_slope_eq
#print axioms KakeyaSharp.Graph.normalize_slope_eq
#print axioms KakeyaSharp.Graph.direction_dist_le_slope_dist
#print axioms KakeyaSharp.Graph.small_slope_of_near_north
#print axioms KakeyaSharp.Graph.slope_sq_sum_of_near_north
#print axioms KakeyaSharp.Graph.slope_separated
#print axioms KakeyaSharp.Graph.graphAxis_intercept
#print axioms KakeyaSharp.Graph.graph_error_identity
#print axioms KakeyaSharp.Graph.tube_transverse_error
#print axioms KakeyaSharp.Graph.tube_time_window
#print axioms KakeyaSharp.Graph.tube_near_north_in_graph
#print axioms KakeyaSharp.Graph.powerWindow_nonneg
#print axioms KakeyaSharp.Graph.powerWindow_measurable
#print axioms KakeyaSharp.Graph.powerWindow_slice_integral
#print axioms KakeyaSharp.Graph.powerWindow_integrable
#print axioms KakeyaSharp.Graph.powerWindow_integral
#print axioms KakeyaSharp.Packet.sliceOverlap_mono_radius
#print axioms KakeyaSharp.Packet.sliceIntegral_mono_radius
#print axioms KakeyaSharp.Packet.normalizedTubeMoment_mono_radius
#print axioms KakeyaSharp.Packet.exists_globalGraphTube_broad_constant
#print axioms KakeyaSharp.Packet.exists_globalGraphTube_broad_timeInterval_constant
#print axioms KakeyaSharp.Packet.exists_globalGraphTube_constant
#print axioms KakeyaSharp.Packet.normalizedTubeMoment_crude_bound
#print axioms KakeyaSharp.Packet.coarseGraphConstant_pos
#print axioms KakeyaSharp.Packet.normalizedTubeMoment_coarse_bound
#print axioms KakeyaSharp.Packet.exists_globalGraphTube_closedScale_constant
#print axioms KakeyaSharp.Packet.graphAxis_timeShift
#print axioms KakeyaSharp.Packet.sliceOverlap_timeShift
#print axioms KakeyaSharp.Packet.sliceIntegral_timeShift
#print axioms KakeyaSharp.Packet.normalizedTubeMoment_timeShift
#print axioms KakeyaSharp.Packet.sliceIntegral_intervalIntegrable_all
#print axioms KakeyaSharp.Packet.exists_globalGraphTube_timeInterval_constant
#print axioms KakeyaSharp.Packet.groupWeights_nonneg
#print axioms KakeyaSharp.Packet.groupWeights_power_sum
#print axioms KakeyaSharp.Packet.relativeIntercept_bound
#print axioms KakeyaSharp.Packet.sliceOverlap_group_sum
#print axioms KakeyaSharp.Packet.sliceOverlap_group_translate
#print axioms KakeyaSharp.Packet.sliceIntegral_group_translate
#print axioms KakeyaSharp.Packet.normalizedTubeMoment_group_translate
#print axioms KakeyaSharp.Packet.spatialGroupFactor_pos
#print axioms KakeyaSharp.Packet.sliceOverlap_group_near
#print axioms KakeyaSharp.Packet.sliceOverlap_spatial_power_le
#print axioms KakeyaSharp.Packet.sliceIntegral_spatial_le
#print axioms KakeyaSharp.Packet.normalizedTubeMoment_spatial_le
#print axioms KakeyaSharp.sharpTubeBound_of_three_le
#print axioms KakeyaSharp.sharpMaximalBound_of_three_le
#print axioms KakeyaSharp.Graph.weightedTubeOverlap_power_integrable
#print axioms KakeyaSharp.Graph.mem_tube_translate
#print axioms KakeyaSharp.Graph.relativeCenter_norm_le
#print axioms KakeyaSharp.Graph.weightedTubeOverlap_group_sum
#print axioms KakeyaSharp.Graph.weightedTubeOverlap_group_translate
#print axioms KakeyaSharp.Graph.weightedTubeMoment_group_translate
#print axioms KakeyaSharp.Graph.weightedTubeOverlap_group_near
#print axioms KakeyaSharp.Graph.groupWeights_sum_reindex
#print axioms KakeyaSharp.Graph.groupWeights_power_reindex
#print axioms KakeyaSharp.Graph.weightedTubeOverlap_group_reindex
#print axioms KakeyaSharp.Graph.weightedTubeOverlap_rotation
#print axioms KakeyaSharp.Graph.weightedTubeMoment_rotation
#print axioms KakeyaSharp.Graph.tubeGroupFactor_pos
#print axioms KakeyaSharp.Graph.weightedTubeOverlap_spatial_power_le
#print axioms KakeyaSharp.Graph.weightedTubeMoment_spatial_le

-- Checkpoint 0.19.0: the planar case through the same argument.
#check KakeyaSharp.boundaryKernel_radial_le
#print axioms KakeyaSharp.boundaryKernel_radial_le
#check KakeyaSharp.spatial_boundary_integral_log_of_one_le
#print axioms KakeyaSharp.spatial_boundary_integral_log_of_one_le
#check KakeyaSharp.Packet.output_delta_power_real
#print axioms KakeyaSharp.Packet.output_delta_power_real
#check KakeyaSharp.Packet.output_lower_scaling_real
#print axioms KakeyaSharp.Packet.output_lower_scaling_real
#check KakeyaSharp.sharpTubeBound_of_two_le
#print axioms KakeyaSharp.sharpTubeBound_of_two_le
#check KakeyaSharp.sharpMaximalBound_of_two_le
#print axioms KakeyaSharp.sharpMaximalBound_of_two_le
#print KakeyaSharp.sharpTubeBound_of_two_le
#print KakeyaSharp.sharpMaximalBound_of_two_le
example : KakeyaSharp.SharpTubeBound 2 := KakeyaSharp.sharpTubeBound_of_two_le (by decide)
example : KakeyaSharp.SharpMaximalBound 2 := KakeyaSharp.sharpMaximalBound_of_two_le (by decide)
