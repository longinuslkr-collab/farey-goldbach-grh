import FareyGoldbach.Target3AFoundation
import FareyGoldbach.Target3AAssembly
import FareyGoldbach.CompositeTarget3A
import FareyGoldbach.Target3BMoebiusSplit
import FareyGoldbach.Target3BKaratsuba
import FareyGoldbach.Target3BThresholds

-- Target 3A foundation & regressions
#print axioms Target3A.physicalShift
#print axioms Target3A.plusShiftObstruction
#print axioms Target3A.correctedCofactorEquiv
#print axioms Target3A.originalNumericalRegression
#print axioms Target3A.positiveOrderRegression
#print axioms Target3A.physicalBoxRegression
#print axioms Target3A.latticeMatrix_det
#print axioms Target3A.latticeMatrix_range
#print axioms Target3A.latticeMatrix_primitive_in_box
#print axioms Target3A.latticeMatrix_p7_regression

-- Target 3A assembly & parameter budget
#print axioms Target3A.r2_congruence_of_minus_cofactor
#print axioms Target3A.determinant_dvd_of_minus_cofactors
#print axioms Target3A.product_fiber_spacing
#print axioms Target3A.swap_matrix_class_formula
#print axioms Target3A.swap_matrix_class_det_and_r2
#print axioms Target3A.swap_matrix_class_involutive
#print axioms Target3A.swap_matrix_class_modEq_iff
#print axioms Target3A.auxiliary_pairing_weight_identity
#print axioms Target3A.minor_arc_parameter_budget
#print axioms Target3A.minor_arc_assembled_moment_bound
#print axioms Target3A.minor_arc_normalized_pairing_bound
#print axioms Target3A.minor_arc_physical_pairing_bound
#print axioms Target3A.minor_arc_arbitrary_log_saving
#print axioms Target3A.minor_arc_arbitrary_real_log_saving

-- Target 3A composite-modulus (all integers) lattice, gcd strip, and log budget
#print axioms CompositeTarget3A.latticeMatrix_det
#print axioms CompositeTarget3A.latticeMatrix_mulVec_zero
#print axioms CompositeTarget3A.latticeMatrix_mulVec_one
#print axioms CompositeTarget3A.exists_lattice_completion
#print axioms CompositeTarget3A.root_coprime_of_unit
#print axioms CompositeTarget3A.latticeMatrix_range_of_primitive
#print axioms CompositeTarget3A.latticeMatrix_range
#print axioms CompositeTarget3A.latticeMatrix_primitive_in_box
#print axioms CompositeTarget3A.collinear_trans
#print axioms CompositeTarget3A.kloosterman_rhs_coprime
#print axioms CompositeTarget3A.gcd_strip
#print axioms CompositeTarget3A.minus_cofactor_strip
#print axioms CompositeTarget3A.gcd_dvd_cofactor
#print axioms CompositeTarget3A.minus_cofactor_strip_exists
#print axioms CompositeTarget3A.minus_cofactor_determinant
#print axioms CompositeTarget3A.minus_cofactor_mod_second_prime
#print axioms CompositeTarget3A.log_budget

-- Target 3B double-cutoff Möbius split & 9/19 ledger
#print axioms Target3B.moebius_two_cutoffs
#print axioms Target3B.moebius_finite_split
#print axioms Target3B.typeI_vanish_of_mul_cutoffs_lt
#print axioms Target3B.typeII_tail_vanish_of_le_cutoff
#print axioms Target3B.typeI_scale
#print axioms Target3B.typeII_completion_scales
#print axioms Target3B.typeII_fourth_scales
#print axioms Target3B.every_row_strict
#print axioms Target3B.sum_rows_strict
#print axioms Target3B.transition_optimal
#print axioms Target3B.truncation_optimal
#print axioms Target3B.threshold
#print axioms Target3B.analytic_power_bound

-- Target 3B Karatsuba–Bourgain–Garaev LCM lemma (unconditional)
#print axioms Target3B.karatsuba_lcm_sq_dvd_prod
#print axioms Target3B.karatsuba_lcm_sq_le_prod
#print axioms Target3B.karatsuba_four_reciprocals
#print axioms Target3B.karatsuba_six_reciprocals

-- Target 3B 8/17 elementary and 7/15 spectral threshold ledgers
#print axioms ThresholdEightSeventeenths.cuts_ordered
#print axioms ThresholdEightSeventeenths.type_i_rows
#print axioms ThresholdEightSeventeenths.cauchy_rows
#print axioms ThresholdEightSeventeenths.sixth_moment_rows
#print axioms ThresholdEightSeventeenths.fourth_moment_rows
#print axioms ThresholdEightSeventeenths.attained_at_sixth_cut
#print axioms ThresholdEightSeventeenths.balanced_threshold
#print axioms ThresholdEightSeventeenths.shifted_poisson_cap
#print axioms ThresholdSevenFifteenths.cuts_ordered
#print axioms ThresholdSevenFifteenths.type_i_rows
#print axioms ThresholdSevenFifteenths.spectral_cauchy_rows
#print axioms ThresholdSevenFifteenths.spectral_length_margin
#print axioms ThresholdSevenFifteenths.exceptional_factor_exponents
#print axioms ThresholdSevenFifteenths.normalize_completed_terms
#print axioms ThresholdSevenFifteenths.sixth_moment_rows
#print axioms ThresholdSevenFifteenths.fourth_moment_rows
#print axioms ThresholdSevenFifteenths.attained_at_fourth_cut
#print axioms ThresholdSevenFifteenths.obstruction_at_three_j
#print axioms ThresholdSevenFifteenths.spectral_strictly_improves
#print axioms ThresholdSevenFifteenths.balanced_threshold
#print axioms ThresholdSevenFifteenths.shifted_poisson_cap
