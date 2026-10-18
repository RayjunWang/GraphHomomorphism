import AbelianTargets
import Lean.Util.CollectAxioms

/-!
Audit every declaration in the project namespace, including intermediates.
A clean audit checks proof trust; it does NOT discharge explicit hypotheses
of conditional helper theorems. The final positive results are also checked
against the three standard axioms alone.
-/

open Lean Elab Command in
elab "#audit_abelian_targets" : command => do
  let env ← getEnv
  let mut count := 0
  for (name, _) in env.constants.toList do
    if (`AbelianTargets).isPrefixOf (Lean.privateToUserName name) then
      count := count + 1
      let dependencies ← Lean.collectAxioms name
      for ax in dependencies do
        unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound ||
            ax == `AbelianTargets.References.bernshteyn_theorem_1_12 ||
            ax == `AbelianTargets.References.gjks_theorem_3_5_1 ||
            ax == `AbelianTargets.References.gjks_direction_preserving_twelve_tiles ||
            ax == `AbelianTargets.References.gjks_eventual_twelve_tile_source ||
            ax == `AbelianTargets.References.bernshteyn_directed_twelve_tiles_universality do
          throwError "Unexpected axiom {ax} in {name}"
  for name in [`AbelianTargets.proposition7_1, `AbelianTargets.theorem1_4] do
    unless env.contains name do
      throwError "Missing completed positive theorem {name}"
    for ax in (← Lean.collectAxioms name) do
      unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
        throwError "Nonstandard axiom {ax} in final positive theorem {name}"
  logInfo "FINAL_POSITIVE_AXIOMS_OK: Theorem 1.4 and Proposition 7.1 use only standard Lean axioms"
  logInfo m!"AUDIT_OK: {count} declarations; allowed: three standard axioms and five individually whitelisted reference axioms"

#audit_abelian_targets

-- Exact statement definitions and the completed dimension theorem.
#check AbelianTargets.Theorem14Statement
#check AbelianTargets.Proposition71Statement
#check AbelianTargets.Proposition77Statement
#check AbelianTargets.proposition7_1
#check AbelianTargets.theorem1_4
#check AbelianTargets.proposition7_7
#check AbelianTargets.finiteGraphClasses_strictDecrease

-- The construction/source-obstruction parameters remain visible in these types.
#check AbelianTargets.theorem1_4_of_torsionFieldConstruction
#check AbelianTargets.proposition7_1_of_torsionFieldConstruction
#check AbelianTargets.proposition7_7_of_finite_source_obstructions

#print axioms AbelianTargets.ReducedFundamentalGroup.parity
#print axioms AbelianTargets.odd_class_order_even
#print axioms AbelianTargets.k4Triangle_square_null
#print axioms AbelianTargets.hasContinuousHom_of_supportModel
#print axioms AbelianTargets.markerDirectionLaws
#print axioms AbelianTargets.ClopenMarkers.hasContinuousHom
#print axioms AbelianTargets.exists_clopen_maximal_independent
#print axioms AbelianTargets.markerGraph_universalTarget
#print axioms AbelianTargets.markerGraph_inClass
#print axioms AbelianTargets.inClass_succ_subset
#print axioms AbelianTargets.coprime_torus_signedDiagonal_no_edge
#print axioms AbelianTargets.signedDirection_sum_saturation
#print axioms AbelianTargets.strictDecrease_of_proposition7_7
#print axioms AbelianTargets.proposition7_1_dimensions_at_most_two
#print axioms AbelianTargets.theorem1_4_dimensions_at_most_two
#print axioms AbelianTargets.freeShiftPolishSpace
#print axioms AbelianTargets.exists_continuous_displacement_three_coloring
#print axioms AbelianTargets.exists_freeShift_extension
#print axioms AbelianTargets.cyclicProductShift_transitive
#print axioms AbelianTargets.signedDirection_coprime_periods
#print axioms AbelianTargets.proposition7_7
#print axioms AbelianTargets.finiteGraphClasses_strictDecrease
#print axioms AbelianTargets.proposition7_1
#print axioms AbelianTargets.theorem1_4
#print axioms AbelianTargets.supportTorsionData_of_oddTorsion
#print axioms AbelianTargets.approximateParityMaps_of_anisotropicConstruction
#print axioms AbelianTargets.exists_continuous_finite_coloring
#print axioms AbelianTargets.exists_anisotropicClopenMarkers
#print axioms AbelianTargets.exists_continuous_markerPriorities
#print axioms AbelianTargets.priorityCutIteration_translated
#print axioms AbelianTargets.ControlledContraction.relativeHomotopy_uniform_comparison
#print axioms AbelianTargets.ControlledContraction.continuous_rectangularValue
#print axioms AbelianTargets.ParityPresentation.etaImage_deck
#print axioms AbelianTargets.FixedSlots.sequenceHomotopy_path_time_lipschitz
#print axioms AbelianTargets.compressedWord_interval_safe_carry
#print axioms AbelianTargets.FixedSlots.localMove_mem
#print axioms AbelianTargets.FixedSlots.localMove_path_time_lipschitz
#print axioms AbelianTargets.SupportPair.faceControlledContraction
#print axioms AbelianTargets.exists_markerPriorityNeighborhood
#print axioms AbelianTargets.continuous_priorityCuts
#print axioms AbelianTargets.exists_bounded_carrier_carry_rows
#print axioms AbelianTargets.exists_orbitMarkerCuts
#print axioms AbelianTargets.FixedSlots.pauseTransport_path_time_lipschitz
#print axioms AbelianTargets.continuous_inactiveOrbitNeighbors
