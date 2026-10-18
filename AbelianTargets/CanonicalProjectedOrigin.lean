import AbelianTargets.ActualProjectedOriginLocality
import AbelianTargets.FinitePatternFunctions

namespace AbelianTargets
noncomputable section
open scoped NNReal
variable {d : ℕ} {L : Fin d→ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
variable {M₀ : AnisotropicClopenMarkers d L X} {S : ℕ}
variable {W : Type*} [Fintype W] {G : SimpleGraph W} (D₀ : SupportTorsionData G)

theorem ContinuousMarkerBoxes.canonicalProjectedMap_isLocallyConstant
    (B : ContinuousMarkerBoxes M₀ S) (hL : ∀j,1≤L j) (hS : 24≤S)
    (K : ℕ) (i : Fin d) (J : ℝ≥0)
    (H : IntervalCarriers.NormalizedContractionFamily (2*D₀.power+1) K (6*L i) J)
    (z : RealCoordinates d) : IsLocallyConstant (fun x=>B.canonicalProjectedMap D₀ hL hS K i J H x z) := by
  apply locallyConstant_of_pattern (fun x=>(B.tiling hL (by omega) x).dependencyPattern z)
    (IntegerRectangularTiling.dependencyPattern_isLocallyConstant
      (B.tiling hL (by omega)) B.retainedTiles_eventually_eq z)
  intro x y hpat
  exact B.canonicalProjectedMap_pattern D₀ hL hS K i J H x y z hpat

theorem ContinuousMarkerBoxes.canonicalProjectedMap_finite_range
    (B : ContinuousMarkerBoxes M₀ S) (hL : ∀j,1≤L j) (hS : 24≤S)
    (K : ℕ) (i : Fin d) (J : ℝ≥0)
    (H : IntervalCarriers.NormalizedContractionFamily (2*D₀.power+1) K (6*L i) J)
    (z : RealCoordinates d) : (Set.range (fun x=>B.canonicalProjectedMap D₀ hL hS K i J H x z)).Finite := by
  apply finite_range_of_constant_pattern (fun x=>(B.tiling hL (by omega) x).dependencyPattern z)
    (IntegerRectangularTiling.dependencyPattern_finite_range (B.tiling hL (by omega)) z)
  intro x y hpat
  exact B.canonicalProjectedMap_pattern D₀ hL hS K i J H x y z hpat

theorem ContinuousMarkerBoxes.continuous_canonicalProjectedMap
    (B : ContinuousMarkerBoxes M₀ S) (hL : ∀j,1≤L j) (hS : 24≤S)
    (K : ℕ) (i : Fin d) (J : ℝ≥0)
    (H : IntervalCarriers.NormalizedContractionFamily (2*D₀.power+1) K (6*L i) J)
    (z : RealCoordinates d) : Continuous (fun x=>B.canonicalProjectedMap D₀ hL hS K i J H x z) :=
  (B.canonicalProjectedMap_isLocallyConstant D₀ hL hS K i J H z).continuous

end
end AbelianTargets
