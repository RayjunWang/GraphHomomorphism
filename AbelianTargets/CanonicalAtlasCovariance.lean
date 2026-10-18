import AbelianTargets.ActualAtlasExtensionCovariance
import AbelianTargets.DeterministicAtlasCovariance
import AbelianTargets.AtlasCanonicalContractions

/-! Translation covariance of the literal rank recursion driven by a
single normalized contraction family. -/

namespace AbelianTargets
noncomputable section
open scoped NNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d m K S : ℕ} {K₀ : Fin d→ℕ}
variable {T : IntegerRectangularTiling d K₀} {i : Fin d} {J : ℝ≥0}

theorem canonicalQuantitativeSkeleton_translate
    (H : IntervalCarriers.NormalizedContractionFamily m K S J) (hS : K₀ i≤S)
    (δ U : Fin d→ℝ≥0) (hδ : ∀j,0<δ j)
    (hl : ∀R,R∈T.cells→∀j,R.lower j<R.upper j→δ j≤(R.transverseWidth j).toNNReal)
    (hu : ∀R,R∈T.cells→∀j,(R.transverseWidth j).toNNReal≤U j)
    (a : Fin d→ℤ)
    (hl' : ∀R,R∈(T.translate a).cells→∀j,R.lower j<R.upper j→δ j≤(R.transverseWidth j).toNNReal)
    (hu' : ∀R,R∈(T.translate a).cells→∀j,(R.transverseWidth j).toNNReal≤U j)
    (n : ℕ) :
    SkeletonCarrierMaps.TranslationCovariant
      (actualQuantitativeSkeleton δ U (IntervalCarriers.uniformCarrierSpeed m K) J hδ hl hu
        (canonicalAtlasContractionProvider H T i hS) n).toSkeletonCarrierMaps
      (actualQuantitativeSkeleton δ U (IntervalCarriers.uniformCarrierSpeed m K) J hδ hl' hu'
        (canonicalAtlasContractionProvider H (T.translate a) i hS) n).toSkeletonCarrierMaps
      a (fun R hR=>T.cell_translate hR a) := by
  apply actualQuantitativeSkeleton_covariant δ U (IntervalCarriers.uniformCarrierSpeed m K) J
    hδ hl hu hl' hu' (canonicalAtlasContractionProvider H T i hS)
    (canonicalAtlasContractionProvider H (T.translate a) i hS) a
    (fun R hR=>T.cell_translate hR a)
  intro r F G hold R hR he z
  apply actualQuantitativeExtension_translate F a G
    (canonicalAtlasContractionProvider H T i hS)
    (canonicalAtlasContractionProvider H (T.translate a) i hS) hold
    (fun Q hQ hi p t=>?_) R hR he z
  exact canonicalCellContraction_translate H i Q hi _ a p t

end
end AbelianTargets
