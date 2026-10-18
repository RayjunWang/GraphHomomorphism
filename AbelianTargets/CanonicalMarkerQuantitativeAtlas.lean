import AbelianTargets.ActualMarkerQuantitativeAtlas
import AbelianTargets.AtlasCanonicalContractions

namespace AbelianTargets
noncomputable section
open scoped NNReal
variable {d : ℕ} {L : Fin d→ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
variable {M₀ : AnisotropicClopenMarkers d L X} {S : ℕ}

/-- Literal atlas rank recursion driven by one fixed zero-based contraction
family. The provider makes no further choice on individual cells. -/
def ContinuousMarkerBoxes.canonicalQuantitativeSkeleton
    (B : ContinuousMarkerBoxes M₀ S) (hL : ∀j,1≤L j) (hS : 24≤S) (x : X)
    (m K : ℕ) (i : Fin d) (J : ℝ≥0)
    (H : IntervalCarriers.NormalizedContractionFamily m K (6*L i) J) (n : ℕ) :
    QuantitativeEndpointSkeletonCarrierMaps (B.tiling hL (by omega) x) m K i n
      (atlasRankRates (fun j=>(L j : ℝ≥0)/(32*((2*S+1)^d : ℕ)))
        (fun j=>6*(L j : ℝ≥0)) (IntervalCarriers.uniformCarrierSpeed m K) J i n) :=
  B.quantitativeSkeleton hL hS x m K i (IntervalCarriers.uniformCarrierSpeed m K) J
    (canonicalAtlasContractionProvider H (B.tiling hL (by omega) x) i (by rfl)) n

end
end AbelianTargets
