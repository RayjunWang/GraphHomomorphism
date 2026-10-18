import AbelianTargets.DeterministicQuantitativeAtlas
import AbelianTargets.AtlasRankCovariance

/-! The computed quantitative atlas builder preserves a covariant local extension rule. -/
namespace AbelianTargets
noncomputable section
open scoped NNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d:ℕ} {K₀ K₁:Fin d→ℕ}
variable {T:IntegerRectangularTiling d K₀} {V:IntegerRectangularTiling d K₁}
variable {m K:ℕ} {i:Fin d}

theorem actualQuantitativeSkeleton_covariant
    (δ U:Fin d→ℝ≥0) (D J:ℝ≥0) (hδ:∀j,0<δ j)
    (hlT:∀R,R∈T.cells→∀j,R.lower j<R.upper j→δ j≤(R.transverseWidth j).toNNReal)
    (huT:∀R,R∈T.cells→∀j,(R.transverseWidth j).toNNReal≤U j)
    (hlV:∀R,R∈V.cells→∀j,R.lower j<R.upper j→δ j≤(R.transverseWidth j).toNNReal)
    (huV:∀R,R∈V.cells→∀j,(R.transverseWidth j).toNNReal≤U j)
    (HT:∀R,R∈T.cells→R.lower i<R.upper i→ControlledContraction (cellLeftPoint m K i R) D J)
    (HV:∀R,R∈V.cells→R.lower i<R.upper i→ControlledContraction (cellLeftPoint m K i R) D J)
    (a:Fin d→ℤ) (hcell:∀R:RectangularCell d,R∈T.cells→R.translate a∈V.cells)
    (hstep:∀(n:ℕ)
      (F:QuantitativeEndpointSkeletonCarrierMaps T m K i n (atlasRankRates δ U D J i n))
      (G:QuantitativeEndpointSkeletonCarrierMaps V m K i n (atlasRankRates δ U D J i n)),
      SkeletonCarrierMaps.TranslationCovariant F.toSkeletonCarrierMaps G.toSkeletonCarrierMaps a hcell→
      ∀(R:RectangularCell d)(hR:R∈T.cells)(he:R.rank=n)(z:CellClosedDomain R),
        (actualQuantitativeExtension G HV (R.translate a) (hcell R hR)
          (by simpa only [RectangularCell.rank_translate] using he)).map (R.translateClosedPoint a z)=
          IntervalCarriers.realizationTranslation (a i) ((actualQuantitativeExtension F HT R hR he).map z))
    (n:ℕ) :
    SkeletonCarrierMaps.TranslationCovariant
      (actualQuantitativeSkeleton δ U D J hδ hlT huT HT n).toSkeletonCarrierMaps
      (actualQuantitativeSkeleton δ U D J hδ hlV huV HV n).toSkeletonCarrierMaps a hcell := by
  induction n with
  | zero => exact SkeletonCarrierMaps.empty_translationCovariant a hcell
  | succ n ih =>
    let F := actualQuantitativeSkeleton δ U D J hδ hlT huT HT n
    let G := actualQuantitativeSkeleton δ U D J hδ hlV huV HV n
    have hnext := EndpointSkeletonCarrierMaps.next_translationCovariant
      F.toEndpointSkeletonCarrierMaps G.toEndpointSkeletonCarrierMaps a hcell ih
      (actualQuantitativeExtension F HT) (actualQuantitativeExtension G HV) (hstep n F G ih)
    exact hnext

end
end AbelianTargets
