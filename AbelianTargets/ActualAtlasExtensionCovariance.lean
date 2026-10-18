import AbelianTargets.DeterministicQuantitativeAtlas
import AbelianTargets.AtlasBoundaryTranslation
import AbelianTargets.PrismFillNaturality
import AbelianTargets.AtlasRankCovariance

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace AbelianTargets
noncomputable section
open scoped NNReal unitInterval
variable {d : ℕ} {K₀ : Fin d→ℕ} {T : IntegerRectangularTiling d K₀}
variable {m K n : ℕ} {i : Fin d} {C C' : Fin d→ℝ≥0} {D J : ℝ≥0}

theorem actualQuantitativeExtension_translate
    (F : QuantitativeEndpointSkeletonCarrierMaps T m K i n C) (a : Fin d→ℤ)
    (G : QuantitativeEndpointSkeletonCarrierMaps (T.translate a) m K i n C')
    (H : ∀R,R∈T.cells → R.lower i<R.upper i → ControlledContraction (cellLeftPoint m K i R) D J)
    (H' : ∀R,R∈(T.translate a).cells → R.lower i<R.upper i → ControlledContraction (cellLeftPoint m K i R) D J)
    (hold : SkeletonCarrierMaps.TranslationCovariant F.toSkeletonCarrierMaps G.toSkeletonCarrierMaps a
      (fun R hR=>T.cell_translate hR a))
    (hH : ∀ (R : RectangularCell d) (hR : R∈T.cells) (hi : R.lower i<R.upper i)
      (p : CellIntervalCarrier m K i R) (t : I),
      (H' (R.translate a) (T.cell_translate hR a) (by simpa [RectangularCell.translate] using hi)).map
        (cellIntervalTranslate i a R p,t)=cellIntervalTranslate i a R ((H R hR hi).map (p,t)))
    (R : RectangularCell d) (hR : R∈T.cells) (he : R.rank=n) (z : CellClosedDomain R) :
    (actualQuantitativeExtension G H' (R.translate a) (T.cell_translate hR a)
      (by simpa only [RectangularCell.rank_translate] using he)).map (R.translateClosedPoint a z)=
      cellIntervalTranslate i a R ((actualQuantitativeExtension F H R hR he).map z) := by
  have he' : (R.translate a).rank=n := by simpa only [RectangularCell.rank_translate] using he
  by_cases hi : R.lower i<R.upper i
  · have hi' : (R.translate a).lower i<(R.translate a).upper i := by simpa [RectangularCell.translate] using hi
    simp only [actualQuantitativeExtension,dif_pos hi,dif_pos hi']
    let LF := F.toSkeletonCarrierMaps.lowerFamily R he
    let LG := G.toSkeletonCarrierMaps.lowerFamily (R.translate a) he'
    let PF := LF.controlledPrismData hR (F.toEndpointSkeletonCarrierMaps.lowerFamily_endpoints R he)
      C (F.lowerFamily_update_bounds R he) hi
    let PG := LG.controlledPrismData (T.cell_translate hR a)
      (G.toEndpointSkeletonCarrierMaps.lowerFamily_endpoints (R.translate a) he')
      C' (G.lowerFamily_update_bounds (R.translate a) he') hi'
    exact PF.fill_translate_of_maps (H R hR hi) a
      (IntervalCarriers.realizationTranslationEquiv (a i)) PG
      (H' (R.translate a) (T.cell_translate hR a) hi')
      (cellLeftPoint_translate i a R) (cellRightPoint_translate i a R)
      (hH R hR hi)
      (LF.boundaryValue_translate hR a LG (by
        intro Q hQ hrQ zQ
        exact hold Q hQ (by omega) zQ)) hi z
  · have hi' : ¬(R.translate a).lower i<(R.translate a).upper i := by simpa [RectangularCell.translate] using hi
    simp only [actualQuantitativeExtension,dif_neg hi,dif_neg hi']
    exact (cellLeftPoint_translate i a R).symm

end
end AbelianTargets
