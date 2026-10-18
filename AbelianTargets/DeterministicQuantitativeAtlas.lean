import AbelianTargets.ActualQuantitativeAtlasRecursion

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace AbelianTargets
noncomputable section
open scoped NNReal
variable {d : ℕ} {K₀ : Fin d→ℕ} {T : IntegerRectangularTiling d K₀}
variable {m K : ℕ} {i : Fin d}

def actualQuantitativeExtension {n : ℕ} {C : Fin d→ℝ≥0}
    (F : QuantitativeEndpointSkeletonCarrierMaps T m K i n C) {D J : ℝ≥0}
    (H : ∀R,R∈T.cells → R.lower i<R.upper i → ControlledContraction (cellLeftPoint m K i R) D J)
    (R : RectangularCell d) (hR : R∈T.cells) (he : R.rank=n) :
    EndpointCellCarrierExtension (F.toSkeletonCarrierMaps.lowerFamily R he) hR :=
  if hi : R.lower i<R.upper i then
    (F.toSkeletonCarrierMaps.lowerFamily R he).controlledCellExtension hR
      (F.toEndpointSkeletonCarrierMaps.lowerFamily_endpoints R he) C
      (F.lowerFamily_update_bounds R he) hi (H R hR hi)
  else (F.toSkeletonCarrierMaps.lowerFamily R he).collapsedCellExtension hR
    (F.toEndpointSkeletonCarrierMaps.lowerFamily_endpoints R he)
    (le_antisymm (R.ordered i) (le_of_not_gt hi))

theorem actualQuantitativeExtension_bounds {n : ℕ} {C δ U : Fin d→ℝ≥0}
    (F : QuantitativeEndpointSkeletonCarrierMaps T m K i n C) {D J : ℝ≥0}
    (H : ∀R,R∈T.cells → R.lower i<R.upper i → ControlledContraction (cellLeftPoint m K i R) D J)
    (hδ : ∀j,0<δ j)
    (hlower : ∀R,R∈T.cells → ∀j,R.lower j<R.upper j → δ j≤(R.transverseWidth j).toNNReal)
    (hupper : ∀R,R∈T.cells → ∀j,(R.transverseWidth j).toNNReal≤U j)
    (R : RectangularCell d) (hR : R∈T.cells) (he : R.rank=n) :
    CellCoordinateBounds R (actualQuantitativeExtension F H R hR he).map (nextRankRates δ U C D J i) := by
  intro j z z' heq
  by_cases hi : R.lower i<R.upper i
  · simp only [actualQuantitativeExtension,dif_pos hi]
    let LF := F.toSkeletonCarrierMaps.lowerFamily R he
    have hC : LF.CoordinateBounds C := F.lowerFamily_update_bounds R he
    have hE := LF.relativeCellExtension_coordinate_bounds hR
      (F.toEndpointSkeletonCarrierMaps.lowerFamily_endpoints R he) hi (H R hR hi)
      (LF.prism_path_lipschitz hR hi (C i) (hC i)) (LF.prism_transverse_lipschitz hR C hC)
    have hh := hE j z z' heq
    by_cases hj : R.lower j<R.upper j
    · exact hh.trans (mul_le_mul_of_nonneg_right
        (fillingCoordinateRate_le_nextRankRates R i C δ U D J hδ
          (hlower R hR) (hupper R hR) j hj) (abs_nonneg _))
    · have hz := R.point_eq_of_only_collapsed_coordinate j
        (le_antisymm (R.ordered j) (le_of_not_gt hj)) z z' heq
      rw [hz,dist_self]
      positivity
  · simp only [actualQuantitativeExtension,dif_neg hi]
    exact (F.toSkeletonCarrierMaps.lowerFamily R he).collapsedCellExtension_coordinate_bounds hR
      (F.toEndpointSkeletonCarrierMaps.lowerFamily_endpoints R he) _ _ j z z' heq

def actualQuantitativeNext {n : ℕ} (δ U : Fin d→ℝ≥0) (D J : ℝ≥0)
    (hδ : ∀j,0<δ j)
    (hlower : ∀R,R∈T.cells → ∀j,R.lower j<R.upper j → δ j≤(R.transverseWidth j).toNNReal)
    (hupper : ∀R,R∈T.cells → ∀j,(R.transverseWidth j).toNNReal≤U j)
    (H : ∀R,R∈T.cells → R.lower i<R.upper i → ControlledContraction (cellLeftPoint m K i R) D J)
    (F : QuantitativeEndpointSkeletonCarrierMaps T m K i n (atlasRankRates δ U D J i n)) :
    QuantitativeEndpointSkeletonCarrierMaps T m K i (n+1) (atlasRankRates δ U D J i (n+1)) :=
  F.next (actualQuantitativeExtension F H) (atlasRankRates_step_mono δ U D J i n)
    (actualQuantitativeExtension_bounds F H hδ hlower hupper)

def actualQuantitativeSkeleton (δ U : Fin d→ℝ≥0) (D J : ℝ≥0)
    (hδ : ∀j,0<δ j)
    (hlower : ∀R,R∈T.cells → ∀j,R.lower j<R.upper j → δ j≤(R.transverseWidth j).toNNReal)
    (hupper : ∀R,R∈T.cells → ∀j,(R.transverseWidth j).toNNReal≤U j)
    (H : ∀R,R∈T.cells → R.lower i<R.upper i → ControlledContraction (cellLeftPoint m K i R) D J) :
    ∀ n,QuantitativeEndpointSkeletonCarrierMaps T m K i n (atlasRankRates δ U D J i n)
  | 0 => QuantitativeEndpointSkeletonCarrierMaps.empty
  | n+1 => actualQuantitativeNext δ U D J hδ hlower hupper H
      (actualQuantitativeSkeleton δ U D J hδ hlower hupper H n)

end
end AbelianTargets
