import AbelianTargets.AtlasEndpointRecursion
import AbelianTargets.IntegerPrismEstimates

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace AbelianTargets
noncomputable section
open scoped NNReal unitInterval
variable {d : ℕ} {K₀ : Fin d→ℕ} {T : IntegerRectangularTiling d K₀}
variable {m K : ℕ} {i : Fin d}

def CellCoordinateBounds (R : RectangularCell d)
    (f : CellClosedDomain R → CellIntervalCarrier m K i R) (C : Fin d→ℝ≥0) : Prop :=
  ∀ j (z z' : CellClosedDomain R),(∀ k,k≠j → z.val k=z'.val k) →
    dist (f z) (f z')≤C j*|z.val j-z'.val j|

structure QuantitativeEndpointSkeletonCarrierMaps (T : IntegerRectangularTiling d K₀)
    (m K : ℕ) (i : Fin d) (n : ℕ) (C : Fin d→ℝ≥0)
    extends EndpointSkeletonCarrierMaps T m K i n where
  coordinate_bounds : ∀ R hR hr,CellCoordinateBounds R (map R hR hr) C

namespace QuantitativeEndpointSkeletonCarrierMaps
variable {n : ℕ} {C C' : Fin d→ℝ≥0}

def empty : QuantitativeEndpointSkeletonCarrierMaps T m K i 0 C where
  toEndpointSkeletonCarrierMaps := EndpointSkeletonCarrierMaps.empty
  coordinate_bounds R hR hr := (Nat.not_lt_zero _ hr).elim

def next (F : QuantitativeEndpointSkeletonCarrierMaps T m K i n C)
    (extend : ∀ (R : RectangularCell d) (hR : R∈T.cells) (he : R.rank=n),
      EndpointCellCarrierExtension (F.toSkeletonCarrierMaps.lowerFamily R he) hR)
    (hCC : ∀ j,C j≤C' j)
    (hnew : ∀ R hR he,CellCoordinateBounds R (extend R hR he).map C') :
    QuantitativeEndpointSkeletonCarrierMaps T m K i (n+1) C' where
  toEndpointSkeletonCarrierMaps := F.toEndpointSkeletonCarrierMaps.next extend
  coordinate_bounds R hR hr := by
    intro j z z' heq
    change dist (F.toEndpointSkeletonCarrierMaps.nextMap extend R hR hr z)
      (F.toEndpointSkeletonCarrierMaps.nextMap extend R hR hr z')≤_
    by_cases h : R.rank<n
    · simp only [EndpointSkeletonCarrierMaps.nextMap,dif_pos h]
      exact (F.coordinate_bounds R hR h j z z' heq).trans
        (mul_le_mul_of_nonneg_right (hCC j) (abs_nonneg _))
    · simp only [EndpointSkeletonCarrierMaps.nextMap,dif_neg h]
      exact hnew R hR (by omega) j z z' heq

theorem lowerFamily_update_bounds (F : QuantitativeEndpointSkeletonCarrierMaps T m K i n C)
    (R : RectangularCell d) (he : R.rank=n) (j : Fin d)
    (Q : RectangularCell d) (hQ : Q∈T.cells) (hrQ : Q.rank<R.rank)
    (w : RealCoordinates d) (x y : ℝ)
    (hx : Function.update w j x∈Q.closedBox) (hy : Function.update w j y∈Q.closedBox) :
    dist ((F.toSkeletonCarrierMaps.lowerFamily R he).map Q hQ hrQ ⟨Function.update w j x,hx⟩)
      ((F.toSkeletonCarrierMaps.lowerFamily R he).map Q hQ hrQ ⟨Function.update w j y,hy⟩)≤C j*|x-y| := by
  have hh := F.coordinate_bounds Q hQ (by omega : Q.rank<n) j
    ⟨Function.update w j x,hx⟩ ⟨Function.update w j y,hy⟩ (by
      intro k hk; simp only [Function.update_of_ne hk])
  simpa using hh

end QuantitativeEndpointSkeletonCarrierMaps

namespace LowerCellCarrierMaps
variable {R : RectangularCell d}

def fillingCoordinateRate (R : RectangularCell d) (i : Fin d)
    (S B D J : ℝ≥0) (j : Fin d) : ℝ≥0 :=
  if j=i then 3*max S D/(R.transverseWidth j).toNNReal
  else 2*ControlledContraction.coneTransverseConstant S D J B/(R.transverseWidth j).toNNReal

theorem relativeCellExtension_coordinate_bounds (F : LowerCellCarrierMaps T m K i R)
    (hR : R∈T.cells) (hF : F.EndpointValues) {S B D J : ℝ≥0}
    (hi : R.lower i<R.upper i) (H : ControlledContraction (cellLeftPoint m K i R) D J)
    (hpath : ∀ v : ConeSphere (R.ActiveTransverse i→ℝ),LipschitzWith S
      (fun r => F.boundaryValue hR (prismBoundaryPoint R i v r)))
    (htrans : ∀ r : unitInterval,LipschitzWith B
      (fun v : ConeSphere (R.ActiveTransverse i→ℝ) => F.boundaryValue hR (prismBoundaryPoint R i v r))) :
    CellCoordinateBounds R (F.relativeCellExtension hR hF hi H hpath htrans).map
      (fillingCoordinateRate R i S B D J) := by
  intro j z z' heq
  by_cases hji : j=i
  · subst j
    have hw : 0<R.transverseWidth i := sub_pos.mpr (by exact_mod_cast hi)
    have hh := (F.prismBoundaryData hR hF S B hpath htrans).fill_first_dist_le H hi z z' heq
    simpa [relativeCellExtension,fillingCoordinateRate,PrismBoundaryData.continuousMap,NNReal.coe_div,NNReal.coe_mul,
      NNReal.coe_ofNat,Real.coe_toNNReal _ hw.le] using hh
  · by_cases hj : R.lower j<R.upper j
    · have hw : 0<R.transverseWidth j := sub_pos.mpr (by exact_mod_cast hj)
      have hh := (F.prismBoundaryData hR hF S B hpath htrans).fill_transverse_dist_le H hi j hji hj z z' heq
      simpa [relativeCellExtension,fillingCoordinateRate,PrismBoundaryData.continuousMap,hji,NNReal.coe_div,NNReal.coe_mul,
        NNReal.coe_ofNat,Real.coe_toNNReal _ hw.le] using hh
    · have he : R.lower j=R.upper j := le_antisymm (R.ordered j) (le_of_not_gt hj)
      have hz := R.point_eq_of_only_collapsed_coordinate j he z z' heq
      rw [hz,dist_self]
      positivity

theorem collapsedCellExtension_coordinate_bounds (F : LowerCellCarrierMaps T m K i R)
    (hR : R∈T.cells) (hF : F.EndpointValues) (hi : R.lower i=R.upper i)
    (C : Fin d→ℝ≥0) : CellCoordinateBounds R (F.collapsedCellExtension hR hF hi).map C := by
  intro j z z' heq
  change dist (cellLeftPoint m K i R) (cellLeftPoint m K i R)≤_
  rw [dist_self]
  positivity

end LowerCellCarrierMaps
end
end AbelianTargets
