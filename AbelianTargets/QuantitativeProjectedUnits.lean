import AbelianTargets.ProjectedAtlasMaps
import AbelianTargets.AtlasQuantitativeRecursion

namespace AbelianTargets
noncomputable section
open scoped NNReal
variable {d : ℕ} {K₀ : Fin d→ℕ} {T : IntegerRectangularTiling d K₀}
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)
variable {K : ℕ} {i : Fin d} {C : Fin d→ℝ≥0}

theorem QuantitativeEndpointSkeletonCarrierMaps.projectedMap_unit_close
    (F : QuantitativeEndpointSkeletonCarrierMaps T (2*D.power+1) K i (d+1) C)
    (ε δ : ℝ)
    (hmod : ∀A B : ℤ,∀p q : IntervalCarriers.Realization (2*D.power+1) K A B,
      dist p q<δ→dist (D.carrierProjection K A B p) (D.carrierProjection K A B q)<ε)
    (j : Fin d) (hj : (C j : ℝ)<δ) (z : RealCoordinates d) (n : ℤ)
    (x y : ℝ) (hx : x∈Set.Icc (n : ℝ) ((n : ℝ)+1))
    (hy : y∈Set.Icc (n : ℝ) ((n : ℝ)+1)) :
    dist (F.toSkeletonCarrierMaps.projectedMap D (Function.update z j x))
      (F.toSkeletonCarrierMaps.projectedMap D (Function.update z j y))<ε := by
  obtain ⟨R,hR,hxR,hyR,_,_⟩ := F.toSkeletonCarrierMaps.projectedMap_unit_interval_cell D j z n x y hx hy
  apply F.toSkeletonCarrierMaps.projectedMap_close_in_cell D ε δ hmod R hR _ _ hxR hyR
  have hb := F.coordinate_bounds R hR R.rank_lt_succ_dimension j
    ⟨Function.update z j x,hxR⟩ ⟨Function.update z j y,hyR⟩ (by
      intro k hk
      simp only [Function.update_of_ne hk])
  have hxy : |x-y|≤1 := abs_le.mpr ⟨by linarith [hx.1,hy.2],by linarith [hx.2,hy.1]⟩
  have hc : (C j : ℝ)*|x-y|≤(C j : ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hxy (C j).coe_nonneg
  have hb' : dist (F.map R hR R.rank_lt_succ_dimension ⟨Function.update z j x,hxR⟩)
      (F.map R hR R.rank_lt_succ_dimension ⟨Function.update z j y,hyR⟩)≤(C j : ℝ)*|x-y| := by
    simpa using hb
  exact lt_of_le_of_lt (hb'.trans hc) hj

end
end AbelianTargets
