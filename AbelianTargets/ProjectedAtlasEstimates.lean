import AbelianTargets.ProjectedAtlasMaps
import AbelianTargets.AtlasQuantitativeRecursion

/-! Coordinate estimates survive the actual carrier projection with its common modulus. -/
namespace AbelianTargets.QuantitativeEndpointSkeletonCarrierMaps
noncomputable section
open scoped NNReal
set_option backward.isDefEq.respectTransparency false
variable {d:ℕ} {K₀:Fin d→ℕ} {T:IntegerRectangularTiling d K₀}
variable {W:Type*} [Fintype W] {H:SimpleGraph W} (D:SupportTorsionData H)
variable {K:ℕ} {i:Fin d} {C:Fin d→ℝ≥0}
variable (F:QuantitativeEndpointSkeletonCarrierMaps T (2*D.power+1) K i (d+1) C)

theorem projected_coordinate_unit_close (ε δ:ℝ)
    (hmod:∀A B:ℤ,∀p q:IntervalCarriers.Realization (2*D.power+1) K A B,
      dist p q<δ→dist (D.carrierProjection K A B p) (D.carrierProjection K A B q)<ε)
    (j:Fin d) (z:RealCoordinates d) (n:ℤ) (x y:ℝ)
    (hx:x∈Set.Icc (n:ℝ) ((n:ℝ)+1)) (hy:y∈Set.Icc (n:ℝ) ((n:ℝ)+1))
    (hsmall:(C j:ℝ)*|x-y|<δ) :
    dist (F.toSkeletonCarrierMaps.projectedMap D (Function.update z j x))
      (F.toSkeletonCarrierMaps.projectedMap D (Function.update z j y))<ε := by
  obtain ⟨R,hR,hxR,hyR,hprojx,hprojy⟩ :=
    F.toSkeletonCarrierMaps.projectedMap_unit_interval_cell D j z n x y hx hy
  rw [hprojx,hprojy]
  apply hmod
  have hb := F.coordinate_bounds R hR R.rank_lt_succ_dimension j
    ⟨Function.update z j x,hxR⟩ ⟨Function.update z j y,hyR⟩
    (by intro k hk; simp only [Function.update_of_ne hk])
  have hb' : dist (F.map R hR R.rank_lt_succ_dimension ⟨Function.update z j x,hxR⟩)
      (F.map R hR R.rank_lt_succ_dimension ⟨Function.update z j y,hyR⟩)≤(C j:ℝ)*|x-y| := by
    simpa using hb
  exact hb'.trans_lt hsmall

theorem projected_integer_step_close (ε δ:ℝ)
    (hmod:∀A B:ℤ,∀p q:IntervalCarriers.Realization (2*D.power+1) K A B,
      dist p q<δ→dist (D.carrierProjection K A B p) (D.carrierProjection K A B q)<ε)
    (j:Fin d) (z:RealCoordinates d) (n:ℤ) (hsmall:(C j:ℝ)<δ) :
    dist (F.toSkeletonCarrierMaps.projectedMap D (Function.update z j (n:ℝ)))
      (F.toSkeletonCarrierMaps.projectedMap D (Function.update z j ((n:ℝ)+1)))<ε := by
  apply F.projected_coordinate_unit_close D ε δ hmod j z n
    (n:ℝ) ((n:ℝ)+1) (by constructor <;> linarith) (by constructor <;> linarith)
  simpa using hsmall

end
end AbelianTargets.QuantitativeEndpointSkeletonCarrierMaps
