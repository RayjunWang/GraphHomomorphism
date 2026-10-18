import AbelianTargets.ProjectedAtlasMaps
import AbelianTargets.IntegerPrismTranslation

/-! Literal covariance of the global projected map follows from cell-map covariance. -/
namespace AbelianTargets
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace IntegerRectangularTiling
theorem translated_cell_mem {d:ℕ} {K₀:Fin d→ℕ} (T:IntegerRectangularTiling d K₀)
    (a:Fin d→ℤ) {R:RectangularCell d} (hR:R∈T.cells) : R.translate a∈(T.translate a).cells := by
  obtain ⟨z,rfl⟩ := hR
  exact ⟨translateCoordinates a z,T.pointCell_translate a z⟩
end IntegerRectangularTiling

namespace SkeletonCarrierMaps
variable {d:ℕ} {K₀ K₁:Fin d→ℕ}
variable {T:IntegerRectangularTiling d K₀} {U:IntegerRectangularTiling d K₁}
variable {W:Type*} [Fintype W] {H:SimpleGraph W} (D:SupportTorsionData H)
variable {K:ℕ} {i:Fin d}
variable (F:SkeletonCarrierMaps T (2*D.power+1) K i (d+1))

theorem projectedMap_translate_of_cell_maps
    (G:SkeletonCarrierMaps U (2*D.power+1) K i (d+1)) (a:Fin d→ℤ)
    (hcell:∀R:RectangularCell d,R∈T.cells→R.translate a∈U.cells)
    (hmap:∀(R:RectangularCell d)(hR:R∈T.cells)(z:CellClosedDomain R),
      G.map (R.translate a) (hcell R hR) (R.translate a).rank_lt_succ_dimension
        (R.translateClosedPoint a z)=
          IntervalCarriers.realizationTranslation (a i)
            (F.map R hR R.rank_lt_succ_dimension z)) (z:RealCoordinates d) :
    G.projectedMap D (translateCoordinates a z)=
      SupportPair.paritySwap H (a i) (F.projectedMap D z) := by
  let R := T.pointCell z
  have hR : R∈T.cells := ⟨z,rfl⟩
  have hz : z∈R.closedBox := R.relativeInterior_subset (T.mem_relativeInterior_pointCell z)
  have hza : translateCoordinates a z∈(R.translate a).closedBox :=
    (R.mem_closedBox_translateCoordinates a z).mpr hz
  rw [G.projectedMap_eq_cell D (R.translate a) (hcell R hR) _ hza]
  have htrans := hmap R hR ⟨z,hz⟩
  change G.map (R.translate a) (hcell R hR) (R.translate a).rank_lt_succ_dimension
    ⟨translateCoordinates a z,hza⟩=IntervalCarriers.realizationTranslation (a i)
      (F.map R hR R.rank_lt_succ_dimension ⟨z,hz⟩) at htrans
  rw [htrans]
  change D.carrierProjection K (R.lower i+a i) (R.upper i+a i)
      (IntervalCarriers.realizationTranslation (a i) (F.map R hR R.rank_lt_succ_dimension ⟨z,hz⟩))=_
  rw [D.carrierProjection_translate,←F.projectedMap_eq_cell D R hR z hz]

theorem projectedMap_translate
    (a:Fin d→ℤ)
    (G:SkeletonCarrierMaps (T.translate a) (2*D.power+1) K i (d+1))
    (hmap:∀(R:RectangularCell d)(hR:R∈T.cells)(z:CellClosedDomain R),
      G.map (R.translate a) (T.translated_cell_mem a hR) (R.translate a).rank_lt_succ_dimension
        (R.translateClosedPoint a z)=
          IntervalCarriers.realizationTranslation (a i)
            (F.map R hR R.rank_lt_succ_dimension z)) (z:RealCoordinates d) :
    G.projectedMap D (translateCoordinates a z)=
      SupportPair.paritySwap H (a i) (F.projectedMap D z) :=
  F.projectedMap_translate_of_cell_maps D G a (fun R hR=>T.translated_cell_mem a hR) hmap z

end SkeletonCarrierMaps
end
end AbelianTargets
