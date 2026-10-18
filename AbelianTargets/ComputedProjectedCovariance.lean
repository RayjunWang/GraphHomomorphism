import AbelianTargets.DeterministicAtlasCovariance

/-! Covariance of a checked full-rank atlas gives covariance of its actual support projection. -/
namespace AbelianTargets
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SkeletonCarrierMaps
variable {d:ℕ} {K₀ K₁:Fin d→ℕ}
variable {T:IntegerRectangularTiling d K₀} {U:IntegerRectangularTiling d K₁}
variable {W:Type*} [Fintype W] {H:SimpleGraph W} (D:SupportTorsionData H)
variable {K:ℕ} {i:Fin d}

theorem TranslationCovariant.projectedMap_eq
    {F:SkeletonCarrierMaps T (2*D.power+1) K i (d+1)}
    {G:SkeletonCarrierMaps U (2*D.power+1) K i (d+1)}
    {a:Fin d→ℤ} {hcell:∀R:RectangularCell d,R∈T.cells→R.translate a∈U.cells}
    (hc:TranslationCovariant F G a hcell) (z:RealCoordinates d) :
    G.projectedMap D (translateCoordinates a z)=
      SupportPair.paritySwap H (a i) (F.projectedMap D z) := by
  exact F.projectedMap_translate_of_cell_maps D G a hcell
    (fun R hR z=>hc R hR R.rank_lt_succ_dimension z) z

end SkeletonCarrierMaps
end
end AbelianTargets
