import AbelianTargets.ProjectedAtlasCovariance
import AbelianTargets.AtlasEndpointRecursion

/-! Translation covariance propagates through the literal rank recursion. -/
namespace AbelianTargets
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace SkeletonCarrierMaps
variable {d:ℕ} {K₀ K₁:Fin d→ℕ}
variable {T:IntegerRectangularTiling d K₀} {U:IntegerRectangularTiling d K₁}
variable {m K n:ℕ} {i:Fin d}

def TranslationCovariant (F:SkeletonCarrierMaps T m K i n) (G:SkeletonCarrierMaps U m K i n)
    (a:Fin d→ℤ) (hcell:∀R:RectangularCell d,R∈T.cells→R.translate a∈U.cells) : Prop :=
  ∀(R:RectangularCell d)(hR:R∈T.cells)(hr:R.rank<n)(z:CellClosedDomain R),
    G.map (R.translate a) (hcell R hR) (by simpa only [RectangularCell.rank_translate] using hr) (R.translateClosedPoint a z)=
      IntervalCarriers.realizationTranslation (a i) (F.map R hR hr z)

theorem empty_translationCovariant (a:Fin d→ℤ)
    (hcell:∀R:RectangularCell d,R∈T.cells→R.translate a∈U.cells) :
    TranslationCovariant (empty:SkeletonCarrierMaps T m K i 0)
      (empty:SkeletonCarrierMaps U m K i 0) a hcell := by
  intro R hR hr z
  exact (Nat.not_lt_zero _ hr).elim

end SkeletonCarrierMaps

namespace EndpointSkeletonCarrierMaps
variable {d:ℕ} {K₀ K₁:Fin d→ℕ}
variable {T:IntegerRectangularTiling d K₀} {U:IntegerRectangularTiling d K₁}
variable {m K n:ℕ} {i:Fin d}
variable (F:EndpointSkeletonCarrierMaps T m K i n) (G:EndpointSkeletonCarrierMaps U m K i n)

theorem next_translationCovariant (a:Fin d→ℤ)
    (hcell:∀R:RectangularCell d,R∈T.cells→R.translate a∈U.cells)
    (hold:SkeletonCarrierMaps.TranslationCovariant F.toSkeletonCarrierMaps G.toSkeletonCarrierMaps a hcell)
    (extendF:∀(R:RectangularCell d)(hR:R∈T.cells)(he:R.rank=n),
      EndpointCellCarrierExtension (F.toSkeletonCarrierMaps.lowerFamily R he) hR)
    (extendG:∀(R:RectangularCell d)(hR:R∈U.cells)(he:R.rank=n),
      EndpointCellCarrierExtension (G.toSkeletonCarrierMaps.lowerFamily R he) hR)
    (hnew:∀(R:RectangularCell d)(hR:R∈T.cells)(he:R.rank=n)(z:CellClosedDomain R),
      (extendG (R.translate a) (hcell R hR) (by simpa only [RectangularCell.rank_translate] using he)).map (R.translateClosedPoint a z)=
        IntervalCarriers.realizationTranslation (a i) ((extendF R hR he).map z)) :
    SkeletonCarrierMaps.TranslationCovariant (F.next extendF).toSkeletonCarrierMaps
      (G.next extendG).toSkeletonCarrierMaps a hcell := by
  intro R hR hr z
  change G.nextMap extendG (R.translate a) (hcell R hR) (by simpa only [RectangularCell.rank_translate] using hr)
    (R.translateClosedPoint a z)=IntervalCarriers.realizationTranslation (a i)
      (F.nextMap extendF R hR hr z)
  by_cases h:R.rank<n
  · have ht:(R.translate a).rank<n := by simpa only [RectangularCell.rank_translate] using h
    simp only [nextMap,dif_pos h,dif_pos ht]
    exact hold R hR h z
  · have ht:¬(R.translate a).rank<n := by simpa only [RectangularCell.rank_translate] using h
    have he:R.rank=n := by omega
    simp only [nextMap,dif_neg h,dif_neg ht]
    exact hnew R hR he z

end EndpointSkeletonCarrierMaps
end
end AbelianTargets
