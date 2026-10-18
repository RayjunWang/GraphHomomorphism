import AbelianTargets.CanonicalIntervalContractions
import AbelianTargets.AtlasBoundaryTranslation

/-! One fixed family of contractions at zero-based interval widths gives
a literal contraction provider on all atlas cells, with exact translation
covariance. There is no new choice at a translated cell. -/

namespace AbelianTargets
open scoped unitInterval NNReal
noncomputable section
variable {d m K S : ℕ} {J : ℝ≥0}
variable (H : IntervalCarriers.NormalizedContractionFamily m K S J)

theorem normalizedWidth_map_congr (n n' : ℕ) (he : n=n')
    (hn : 0<n) (hn' : 0<n') (hS : n≤S) (hS' : n'≤S)
    (A B : ℤ) (hb : (n:ℤ)+A=B) (hb' : (n':ℤ)+A=B)
    (p : IntervalCarriers.Realization m K A B) (t : I) :
    (H.atWidthInterval n hn hS A B hb).map (p,t)=
      (H.atWidthInterval n' hn' hS' A B hb').map (p,t) := by
  subst n'
  rfl

def canonicalCellContraction (i : Fin d) (R : RectangularCell d)
    (hi : R.lower i<R.upper i) (hS : (R.upper i-R.lower i).toNat≤S) :
    ControlledContraction (cellLeftPoint m K i R) (IntervalCarriers.uniformCarrierSpeed m K) J :=
  (H.atWidthInterval (R.upper i-R.lower i).toNat (by omega) hS
    (R.lower i) (R.upper i)
    (by rw [Int.toNat_of_nonneg (by omega : 0≤R.upper i-R.lower i)] <;> omega)).rebase rfl

theorem canonicalCellContraction_translate (i : Fin d) (R : RectangularCell d)
    (hi : R.lower i<R.upper i) (hS : (R.upper i-R.lower i).toNat≤S)
    (a : Fin d→ℤ) (p : CellIntervalCarrier m K i R) (t : I) :
    (canonicalCellContraction H i (R.translate a) (by dsimp [RectangularCell.translate]; omega)
      (by simpa [RectangularCell.translate] using hS)).map (cellIntervalTranslate i a R p,t)=
      cellIntervalTranslate i a R ((canonicalCellContraction H i R hi hS).map (p,t)) := by
  simp only [canonicalCellContraction,ControlledContraction.rebase_map,
    RectangularCell.translate]
  have hw : R.upper i+a i-(R.lower i+a i)=R.upper i-R.lower i := by omega
  rw [normalizedWidth_map_congr H _ (R.upper i-R.lower i).toNat (congrArg Int.toNat hw)
    _ (by omega) _ hS _ _ _
    (by rw [Int.toNat_of_nonneg (by omega : 0≤R.upper i-R.lower i)]; omega)]
  exact H.atWidthInterval_shift (R.upper i-R.lower i).toNat (by omega) hS
    (R.lower i) (R.upper i) (R.lower i+a i) (R.upper i+a i) (a i)
    (by rw [Int.toNat_of_nonneg (by omega : 0≤R.upper i-R.lower i)] <;> omega) rfl rfl p t

def canonicalAtlasContractionProvider {K₀ : Fin d→ℕ}
    (T : IntegerRectangularTiling d K₀) (i : Fin d) (hS : K₀ i≤S)
    (R : RectangularCell d) (hR : R∈T.cells) (hi : R.lower i<R.upper i) :
    ControlledContraction (cellLeftPoint m K i R) (IntervalCarriers.uniformCarrierSpeed m K) J :=
  canonicalCellContraction H i R hi (by
    have hh := T.cells_bounded hR i
    omega)

end
end AbelianTargets
