import AbelianTargets.AtlasCarrierEndpoints
import AbelianTargets.IntegerPrismFillTranslation
import AbelianTargets.CarrierTranslationGeometry

namespace AbelianTargets
noncomputable section
variable {d : ℕ} {m K : ℕ} {i : Fin d}

def cellIntervalTranslate (i : Fin d) (a : Fin d→ℤ) (R : RectangularCell d) :
    CellIntervalCarrier m K i R→CellIntervalCarrier m K i (R.translate a) :=
  IntervalCarriers.realizationTranslation (a i)

theorem cellIntervalTranslate_isometry (i : Fin d) (a : Fin d→ℤ) (R : RectangularCell d) :
    Isometry (cellIntervalTranslate (m := m) (K := K) i a R) :=
  IntervalCarriers.realizationTranslation_isometry _

theorem closedBox_subset_translate {Q R : RectangularCell d} (a : Fin d→ℤ)
    (hQR : Q.closedBox⊆R.closedBox) : (Q.translate a).closedBox⊆(R.translate a).closedBox := by
  intro z hz
  have hQ := (Q.mem_closedBox_translateCoordinates a (translateCoordinates (-a) z)).mp
    (by simpa using hz)
  have hR := (R.mem_closedBox_translateCoordinates a (translateCoordinates (-a) z)).mpr (hQR hQ)
  simpa using hR

theorem cellIntervalInclude_translate {Q R : RectangularCell d} (a : Fin d→ℤ)
    (hQR : Q.closedBox⊆R.closedBox) (p : CellIntervalCarrier m K i Q) :
    cellIntervalTranslate i a R (cellIntervalInclude i hQR p)=
      cellIntervalInclude i (closedBox_subset_translate a hQR) (cellIntervalTranslate i a Q p) := by
  apply Subtype.ext
  change Probability.push _ (Probability.push _ p.val)=Probability.push _ (Probability.push _ p.val)
  rw [Probability.push_comp,Probability.push_comp]
  rfl

theorem cellLeftPoint_translate (i : Fin d) (a : Fin d→ℤ) (R : RectangularCell d) :
    cellIntervalTranslate i a R (cellLeftPoint m K i R)=cellLeftPoint m K i (R.translate a) := by
  apply Subtype.ext
  change Probability.push _ (Probability.dirac _)=Probability.dirac _
  rw [Probability.push_dirac]
  rfl

theorem cellRightPoint_translate (i : Fin d) (a : Fin d→ℤ) (R : RectangularCell d) :
    cellIntervalTranslate i a R (cellRightPoint m K i R)=cellRightPoint m K i (R.translate a) := by
  apply Subtype.ext
  change Probability.push _ (Probability.dirac _)=Probability.dirac _
  rw [Probability.push_dirac]
  rfl

namespace IntegerRectangularTiling
variable {K₀ : Fin d→ℕ} (T : IntegerRectangularTiling d K₀)

theorem cell_translate {Q : RectangularCell d} (hQ : Q∈T.cells) (a : Fin d→ℤ) :
    Q.translate a∈(T.translate a).cells := by
  obtain ⟨z,rfl⟩ := hQ
  exact ⟨translateCoordinates a z,T.pointCell_translate a z⟩

end IntegerRectangularTiling

namespace LowerCellCarrierMaps
variable {K₀ : Fin d→ℕ} {T : IntegerRectangularTiling d K₀} {R : RectangularCell d}

theorem boundaryValue_translate (F : LowerCellCarrierMaps T m K i R) (hR : R∈T.cells)
    (a : Fin d→ℤ) (G : LowerCellCarrierMaps (T.translate a) m K i (R.translate a))
    (hmap : ∀ (Q : RectangularCell d) (hQ : Q∈T.cells) (hr : Q.rank<R.rank)
      (z : CellClosedDomain Q),
      G.map (Q.translate a) (T.cell_translate hQ a)
        (by simpa only [RectangularCell.rank_translate] using hr) (Q.translateClosedPoint a z)=
        cellIntervalTranslate i a Q (F.map Q hQ hr z))
    (z : CellBoundaryDomain R) :
    G.boundaryValue (T.cell_translate hR a) (R.translateBoundaryPoint a z)=
      cellIntervalTranslate i a R (F.boundaryValue hR z) := by
  let Q := T.pointCell z.val
  have hQ : Q∈T.cells := ⟨z.val,rfl⟩
  have hr : Q.rank<R.rank := T.pointCell_rank_lt_cell_boundary hR z.property
  have hQR := T.pointCell_subset_cell hR z.property.1
  have hzQ : z.val∈Q.closedBox := Q.relativeInterior_subset (T.mem_relativeInterior_pointCell z.val)
  have hQ' := T.cell_translate hQ a
  have hr' : (Q.translate a).rank<(R.translate a).rank := by
    simpa only [RectangularCell.rank_translate] using hr
  have hQR' := closedBox_subset_translate a hQR
  have hzQ' : (R.translateBoundaryPoint a z).val∈(Q.translate a).closedBox :=
    (Q.mem_closedBox_translateCoordinates a z.val).mpr hzQ
  rw [G.boundaryValue_eq (T.cell_translate hR a) hQ' hr' hQR' _ hzQ']
  rw [F.boundaryValue_eq hR hQ hr hQR z hzQ]
  rw [cellIntervalInclude_translate]
  congr 1
  exact hmap Q hQ hr ⟨z.val,hzQ⟩

end LowerCellCarrierMaps
end
end AbelianTargets
