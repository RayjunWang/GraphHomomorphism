import AbelianTargets.AtlasControlledCellExtension
import AbelianTargets.IntegerPrismFillTranslation

namespace AbelianTargets
noncomputable section
open scoped NNReal
variable {d : ℕ} {K₀ : Fin d→ℕ} {T T' : IntegerRectangularTiling d K₀}
variable {m K : ℕ} {i : Fin d} {R : RectangularCell d}

namespace LowerCellCarrierMaps

/-- The boundary operator inspects only the finite actual boundary cells
of its parent. A different atlas agreeing on those cells gives the same value. -/
theorem boundaryValue_eq_of_finite_lower_agreement
    (F : LowerCellCarrierMaps T m K i R) (G : LowerCellCarrierMaps T' m K i R)
    (hR : R∈T.cells) (hR' : R∈T'.cells)
    (hcell : ∀ Q∈T.boundaryCells R,Q∈T'.cells)
    (hmap : ∀ (Q : RectangularCell d) (hQ : Q∈T.boundaryCells R)
      (hQc : Q∈T.cells) (hQc' : Q∈T'.cells) (hr : Q.rank<R.rank) (z : CellClosedDomain Q),
      F.map Q hQc hr z=G.map Q hQc' hr z)
    (z : CellBoundaryDomain R) : F.boundaryValue hR z=G.boundaryValue hR' z := by
  let Q := T.pointCell z.val
  have hQ : Q∈T.cells := ⟨z.val,rfl⟩
  have hr : Q.rank<R.rank := T.pointCell_rank_lt_cell_boundary hR z.property
  have hQR := T.pointCell_subset_cell hR z.property.1
  have hb : Q∈T.boundaryCells R := (T.mem_boundaryCells R Q).mpr ⟨hQ,hQR,hr⟩
  have hQ' := hcell Q hb
  have hzQ : z.val∈Q.closedBox := Q.relativeInterior_subset (T.mem_relativeInterior_pointCell z.val)
  rw [F.boundaryValue_eq hR hQ hr hQR z hzQ,G.boundaryValue_eq hR' hQ' hr hQR z hzQ]
  rw [hmap Q hb hQ hQ' hr ⟨z.val,hzQ⟩]

theorem controlledCellExtension_map_ext
    (F : LowerCellCarrierMaps T m K i R) (G : LowerCellCarrierMaps T' m K i R)
    (hR : R∈T.cells) (hR' : R∈T'.cells) (hF : F.EndpointValues) (hG : G.EndpointValues)
    (C C' : Fin d→ℝ≥0) (hC : F.CoordinateBounds C) (hC' : G.CoordinateBounds C')
    (hi : R.lower i<R.upper i) {D J : ℝ≥0}
    (H : ControlledContraction (cellLeftPoint m K i R) D J)
    (hmap : ∀ z : CellBoundaryDomain R,F.boundaryValue hR z=G.boundaryValue hR' z)
    (z : CellClosedDomain R) :
    (F.controlledCellExtension hR hF C hC hi H).map z=
      (G.controlledCellExtension hR' hG C' hC' hi H).map z :=
  (F.controlledPrismData hR hF C hC hi).fill_ext
    (G.controlledPrismData hR' hG C' hC' hi) H hmap hi z

end LowerCellCarrierMaps
end
end AbelianTargets
