import AbelianTargets.IntegerPrismEstimates
import AbelianTargets.ProbabilityPushDirac

namespace AbelianTargets
noncomputable section
variable {d : ℕ} {m K : ℕ} {i : Fin d}

def cellBottomVertex (R : RectangularCell d) (i : Fin d) (a : ℤ)
    (ha : R.lower i≤a) (hb : a≤R.upper i) : IntervalCarriers.CarrierVertex K (R.lower i) (R.upper i) :=
  ⟨(a,0),IntervalCarriers.mem_carrierVertices.mpr ⟨ha,hb,Nat.zero_le K⟩⟩

def cellBottomPoint (R : RectangularCell d) (i : Fin d) (a : ℤ)
    (ha : R.lower i≤a) (hb : a≤R.upper i) : CellIntervalCarrier m K i R :=
  IntervalCarriers.point (cellBottomVertex R i a ha hb)

theorem cellIntervalInclude_bottomPoint {Q R : RectangularCell d}
    (hsub : Q.closedBox⊆R.closedBox) (a : ℤ) (ha : Q.lower i≤a) (hb : a≤Q.upper i) :
    cellIntervalInclude (m := m) (K := K) i hsub (cellBottomPoint Q i a ha hb)=
      cellBottomPoint R i a
        (((RectangularCell.closedBox_subset_iff Q R).mp hsub i).1.trans ha)
        (hb.trans ((RectangularCell.closedBox_subset_iff Q R).mp hsub i).2) := by
  apply Subtype.ext
  change Probability.push _ (Probability.dirac _)=Probability.dirac _
  rw [Probability.push_dirac]
  rfl

def cellLeftPoint (m K : ℕ) (i : Fin d) (R : RectangularCell d) : CellIntervalCarrier m K i R :=
  cellBottomPoint R i (R.lower i) le_rfl (R.ordered i)

def cellRightPoint (m K : ℕ) (i : Fin d) (R : RectangularCell d) : CellIntervalCarrier m K i R :=
  cellBottomPoint R i (R.upper i) (R.ordered i) le_rfl

namespace LowerCellCarrierMaps
variable {K₀ : Fin d→ℕ} {T : IntegerRectangularTiling d K₀} {R : RectangularCell d}

def EndpointValues (F : LowerCellCarrierMaps T m K i R) : Prop :=
  ∀ (Q : RectangularCell d) (hQ : Q∈T.cells) (hr : Q.rank<R.rank)
    (z : CellClosedDomain Q),
    (z.val i=(Q.lower i : ℝ) → F.map Q hQ hr z=cellLeftPoint m K i Q) ∧
    (z.val i=(Q.upper i : ℝ) → F.map Q hQ hr z=cellRightPoint m K i Q)

theorem boundaryValue_left (F : LowerCellCarrierMaps T m K i R) (hR : R∈T.cells)
    (hF : F.EndpointValues) (z : CellBoundaryDomain R)
    (hz : z.val i=(R.lower i : ℝ)) : F.boundaryValue hR z=cellLeftPoint m K i R := by
  let Q := T.pointCell z.val
  have hQ : Q∈T.cells := ⟨z.val,rfl⟩
  have hr : Q.rank<R.rank := T.pointCell_rank_lt_cell_boundary hR z.property
  have hQR := T.pointCell_subset_cell hR z.property.1
  have hzQ : z.val∈Q.closedBox := Q.relativeInterior_subset (T.mem_relativeInterior_pointCell z.val)
  have hlo : Q.lower i=R.lower i := by
    apply le_antisymm
    · exact_mod_cast (show (Q.lower i : ℝ)≤(R.lower i : ℝ) by rw [←hz]; exact (hzQ i).1)
    · exact ((RectangularCell.closedBox_subset_iff Q R).mp hQR i).1
  rw [F.boundaryValue_eq hR hQ hr hQR z hzQ]
  rw [(hF Q hQ hr ⟨z.val,hzQ⟩).1 (by simpa [hlo] using hz)]
  unfold cellLeftPoint
  rw [cellIntervalInclude_bottomPoint]
  simp only [hlo]

theorem boundaryValue_right (F : LowerCellCarrierMaps T m K i R) (hR : R∈T.cells)
    (hF : F.EndpointValues) (z : CellBoundaryDomain R)
    (hz : z.val i=(R.upper i : ℝ)) : F.boundaryValue hR z=cellRightPoint m K i R := by
  let Q := T.pointCell z.val
  have hQ : Q∈T.cells := ⟨z.val,rfl⟩
  have hr : Q.rank<R.rank := T.pointCell_rank_lt_cell_boundary hR z.property
  have hQR := T.pointCell_subset_cell hR z.property.1
  have hzQ : z.val∈Q.closedBox := Q.relativeInterior_subset (T.mem_relativeInterior_pointCell z.val)
  have hhi : Q.upper i=R.upper i := by
    apply le_antisymm
    · exact ((RectangularCell.closedBox_subset_iff Q R).mp hQR i).2
    · exact_mod_cast (show (R.upper i : ℝ)≤(Q.upper i : ℝ) by rw [←hz]; exact (hzQ i).2)
  rw [F.boundaryValue_eq hR hQ hr hQR z hzQ]
  rw [(hF Q hQ hr ⟨z.val,hzQ⟩).2 (by simpa [hhi] using hz)]
  unfold cellRightPoint
  rw [cellIntervalInclude_bottomPoint]
  simp only [hhi]

end LowerCellCarrierMaps
end
end AbelianTargets
