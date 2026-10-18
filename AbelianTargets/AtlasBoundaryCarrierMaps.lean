import AbelianTargets.RegularAnisotropicAtlas
import AbelianTargets.CarrierIntervalInclusion

/-! Compatible maps on actual lower-rank strata lift continuously into
the literal carrier of a parent cell. The canonical value uses the true
point cell, and the finite closed boundary cover proves continuity. -/

namespace AbelianTargets
noncomputable section

namespace IntegerRectangularTiling
variable {d : ℕ} {K₀ : Fin d → ℕ} (T : IntegerRectangularTiling d K₀)

theorem pointCell_subset_cell {R : RectangularCell d} (hR : R ∈ T.cells)
    {z : RealCoordinates d} (hz : z ∈ R.closedBox) :
    (T.pointCell z).closedBox ⊆ R.closedBox := by
  obtain ⟨x,rfl⟩ := hR
  exact T.pointCell_closed_mono x z hz

theorem pointCell_rank_lt_cell_boundary {R : RectangularCell d} (hR : R ∈ T.cells)
    {z : RealCoordinates d} (hz : z ∈ R.boundary) : (T.pointCell z).rank < R.rank := by
  obtain ⟨x,rfl⟩ := hR
  exact T.pointCell_rank_lt_on_boundary x z hz

end IntegerRectangularTiling

variable {d : ℕ}

abbrev CellClosedDomain (R : RectangularCell d) := {z : RealCoordinates d // z ∈ R.closedBox}
abbrev CellBoundaryDomain (R : RectangularCell d) := {z : RealCoordinates d // z ∈ R.boundary}
abbrev CellIntervalCarrier (m K : ℕ) (i : Fin d) (R : RectangularCell d) :=
  IntervalCarriers.Realization m K (R.lower i) (R.upper i)

def cellIntervalInclude {m K : ℕ} (i : Fin d) {Q R : RectangularCell d}
    (hsub : Q.closedBox ⊆ R.closedBox) : CellIntervalCarrier m K i Q → CellIntervalCarrier m K i R :=
  IntervalCarriers.intervalInclusion
    ((RectangularCell.closedBox_subset_iff Q R).mp hsub i).1
    ((RectangularCell.closedBox_subset_iff Q R).mp hsub i).2

theorem cellIntervalInclude_isometry {m K : ℕ} (i : Fin d) {Q R : RectangularCell d}
    (hsub : Q.closedBox ⊆ R.closedBox) : Isometry (cellIntervalInclude (m := m) (K := K) i hsub) :=
  IntervalCarriers.intervalInclusion_isometry _ _

theorem cellIntervalInclude_comp {m K : ℕ} (i : Fin d) {P Q R : RectangularCell d}
    (hPQ : P.closedBox ⊆ Q.closedBox) (hQR : Q.closedBox ⊆ R.closedBox)
    (hPR : P.closedBox ⊆ R.closedBox) (p : CellIntervalCarrier m K i P) :
    cellIntervalInclude i hQR (cellIntervalInclude i hPQ p)=cellIntervalInclude i hPR p :=
  IntervalCarriers.intervalInclusion_comp _ _ _ _ p

structure LowerCellCarrierMaps {K₀ : Fin d → ℕ} (T : IntegerRectangularTiling d K₀)
    (m K : ℕ) (i : Fin d) (R : RectangularCell d) where
  map : ∀ Q : RectangularCell d,Q ∈ T.cells → Q.rank < R.rank →
    C(CellClosedDomain Q,CellIntervalCarrier m K i Q)
  compatible : ∀ (P Q : RectangularCell d) (hP : P ∈ T.cells) (hQ : Q ∈ T.cells)
    (hrP : P.rank < R.rank) (hrQ : Q.rank < R.rank) (hsub : P.closedBox ⊆ Q.closedBox)
    (z : CellClosedDomain P),
    cellIntervalInclude i hsub (map P hP hrP z)=map Q hQ hrQ ⟨z.val,hsub z.property⟩

namespace LowerCellCarrierMaps
variable {K₀ : Fin d → ℕ} {T : IntegerRectangularTiling d K₀}
variable {m K : ℕ} {i : Fin d} {R : RectangularCell d}
variable (F : LowerCellCarrierMaps T m K i R) (hR : R ∈ T.cells)

def boundaryValue (z : CellBoundaryDomain R) : CellIntervalCarrier m K i R :=
  cellIntervalInclude i (T.pointCell_subset_cell hR z.property.1)
    (F.map (T.pointCell z.val) ⟨z.val,rfl⟩ (T.pointCell_rank_lt_cell_boundary hR z.property)
      ⟨z.val,(T.pointCell z.val).relativeInterior_subset (T.mem_relativeInterior_pointCell z.val)⟩)

theorem boundaryValue_eq {Q : RectangularCell d} (hQ : Q ∈ T.cells)
    (hrQ : Q.rank < R.rank) (hQR : Q.closedBox ⊆ R.closedBox)
    (z : CellBoundaryDomain R) (hzQ : z.val ∈ Q.closedBox) :
    F.boundaryValue hR z=cellIntervalInclude i hQR (F.map Q hQ hrQ ⟨z.val,hzQ⟩) := by
  let P := T.pointCell z.val
  have hP : P ∈ T.cells := ⟨z.val,rfl⟩
  have hrP : P.rank < R.rank := T.pointCell_rank_lt_cell_boundary hR z.property
  have hPQ := T.pointCell_subset_cell hQ hzQ
  have hPR := T.pointCell_subset_cell hR z.property.1
  let zp : CellClosedDomain P :=
    ⟨z.val,P.relativeInterior_subset (T.mem_relativeInterior_pointCell z.val)⟩
  change cellIntervalInclude i hPR (F.map P hP hrP zp)=_
  rw [← cellIntervalInclude_comp i hPQ hQR hPR]
  rw [F.compatible P Q hP hQ hrP hrQ hPQ zp]

theorem continuous_boundaryValue : Continuous (F.boundaryValue hR) := by
  classical
  let J := {Q : RectangularCell d // Q ∈ T.boundaryCells R}
  letI : Fintype J := Fintype.ofFinset (T.boundaryCells R) (by simp)
  let A : J → Set (CellBoundaryDomain R) := fun Q => {z | z.val ∈ Q.val.closedBox}
  apply (locallyFinite_of_finite A).continuous
  · ext z
    simp only [Set.mem_univ,iff_true]
    have hP : T.pointCell z.val ∈ T.boundaryCells R := (T.mem_boundaryCells R _).mpr
      ⟨⟨z.val,rfl⟩,T.pointCell_subset_cell hR z.property.1,
        T.pointCell_rank_lt_cell_boundary hR z.property⟩
    exact Set.mem_iUnion.mpr ⟨⟨T.pointCell z.val,hP⟩,
      (T.pointCell z.val).relativeInterior_subset (T.mem_relativeInterior_pointCell z.val)⟩
  · intro Q
    exact Q.val.isClosed_closedBox.preimage continuous_subtype_val
  · intro Q
    obtain ⟨hQc,hQR,hrQ⟩ := (T.mem_boundaryCells R Q.val).mp Q.property
    apply continuousOn_iff_continuous_restrict.mpr
    let lift : {z : CellBoundaryDomain R // z ∈ A Q} → CellClosedDomain Q.val :=
      fun z => ⟨z.val.val,z.property⟩
    have hl : Continuous lift := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    have hc := (cellIntervalInclude_isometry (m := m) (K := K) i hQR).continuous.comp
      ((F.map Q.val hQc hrQ).continuous.comp hl)
    convert hc using 1
    funext z
    exact F.boundaryValue_eq hR hQc hrQ hQR z.val z.property

def boundaryMap : C(CellBoundaryDomain R,CellIntervalCarrier m K i R) :=
  ⟨F.boundaryValue hR,F.continuous_boundaryValue hR⟩

end LowerCellCarrierMaps
end
end AbelianTargets
