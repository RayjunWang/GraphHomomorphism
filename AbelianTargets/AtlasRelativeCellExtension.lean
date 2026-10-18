import AbelianTargets.AtlasCarrierEndpoints

namespace AbelianTargets
noncomputable section
open scoped NNReal unitInterval
variable {d : ℕ} {K₀ : Fin d→ℕ} {T : IntegerRectangularTiling d K₀}
variable {m K : ℕ} {i : Fin d} {R : RectangularCell d}

structure EndpointCellCarrierExtension (F : LowerCellCarrierMaps T m K i R)
    (hR : R∈T.cells) extends CellCarrierExtension F hR where
  source : ∀ z : CellClosedDomain R,z.val i=(R.lower i : ℝ) → map z=cellLeftPoint m K i R
  target : ∀ z : CellClosedDomain R,z.val i=(R.upper i : ℝ) → map z=cellRightPoint m K i R

namespace LowerCellCarrierMaps
variable (F : LowerCellCarrierMaps T m K i R) (hR : R∈T.cells) (hF : F.EndpointValues)

def prismBoundaryData (S B : ℝ≥0)
    (hpath : ∀ v : ConeSphere (R.ActiveTransverse i→ℝ),LipschitzWith S
      (fun r => F.boundaryValue hR (prismBoundaryPoint R i v r)))
    (htrans : ∀ r : unitInterval,LipschitzWith B
      (fun v : ConeSphere (R.ActiveTransverse i→ℝ) =>
        F.boundaryValue hR (prismBoundaryPoint R i v r))) :
    PrismBoundaryData R i (cellLeftPoint m K i R) (cellRightPoint m K i R) S B where
  map := F.boundaryMap hR
  source := F.boundaryValue_left hR hF
  target := F.boundaryValue_right hR hF
  path_lipschitz := hpath
  transverse := htrans

/-- Actual relative extension when the distinguished side has positive
length. Its only analytic input is the stated quantitative boundary data. -/
def relativeCellExtension {S B D J : ℝ≥0} (hi : R.lower i<R.upper i)
    (H : ControlledContraction (cellLeftPoint m K i R) D J)
    (hpath : ∀ v : ConeSphere (R.ActiveTransverse i→ℝ),LipschitzWith S
      (fun r => F.boundaryValue hR (prismBoundaryPoint R i v r)))
    (htrans : ∀ r : unitInterval,LipschitzWith B
      (fun v : ConeSphere (R.ActiveTransverse i→ℝ) =>
        F.boundaryValue hR (prismBoundaryPoint R i v r))) :
    EndpointCellCarrierExtension F hR where
  map := (F.prismBoundaryData hR hF S B hpath htrans).continuousMap H hi
  boundary := (F.prismBoundaryData hR hF S B hpath htrans).fill_boundary H hi
  source := (F.prismBoundaryData hR hF S B hpath htrans).fill_source H hi
  target := (F.prismBoundaryData hR hF S B hpath htrans).fill_target H hi

/-- A stratum with collapsed distinguished coordinate is assigned its
literal height-zero vertex; the already-built boundary has the same value. -/
def collapsedCellExtension (hi : R.lower i=R.upper i) : EndpointCellCarrierExtension F hR where
  map := ContinuousMap.const _ (cellLeftPoint m K i R)
  boundary z := by
    apply (F.boundaryValue_left hR hF z ?_).symm
    exact le_antisymm (by simpa [hi] using (z.property.1 i).2) (z.property.1 i).1
  source z hz := rfl
  target z hz := by
    change cellLeftPoint m K i R=cellRightPoint m K i R
    simp only [cellLeftPoint,cellRightPoint,cellBottomPoint,cellBottomVertex,hi]

end LowerCellCarrierMaps
end
end AbelianTargets
