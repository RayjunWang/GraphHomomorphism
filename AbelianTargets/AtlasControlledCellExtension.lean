import AbelianTargets.AtlasRelativeCellExtension
import AbelianTargets.AtlasBoundaryPathBounds
import AbelianTargets.AtlasBoundaryTransverseBounds

namespace AbelianTargets
noncomputable section
open scoped NNReal unitInterval
variable {d : ℕ} {K₀ : Fin d→ℕ} {T : IntegerRectangularTiling d K₀}
variable {m K : ℕ} {i : Fin d} {R : RectangularCell d}

namespace LowerCellCarrierMaps

def CoordinateBounds (F : LowerCellCarrierMaps T m K i R) (C : Fin d→ℝ≥0) : Prop :=
  ∀ (k : Fin d) (Q : RectangularCell d) (hQ : Q∈T.cells) (hrQ : Q.rank<R.rank)
    (z : RealCoordinates d) (x y : ℝ)
    (hx : Function.update z k x∈Q.closedBox) (hy : Function.update z k y∈Q.closedBox),
    dist (F.map Q hQ hrQ ⟨Function.update z k x,hx⟩)
      (F.map Q hQ hrQ ⟨Function.update z k y,hy⟩)≤C k*|x-y|

variable (F : LowerCellCarrierMaps T m K i R) (hR : R∈T.cells) (hF : F.EndpointValues)
variable (C : Fin d→ℝ≥0) (hC : F.CoordinateBounds C)
variable (hi : R.lower i<R.upper i)

def controlledPrismData :
    PrismBoundaryData R i (cellLeftPoint m K i R) (cellRightPoint m K i R)
      (C i*(R.transverseWidth i).toNNReal) (prismTransverseBound R i C) :=
  F.prismBoundaryData hR hF _ _ (F.prism_path_lipschitz hR hi (C i) (hC i))
    (F.prism_transverse_lipschitz hR C hC)

variable {D J : ℝ≥0} (H : ControlledContraction (cellLeftPoint m K i R) D J)

/-- The local controlled extension uses the actual finite lower-cell
boundary and the actual carrier contraction. No extension existence is assumed. -/
def controlledCellExtension : EndpointCellCarrierExtension F hR :=
  F.relativeCellExtension hR hF hi H
    (F.prism_path_lipschitz hR hi (C i) (hC i)) (F.prism_transverse_lipschitz hR C hC)

theorem controlledCellExtension_first_dist_le (z z' : CellClosedDomain R)
    (heq : ∀ j,j≠i → z.val j=z'.val j) :
    dist ((F.controlledCellExtension hR hF C hC hi H).map z)
      ((F.controlledCellExtension hR hF C hC hi H).map z')≤
      (3*max (C i*(R.transverseWidth i).toNNReal) D : ℝ≥0)/R.transverseWidth i*
        |z.val i-z'.val i| :=
  (F.controlledPrismData hR hF C hC hi).fill_first_dist_le H hi z z' heq

theorem controlledCellExtension_transverse_dist_le (j : Fin d) (hji : j≠i)
    (hj : R.lower j<R.upper j) (z z' : CellClosedDomain R)
    (heq : ∀ k,k≠j → z.val k=z'.val k) :
    dist ((F.controlledCellExtension hR hF C hC hi H).map z)
      ((F.controlledCellExtension hR hF C hC hi H).map z')≤
      2*(ControlledContraction.coneTransverseConstant (C i*(R.transverseWidth i).toNNReal)
        D J (prismTransverseBound R i C) : ℝ)/R.transverseWidth j*|z.val j-z'.val j| :=
  (F.controlledPrismData hR hF C hC hi).fill_transverse_dist_le H hi j hji hj z z' heq

end LowerCellCarrierMaps
end
end AbelianTargets
