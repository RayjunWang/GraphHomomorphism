import AbelianTargets.RetainedMarkerTiles
import AbelianTargets.RectangularAtlasBoundary

/-! The actual bounded rectangular tiling, and its regular point-cell atlas,
constructed from continuous covariant marker cuts. -/

namespace AbelianTargets
noncomputable section

variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
variable {M : AnisotropicClopenMarkers d L X} {S : ℕ}

theorem ContinuousMarkerBoxes.GridCell.bounded
    {B : ContinuousMarkerBoxes M S} {x : X} {a : Lattice d} {R : RectangularCell d}
    (hR : B.GridCell x a R) : R.HasBoundedSides (fun i => 6*L i) := by
  intro i
  have hb := B.cuts_bounds x a i
  have hr := (hR i).2
  change R.upper i-R.lower i ≤ ((6*L i : ℕ) : ℤ)
  push_cast
  omega

def ContinuousMarkerBoxes.tiling (B : ContinuousMarkerBoxes M S)
    (hL : ∀ i,1 ≤ L i) (hS : 6 ≤ S) (x : X) :
    IntegerRectangularTiling d (fun i => 6*L i) where
  tiles := B.retainedTiles x
  positive R hR i := by
    obtain ⟨a,ha,hR,hkeep⟩ := hR
    exact hR.positive i
  cover := B.retainedTiles_cover hL x
  interior_unique R hR Q hQ hz := by
    obtain ⟨a,hR⟩ := hR
    obtain ⟨b,hQ⟩ := hQ
    exact B.retained_interiors_unique hS x hR hQ hz
  bounded R hR := by
    obtain ⟨a,ha,hR,hkeep⟩ := hR
    exact hR.bounded

/-- The literal atlas at an action point: finite intersections of the minimal
faces of all incident retained marker rectangles. -/
def ContinuousMarkerBoxes.atlasCells (B : ContinuousMarkerBoxes M S)
    (hL : ∀ i,1 ≤ L i) (hS : 6 ≤ S) (x : X) : Set (RectangularCell d) :=
  (B.tiling hL hS x).cells

theorem ContinuousMarkerBoxes.atlas_relativeInterior_cover
    (B : ContinuousMarkerBoxes M S) (hL : ∀ i,1 ≤ L i) (hS : 6 ≤ S) (x : X)
    (z : RealCoordinates d) : ∃ R ∈ B.atlasCells hL hS x,z ∈ R.relativeInterior :=
  (B.tiling hL hS x).relativeInterior_cover z

theorem ContinuousMarkerBoxes.atlas_relativeInterior_unique
    (B : ContinuousMarkerBoxes M S) (hL : ∀ i,1 ≤ L i) (hS : 6 ≤ S) (x : X)
    {R Q : RectangularCell d} (hR : R ∈ B.atlasCells hL hS x)
    (hQ : Q ∈ B.atlasCells hL hS x)
    (hz : (R.relativeInterior ∩ Q.relativeInterior).Nonempty) : R = Q :=
  (B.tiling hL hS x).relativeInterior_unique hR hQ hz

theorem ContinuousMarkerBoxes.atlas_locallyFinite
    (B : ContinuousMarkerBoxes M S) (hL : ∀ i,1 ≤ L i) (hS : 6 ≤ S) (x : X) :
    LocallyFinite (fun R : B.atlasCells hL hS x => R.val.closedBox) :=
  (B.tiling hL hS x).cells_locallyFinite

theorem ContinuousMarkerBoxes.atlas_boundary_eq_finite_union
    (B : ContinuousMarkerBoxes M S) (hL : ∀ i,1 ≤ L i) (hS : 6 ≤ S) (x : X)
    {R : RectangularCell d} (hR : R ∈ B.atlasCells hL hS x) :
    R.boundary = ⋃ Q ∈ (B.tiling hL hS x).boundaryCells R,Q.closedBox :=
  (B.tiling hL hS x).boundary_eq_finite_union hR

end
end AbelianTargets
