import AbelianTargets.ContinuousAtlasStrata

/-! Actual finite atlas patterns on a fixed spatial neighborhood. -/

namespace AbelianTargets
noncomputable section
open Filter Topology
namespace IntegerRectangularTiling
variable {d : ℕ} {K : Fin d → ℕ}

def localPattern (T : IntegerRectangularTiling d K) (z : RealCoordinates d) :
    Finset (RectangularCell d) := by
  classical
  exact (RectangularCell.finite_meeting_ball K z).toFinset.filter (fun R => R ∈ T.cells)

@[simp] theorem mem_localPattern (T : IntegerRectangularTiling d K)
    (z : RealCoordinates d) (R : RectangularCell d) :
    R ∈ T.localPattern z ↔ R ∈ T.cells ∧ (R.closedBox ∩ Metric.ball z 1).Nonempty := by
  classical
  simp only [localPattern,Finset.mem_filter,Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨⟨hb,hi⟩,hR⟩
    exact ⟨hR,hi⟩
  · rintro ⟨hR,hi⟩
    exact ⟨⟨T.cells_bounded hR,hi⟩,hR⟩

theorem localPattern_isLocallyConstant {Y : Type*} [TopologicalSpace Y]
    (T : Y → IntegerRectangularTiling d K)
    (hlocal : ∀ R x,∀ᶠ y in 𝓝 x,R ∈ (T y).tiles ↔ R ∈ (T x).tiles)
    (z : RealCoordinates d) : IsLocallyConstant (fun x => (T x).localPattern z) := by
  classical
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  filter_upwards [finite_cells_eventually_eq T hlocal
    (RectangularCell.finite_meeting_ball K z).toFinset x] with y hy
  unfold localPattern
  apply Finset.filter_congr
  intro R hR
  exact hy R hR

end IntegerRectangularTiling

variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
variable {M : AnisotropicClopenMarkers d L X} {S : ℕ}

theorem ContinuousMarkerBoxes.localAtlasPattern_isLocallyConstant
    (B : ContinuousMarkerBoxes M S) (hL : ∀ i,1 ≤ L i) (hS : 6 ≤ S)
    (z : RealCoordinates d) : IsLocallyConstant (fun x => (B.tiling hL hS x).localPattern z) :=
  IntegerRectangularTiling.localPattern_isLocallyConstant (B.tiling hL hS)
    B.retainedTiles_eventually_eq z

end
end AbelianTargets
