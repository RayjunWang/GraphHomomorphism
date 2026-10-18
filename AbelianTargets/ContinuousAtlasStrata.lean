import AbelianTargets.MarkerAtlasLocality

/-! The actual incident tile lists and point cells are locally constant in
the action point. The proof uses the finite universe of bounded integer
rectangles near the fixed spatial point, rather than assuming atlas locality. -/

namespace AbelianTargets
noncomputable section
open Filter Topology

namespace IntegerRectangularTiling
variable {d : ℕ} {K : Fin d → ℕ}

theorem pointCell_eq_of_incidentFinset_eq (T U : IntegerRectangularTiling d K)
    (z : RealCoordinates d) (he : T.incidentFinset z = U.incidentFinset z) :
    T.pointCell z = U.pointCell z := by
  apply RectangularCell.closedBox_injective
  ext w
  rw [T.mem_pointCell,U.mem_pointCell]
  constructor
  · intro h R hR hzR
    have hr : R ∈ T.incidentFinset z := by
      rw [he]
      exact (U.mem_incidentFinset z R).mpr ⟨hR,hzR⟩
    exact h R ((T.mem_incidentFinset z R).mp hr).1 hzR
  · intro h R hR hzR
    have hr : R ∈ U.incidentFinset z := by
      rw [← he]
      exact (T.mem_incidentFinset z R).mpr ⟨hR,hzR⟩
    exact h R ((U.mem_incidentFinset z R).mp hr).1 hzR

theorem cell_iff_pointCell_at_interior (T : IntegerRectangularTiling d K)
    (R : RectangularCell d) (z : RealCoordinates d) (hz : z ∈ R.relativeInterior) :
    R ∈ T.cells ↔ T.pointCell z = R := by
  constructor
  · rintro ⟨x,rfl⟩
    exact T.pointCell_constant x z hz
  · intro he
    exact ⟨z,he⟩

variable {Y : Type*} [TopologicalSpace Y]

theorem incidentFinset_eventually_eq (T : Y → IntegerRectangularTiling d K)
    (hlocal : ∀ R x,∀ᶠ y in 𝓝 x,R ∈ (T y).tiles ↔ R ∈ (T x).tiles)
    (x : Y) (z : RealCoordinates d) :
    ∀ᶠ y in 𝓝 x,(T y).incidentFinset z = (T x).incidentFinset z := by
  let F := (RectangularCell.finite_meeting_ball K z).toFinset
  have h : ∀ᶠ y in 𝓝 x,∀ R ∈ F,R ∈ (T y).tiles ↔ R ∈ (T x).tiles := by
    apply (Filter.eventually_all_finset _).mpr
    intro R hR
    exact hlocal R x
  filter_upwards [h] with y hy
  ext R
  rw [(T y).mem_incidentFinset,(T x).mem_incidentFinset]
  constructor
  · rintro ⟨hR,hzR⟩
    have hf : R ∈ F := (Set.Finite.mem_toFinset _).mpr
      ⟨(T y).bounded R hR,z,hzR,Metric.mem_ball_self (by norm_num)⟩
    exact ⟨(hy R hf).mp hR,hzR⟩
  · rintro ⟨hR,hzR⟩
    have hf : R ∈ F := (Set.Finite.mem_toFinset _).mpr
      ⟨(T x).bounded R hR,z,hzR,Metric.mem_ball_self (by norm_num)⟩
    exact ⟨(hy R hf).mpr hR,hzR⟩

theorem pointCell_isLocallyConstant (T : Y → IntegerRectangularTiling d K)
    (hlocal : ∀ R x,∀ᶠ y in 𝓝 x,R ∈ (T y).tiles ↔ R ∈ (T x).tiles)
    (z : RealCoordinates d) : IsLocallyConstant (fun x => (T x).pointCell z) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  filter_upwards [incidentFinset_eventually_eq T hlocal x z] with y hy
  exact (T y).pointCell_eq_of_incidentFinset_eq (T x) z hy

theorem cells_eventually_eq (T : Y → IntegerRectangularTiling d K)
    (hlocal : ∀ R x,∀ᶠ y in 𝓝 x,R ∈ (T y).tiles ↔ R ∈ (T x).tiles)
    (R : RectangularCell d) (x : Y) :
    ∀ᶠ y in 𝓝 x,R ∈ (T y).cells ↔ R ∈ (T x).cells := by
  obtain ⟨z,hz⟩ := R.relativeInterior_nonempty
  filter_upwards [(pointCell_isLocallyConstant T hlocal z).eventually_eq x] with y hy
  rw [(T y).cell_iff_pointCell_at_interior R z hz,
    (T x).cell_iff_pointCell_at_interior R z hz,hy]

theorem finite_cells_eventually_eq (T : Y → IntegerRectangularTiling d K)
    (hlocal : ∀ R x,∀ᶠ y in 𝓝 x,R ∈ (T y).tiles ↔ R ∈ (T x).tiles)
    (F : Finset (RectangularCell d)) (x : Y) :
    ∀ᶠ y in 𝓝 x,∀ R ∈ F,R ∈ (T y).cells ↔ R ∈ (T x).cells :=
  (Filter.eventually_all_finset _).mpr (fun R _ => cells_eventually_eq T hlocal R x)

end IntegerRectangularTiling

variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
variable {M : AnisotropicClopenMarkers d L X} {S : ℕ}

theorem ContinuousMarkerBoxes.pointCell_isLocallyConstant
    (B : ContinuousMarkerBoxes M S) (hL : ∀ i,1 ≤ L i) (hS : 6 ≤ S)
    (z : RealCoordinates d) : IsLocallyConstant (fun x => (B.tiling hL hS x).pointCell z) :=
  IntegerRectangularTiling.pointCell_isLocallyConstant (B.tiling hL hS)
    B.retainedTiles_eventually_eq z

theorem ContinuousMarkerBoxes.atlasCells_eventually_eq
    (B : ContinuousMarkerBoxes M S) (hL : ∀ i,1 ≤ L i) (hS : 6 ≤ S)
    (R : RectangularCell d) (x : X) :
    ∀ᶠ y in 𝓝 x,R ∈ B.atlasCells hL hS y ↔ R ∈ B.atlasCells hL hS x :=
  IntegerRectangularTiling.cells_eventually_eq (B.tiling hL hS)
    B.retainedTiles_eventually_eq R x

end
end AbelianTargets
