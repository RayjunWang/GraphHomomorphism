import AbelianTargets.RectangularFaceRefinement

/-!
# Actual boundary strata of a bounded integer rectangular tiling

The cell at a point is the finite intersection of the minimal faces of
all incident full tiles. Integer probes prove that its relative interior
has exactly the same tile incidences. Thus the distinct point cells give
a relative-interior partition, with only tile boundaries refined.
-/

namespace AbelianTargets
noncomputable section

structure IntegerRectangularTiling (d : ℕ) (K : Fin d → ℕ) where
  tiles : Set (RectangularCell d)
  positive : ∀ R ∈ tiles,∀ i,R.lower i < R.upper i
  cover : ∀ z : RealCoordinates d,∃ R ∈ tiles,z ∈ R.closedBox
  interior_unique : ∀ R ∈ tiles,∀ Q ∈ tiles,
    (R.relativeInterior ∩ Q.relativeInterior).Nonempty → R = Q
  bounded : ∀ R ∈ tiles,R.HasBoundedSides K

namespace IntegerRectangularTiling
variable {d : ℕ} {K : Fin d → ℕ} (T : IntegerRectangularTiling d K)

theorem finite_incident (x : RealCoordinates d) :
    {R : RectangularCell d | R ∈ T.tiles ∧ x ∈ R.closedBox}.Finite := by
  apply (RectangularCell.finite_meeting_ball K x).subset
  intro R hR
  exact ⟨T.bounded R hR.1,x,hR.2,Metric.mem_ball_self (by norm_num)⟩

def incidentFinset (x : RealCoordinates d) : Finset (RectangularCell d) :=
  (T.finite_incident x).toFinset

@[simp] theorem mem_incidentFinset (x : RealCoordinates d) (R : RectangularCell d) :
    R ∈ T.incidentFinset x ↔ R ∈ T.tiles ∧ x ∈ R.closedBox := Set.Finite.mem_toFinset _

theorem incidentFinset_nonempty (x : RealCoordinates d) : (T.incidentFinset x).Nonempty := by
  obtain ⟨R,hR,hx⟩ := T.cover x
  exact ⟨R,(T.mem_incidentFinset x R).mpr ⟨hR,hx⟩⟩

def pointCell (x : RealCoordinates d) : RectangularCell d :=
  RectangularCell.faceIntersection (T.incidentFinset x) (T.incidentFinset_nonempty x) x
    (fun R hR => ((T.mem_incidentFinset x R).mp hR).2)

theorem mem_pointCell (x z : RealCoordinates d) :
    z ∈ (T.pointCell x).closedBox ↔
      ∀ R ∈ T.tiles,x ∈ R.closedBox → z ∈ (R.faceAt x).closedBox := by
  rw [pointCell,RectangularCell.mem_faceIntersection]
  constructor
  · intro h R hR hx
    exact h R ((T.mem_incidentFinset x R).mpr ⟨hR,hx⟩)
  · intro h R hR
    obtain ⟨hR,hx⟩ := (T.mem_incidentFinset x R).mp hR
    exact h R hR hx

theorem mem_relativeInterior_pointCell (x : RealCoordinates d) :
    x ∈ (T.pointCell x).relativeInterior :=
  RectangularCell.mem_relativeInterior_faceIntersection _ _ _ _

theorem pointCell_relativeInterior_subset_face (x : RealCoordinates d)
    {R : RectangularCell d} (hR : R ∈ T.tiles) (hx : x ∈ R.closedBox) :
    (T.pointCell x).relativeInterior ⊆ (R.faceAt x).relativeInterior :=
  RectangularCell.faceIntersection_relativeInterior_subset _ _ _ _
    ((T.mem_incidentFinset x R).mpr ⟨hR,hx⟩)

theorem pointCell_subset_tile (x : RealCoordinates d)
    {R : RectangularCell d} (hR : R ∈ T.tiles) (hx : x ∈ R.closedBox) :
    (T.pointCell x).closedBox ⊆ R.closedBox := by
  intro z hz
  exact R.faceAt_subset x ((T.mem_pointCell x z).mp hz R hR hx)

theorem pointCell_incident_faces (x y : RealCoordinates d)
    (hy : y ∈ (T.pointCell x).relativeInterior) :
    ∀ R ∈ T.tiles,x ∈ R.closedBox → y ∈ R.closedBox ∧ R.faceAt x = R.faceAt y := by
  intro R hR hx
  have hyface := T.pointCell_relativeInterior_subset_face x hR hx hy
  exact ⟨R.faceAt_subset x ((R.faceAt x).relativeInterior_subset hyface),
    (R.faceAt_eq_of_relativeInterior (T.positive R hR) x y hyface).symm⟩

theorem pointCell_incident_constant (x y : RealCoordinates d)
    (hy : y ∈ (T.pointCell x).relativeInterior) :
    ∀ R ∈ T.tiles,y ∈ R.closedBox ↔ x ∈ R.closedBox :=
  incident_tiles_constant_of_faces T.tiles T.positive T.cover T.interior_unique x y
    (T.pointCell_incident_faces x y hy)

theorem pointCell_constant (x y : RealCoordinates d)
    (hy : y ∈ (T.pointCell x).relativeInterior) : T.pointCell y = T.pointCell x := by
  apply RectangularCell.closedBox_injective
  ext z
  rw [T.mem_pointCell y z,T.mem_pointCell x z]
  constructor
  · intro h R hR hx
    have hyR := (T.pointCell_incident_constant x y hy R hR).mpr hx
    have he := (T.pointCell_incident_faces x y hy R hR hx).2
    simpa only [he] using h R hR hyR
  · intro h R hR hyR
    have hx := (T.pointCell_incident_constant x y hy R hR).mp hyR
    have he := (T.pointCell_incident_faces x y hy R hR hx).2
    simpa only [he] using h R hR hx

theorem pointCell_closed_mono (x z : RealCoordinates d)
    (hz : z ∈ (T.pointCell x).closedBox) :
    (T.pointCell z).closedBox ⊆ (T.pointCell x).closedBox := by
  intro w hw
  apply (T.mem_pointCell x w).mpr
  intro R hR hx
  have hzface := (T.mem_pointCell x z).mp hz R hR hx
  have hzR := R.faceAt_subset x hzface
  exact R.faceAt_mono (T.positive R hR) x z hzface ((T.mem_pointCell z w).mp hw R hR hzR)

def cells : Set (RectangularCell d) := Set.range T.pointCell

theorem relativeInterior_cover (z : RealCoordinates d) :
    ∃ R ∈ T.cells,z ∈ R.relativeInterior :=
  ⟨T.pointCell z,⟨z,rfl⟩,T.mem_relativeInterior_pointCell z⟩

theorem relativeInterior_unique {R Q : RectangularCell d}
    (hR : R ∈ T.cells) (hQ : Q ∈ T.cells)
    (hz : (R.relativeInterior ∩ Q.relativeInterior).Nonempty) : R = Q := by
  obtain ⟨x,rfl⟩ := hR
  obtain ⟨y,rfl⟩ := hQ
  obtain ⟨z,hzx,hzy⟩ := hz
  exact (T.pointCell_constant x z hzx).symm.trans (T.pointCell_constant y z hzy)

theorem cells_bounded {R : RectangularCell d} (hR : R ∈ T.cells) : R.HasBoundedSides K := by
  obtain ⟨x,rfl⟩ := hR
  obtain ⟨Q,hQ,hxQ⟩ := T.cover x
  have hsub := (RectangularCell.closedBox_subset_iff _ _).mp (T.pointCell_subset_tile x hQ hxQ)
  intro i
  have hQbound := T.bounded Q hQ i
  have hi := hsub i
  omega

theorem cells_locallyFinite :
    LocallyFinite (fun R : T.cells => R.val.closedBox) :=
  RectangularCell.locallyFinite_of_boundedSides Subtype.val Subtype.val_injective K
    (fun R => T.cells_bounded R.property)

theorem finite_cells_contained (R : RectangularCell d) :
    {Q : RectangularCell d | Q ∈ T.cells ∧ Q.closedBox ⊆ R.closedBox}.Finite := by
  apply (RectangularCell.finite_bounded_endpoints R.lower R.upper).subset
  intro Q hQ i
  have hi := (RectangularCell.closedBox_subset_iff Q R).mp hQ.2 i
  exact ⟨hi.1,(Q.ordered i).trans hi.2,hi.1.trans (Q.ordered i),hi.2⟩

end IntegerRectangularTiling
end
end AbelianTargets
