import AbelianTargets.RetainedTilesCovariance

namespace AbelianTargets
noncomputable section

theorem IntegerRectangularTiling.pointCell_eq_of_tiles_eq
    {d : ℕ} {K : Fin d → ℕ} (T U : IntegerRectangularTiling d K)
    (he : T.tiles = U.tiles) (z : RealCoordinates d) : T.pointCell z = U.pointCell z := by
  apply RectangularCell.closedBox_injective
  ext w
  rw [T.mem_pointCell,U.mem_pointCell]
  rw [he]

variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
variable {M : AnisotropicClopenMarkers d L X} {S : ℕ}

theorem ContinuousMarkerBoxes.pointCell_repoint
    (B : ContinuousMarkerBoxes M S) (hL : ∀ i,1 ≤ L i) (hS : 6 ≤ S)
    (x : X) (t : Lattice d) (z : RealCoordinates d) :
    ((B.tiling hL hS (t +ᵥ x)).pointCell z).translate t =
      (B.tiling hL hS x).pointCell (translateCoordinates t z) := by
  rw [← (B.tiling hL hS (t +ᵥ x)).pointCell_translate t z]
  apply IntegerRectangularTiling.pointCell_eq_of_tiles_eq
  exact B.retainedTiles_repoint x t

theorem ContinuousMarkerBoxes.atlasCells_repoint
    (B : ContinuousMarkerBoxes M S) (hL : ∀ i,1 ≤ L i) (hS : 6 ≤ S)
    (x : X) (t : Lattice d) :
    (fun R : RectangularCell d => R.translate t) '' B.atlasCells hL hS (t +ᵥ x) =
      B.atlasCells hL hS x := by
  ext R
  constructor
  · rintro ⟨Q,⟨z,rfl⟩,rfl⟩
    exact ⟨translateCoordinates t z,(B.pointCell_repoint hL hS x t z).symm⟩
  · rintro ⟨z,rfl⟩
    refine ⟨(B.tiling hL hS (t +ᵥ x)).pointCell (translateCoordinates (-t) z),
      ⟨translateCoordinates (-t) z,rfl⟩,?_⟩
    simpa only [translateCoordinates_cancel_neg] using
      B.pointCell_repoint hL hS x t (translateCoordinates (-t) z)

end
end AbelianTargets
