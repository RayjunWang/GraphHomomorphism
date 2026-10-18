import AbelianTargets.FiniteAtlasDependencyPatterns

/-! Equality of the finite dependency pattern determines the point cell
and every cell contained in a parent through the evaluation point. -/

namespace AbelianTargets.IntegerRectangularTiling
noncomputable section
variable {d : ℕ} {K : Fin d→ℕ}

theorem dependencyPattern_eq_contained_cells (T U : IntegerRectangularTiling d K)
    (z : RealCoordinates d) (hpat : T.dependencyPattern z=U.dependencyPattern z)
    (P : RectangularCell d) (hP : P∈T.cells) (hz : z∈P.closedBox)
    (Q : RectangularCell d) (hQP : Q.closedBox⊆P.closedBox) :
    Q∈T.cells ↔ Q∈U.cells := by
  classical
  have hQ := RectangularCell.subcell_mem_dependencyUniverse K z P Q
    (T.cells_bounded hP) hz hQP
  have hh := congrArg (fun s : Finset (RectangularCell d)=>Q∈s) hpat
  exact Iff.of_eq (by simpa only [dependencyPattern,Finset.mem_filter,hQ,true_and] using hh)

theorem pointCell_eq_of_dependencyPattern_eq (T U : IntegerRectangularTiling d K)
    (z : RealCoordinates d) (hpat : T.dependencyPattern z=U.dependencyPattern z) :
    T.pointCell z=U.pointCell z := by
  let P := T.pointCell z
  have hP : P∈T.cells := ⟨z,rfl⟩
  have hz := T.mem_relativeInterior_pointCell z
  have hP' : P∈U.cells := (T.dependencyPattern_eq_contained_cells U z hpat
    P hP (P.relativeInterior_subset hz) P Set.Subset.rfl).mp hP
  exact ((U.cell_iff_pointCell_at_interior P z hz).mp hP').symm

end
end AbelianTargets.IntegerRectangularTiling
