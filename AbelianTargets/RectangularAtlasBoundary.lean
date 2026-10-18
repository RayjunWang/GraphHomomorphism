import AbelianTargets.RectangularBoundaryStrata

/-! Finite, strictly lower-rank boundary refinements of the actual point cells. -/

namespace AbelianTargets
noncomputable section

namespace RectangularCell
variable {d : ℕ}

theorem rank_lt_of_relativeInterior_on_boundary (R Q : RectangularCell d)
    (hsub : R.closedBox ⊆ Q.closedBox) {z : RealCoordinates d}
    (hzR : z ∈ R.relativeInterior) (hzQ : z ∈ Q.boundary) : R.rank < Q.rank := by
  obtain ⟨i,hi,hend⟩ := Q.boundary_has_endpoint hzQ
  apply R.rank_lt_of_subset_and_collapsed Q hsub
  refine ⟨i,hi,?_⟩
  by_contra hne
  have hz := hzR i
  simp only [relativeInterior,hne,if_false] at hz
  have hb := (closedBox_subset_iff R Q).mp hsub i
  have hlo : (Q.lower i : ℝ) ≤ (R.lower i : ℝ) := by exact_mod_cast hb.1
  have hhi : (R.upper i : ℝ) ≤ (Q.upper i : ℝ) := by exact_mod_cast hb.2
  rcases hend with he | he
  · rw [he] at hz
    exact (not_lt_of_ge hlo) hz.1
  · rw [he] at hz
    exact (not_lt_of_ge hhi) hz.2

end RectangularCell

namespace IntegerRectangularTiling
variable {d : ℕ} {K : Fin d → ℕ} (T : IntegerRectangularTiling d K)

theorem pointCell_rank_lt_on_boundary (x z : RealCoordinates d)
    (hz : z ∈ (T.pointCell x).boundary) : (T.pointCell z).rank < (T.pointCell x).rank :=
  RectangularCell.rank_lt_of_relativeInterior_on_boundary _ _
    (T.pointCell_closed_mono x z hz.1) (T.mem_relativeInterior_pointCell z) hz

theorem contained_cell_closed_subset_boundary {R Q : RectangularCell d}
    (hR : R ∈ T.cells) (hQ : Q ∈ T.cells) (hsub : Q.closedBox ⊆ R.closedBox)
    (hrank : Q.rank < R.rank) : Q.closedBox ⊆ R.boundary := by
  obtain ⟨x,rfl⟩ := hR
  obtain ⟨y,rfl⟩ := hQ
  intro z hz
  refine ⟨hsub hz,?_⟩
  intro hzR
  have he := T.pointCell_constant x z hzR
  have hback := T.pointCell_closed_mono y z hz
  rw [he] at hback
  have heq : T.pointCell y = T.pointCell x :=
    RectangularCell.closedBox_injective (Set.Subset.antisymm hsub hback)
  rw [heq] at hrank
  exact (lt_irrefl _) hrank

def boundaryCells (R : RectangularCell d) : Finset (RectangularCell d) :=
  ((T.finite_cells_contained R).subset (by
    intro Q hQ
    exact ⟨hQ.1,hQ.2.1⟩) :
      {Q : RectangularCell d | Q ∈ T.cells ∧ Q.closedBox ⊆ R.closedBox ∧ Q.rank < R.rank}.Finite).toFinset

@[simp] theorem mem_boundaryCells (R Q : RectangularCell d) :
    Q ∈ T.boundaryCells R ↔ Q ∈ T.cells ∧ Q.closedBox ⊆ R.closedBox ∧ Q.rank < R.rank :=
  Set.Finite.mem_toFinset _

theorem boundary_eq_finite_union {R : RectangularCell d} (hR : R ∈ T.cells) :
    R.boundary = ⋃ Q ∈ T.boundaryCells R,Q.closedBox := by
  obtain ⟨x,rfl⟩ := hR
  ext z
  constructor
  · intro hz
    apply Set.mem_iUnion.mpr
    refine ⟨T.pointCell z,Set.mem_iUnion.mpr ⟨?_,?_⟩⟩
    · exact (T.mem_boundaryCells _ _).mpr
        ⟨⟨z,rfl⟩,T.pointCell_closed_mono x z hz.1,T.pointCell_rank_lt_on_boundary x z hz⟩
    · exact (T.pointCell z).relativeInterior_subset (T.mem_relativeInterior_pointCell z)
  · intro hz
    obtain ⟨Q,hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hQ,hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hQc,hsub,hrank⟩ := (T.mem_boundaryCells _ _).mp hQ
    exact T.contained_cell_closed_subset_boundary ⟨x,rfl⟩ hQc hsub hrank hz

end IntegerRectangularTiling
end
end AbelianTargets
