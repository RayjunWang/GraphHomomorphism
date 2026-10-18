import AbelianTargets.ActualMarkerAtlas
import Mathlib.Topology.LocallyConstant.Basic

/-! Finite local cut inputs determine actual retained tiles. In particular
the retained status of every fixed parent/cell is locally constant. -/

namespace AbelianTargets
noncomputable section
open Filter Topology
variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
variable {M : AnisotropicClopenMarkers d L X} {S : ℕ}

theorem ContinuousMarkerBoxes.Retained_iff_neighborhood (B : ContinuousMarkerBoxes M S)
    (x : X) (a : Lattice d) (R : RectangularCell d) :
    B.Retained x a R ↔ a +ᵥ x ∈ M.markers ∧ B.GridCell x a R ∧
      ∀ b ∈ inactiveOrbitNeighbors M 6 x a,
        (B.priority x b).val < (B.priority x a).val →
          Disjoint R.relativeInterior (B.markerBox x b).closedBox := by
  constructor
  · rintro ⟨ha,hgrid,hkeep⟩
    refine ⟨ha,hgrid,?_⟩
    intro b hb hp
    exact hkeep b ((mem_inactiveOrbitNeighbors_of_mem M 6 x a b ha).mp hb).1 hp
  · rintro ⟨ha,hgrid,hkeep⟩
    refine ⟨ha,hgrid,?_⟩
    intro b hb hp
    apply Set.disjoint_left.mpr
    intro z hzR hzb
    have hza := hgrid.subset_parent (R.relativeInterior_subset hzR)
    have hbn := B.parents_near_of_overlap x ha hb ⟨z,hza,hzb⟩
    exact Set.disjoint_left.mp (hkeep b hbn hp) hzR hzb

theorem ContinuousMarkerBoxes.Retained_eq_of_local_inputs
    (B : ContinuousMarkerBoxes M S) (x y : X) (a : Lattice d) (R : RectangularCell d)
    (hm : a +ᵥ x ∈ M.markers ↔ a +ᵥ y ∈ M.markers)
    (hN : inactiveOrbitNeighbors M 6 x a = inactiveOrbitNeighbors M 6 y a)
    (hp : ∀ b ∈ insert a (inactiveOrbitNeighbors M 6 x a),B.priority x b = B.priority y b)
    (hc : ∀ b ∈ insert a (inactiveOrbitNeighbors M 6 x a),∀ i,B.cuts x b i = B.cuts y b i) :
    B.Retained x a R ↔ B.Retained y a R := by
  have hca : ∀ i,B.cuts x a i = B.cuts y a i := fun i => hc a (by simp) i
  have hlevels : ∀ i,B.localCutLevels x a i = B.localCutLevels y a i := by
    intro i
    unfold localCutLevels
    rw [← hN]
    apply Finset.biUnion_congr rfl
    intro b hb
    rw [hc b (Finset.mem_insert_of_mem hb) i]
  have hgrid : B.GridCell x a R ↔ B.GridCell y a R := by
    unfold GridCell
    simp only [hlevels,hca]
  have hboxes : ∀ b ∈ inactiveOrbitNeighbors M 6 x a,B.markerBox x b = B.markerBox y b := by
    intro b hb
    apply RectangularCell.endpoint_pair_injective
    apply Prod.ext <;> funext i <;> dsimp [markerBox] <;>
      rw [hc b (Finset.mem_insert_of_mem hb) i]
  rw [B.Retained_iff_neighborhood,B.Retained_iff_neighborhood,← hm,← hgrid,← hN]
  apply and_congr_right
  intro ha
  apply and_congr_right
  intro hR
  apply forall_congr'
  intro b
  apply forall_congr'
  intro hb
  rw [← hp a (by simp),← hp b (Finset.mem_insert_of_mem hb),← hboxes b hb]

theorem ContinuousMarkerBoxes.retained_eventually_eq
    (B : ContinuousMarkerBoxes M S) (a : Lattice d) (R : RectangularCell d) (x : X) :
    ∀ᶠ y in 𝓝 x,B.Retained y a R ↔ B.Retained x a R := by
  letI : TopologicalSpace (Finset (Lattice d)) := ⊥
  letI : DiscreteTopology (Finset (Lattice d)) := ⟨rfl⟩
  have hn := (IsLocallyConstant.iff_continuous _).mpr
    (continuous_inactiveOrbitNeighbors M 6 a)
  have hm := (IsLocallyConstant.iff_continuous _).mpr
    ((continuous_markerFlag M.markers M.clopen).comp (continuous_const_vadd a))
  have hp : ∀ᶠ y in 𝓝 x,∀ b ∈ insert a (inactiveOrbitNeighbors M 6 x a),
      B.priority y b = B.priority x b := by
    apply (Filter.eventually_all_finset _).mpr
    intro b hb
    exact ((IsLocallyConstant.iff_continuous _).mpr (B.priority_continuous b)).eventually_eq x
  have hc : ∀ᶠ y in 𝓝 x,∀ b ∈ insert a (inactiveOrbitNeighbors M 6 x a),
      ∀ i,B.cuts y b i = B.cuts x b i := by
    apply (Filter.eventually_all_finset _).mpr
    intro b hb
    apply Filter.eventually_all.mpr
    intro i
    exact ((IsLocallyConstant.iff_continuous _).mpr (B.cuts_continuous b i)).eventually_eq x
  filter_upwards [hn.eventually_eq x,hm.eventually_eq x,hp,hc] with y hN hm hp hc
  have hmark : a +ᵥ x ∈ M.markers ↔ a +ᵥ y ∈ M.markers := by
    by_cases hx : a +ᵥ x ∈ M.markers <;> by_cases hy : a +ᵥ y ∈ M.markers <;>
      simp [markerFlag,hx,hy] at hm ⊢
  exact (B.Retained_eq_of_local_inputs x y a R hmark hN.symm
    (fun b hb => (hp b hb).symm) (fun b hb i => (hc b hb i).symm)).symm

def rectangleParentCandidates (L : Fin d → ℕ) (R : RectangularCell d) : Finset (Lattice d) :=
  Fintype.piFinset (fun i => Finset.Icc (R.upper i-3*(L i : ℤ)) (R.lower i+3*(L i : ℤ)))

theorem ContinuousMarkerBoxes.retained_parent_mem (B : ContinuousMarkerBoxes M S)
    {x : X} {a : Lattice d} {R : RectangularCell d} (hR : B.Retained x a R) :
    a ∈ rectangleParentCandidates L R := by
  simp only [rectangleParentCandidates,Fintype.mem_piFinset,Finset.mem_Icc]
  intro i
  have hr := (hR.2.1 i).2
  have hb := B.cuts_bounds x a i
  omega

theorem ContinuousMarkerBoxes.retainedTiles_eventually_eq
    (B : ContinuousMarkerBoxes M S) (R : RectangularCell d) (x : X) :
    ∀ᶠ y in 𝓝 x,R ∈ B.retainedTiles y ↔ R ∈ B.retainedTiles x := by
  have h : ∀ᶠ y in 𝓝 x,∀ a ∈ rectangleParentCandidates L R,
      B.Retained y a R ↔ B.Retained x a R := by
    apply (Filter.eventually_all_finset _).mpr
    intro a ha
    exact B.retained_eventually_eq a R x
  filter_upwards [h] with y hy
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,(hy a (B.retained_parent_mem ha)).mp ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨a,(hy a (B.retained_parent_mem ha)).mpr ha⟩

end
end AbelianTargets
