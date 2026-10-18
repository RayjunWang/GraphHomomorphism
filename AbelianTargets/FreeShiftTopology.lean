import AbelianTargets.MarkerExistence
import Mathlib.Topology.Maps.Basic

/-!
# The free shift is a zero-dimensional Polish action

The proof embeds a countable intersection of open subsets of a Polish
space as a closed diagonal in their product. It uses no reference axiom.
-/

namespace AbelianTargets

open Topology

instance shiftSpacePolishSpace (d : ℕ) : PolishSpace (ShiftSpace d) := by
  constructor

theorem polishSpace_countable_open_intersection
    {X I : Type*} [TopologicalSpace X] [PolishSpace X]
    [Countable I] [Nonempty I] (U : I → Set X) (hU : ∀ i, IsOpen (U i)) :
    PolishSpace {x : X // ∀ i, x ∈ U i} := by
  classical
  let i₀ : I := Classical.choice inferInstance
  let Y := (i : I) → U i
  letI (i : I) : PolishSpace (U i) := (hU i).polishSpace
  let f : {x : X // ∀ i, x ∈ U i} → Y := fun x i => ⟨x.val, x.property i⟩
  let g : Y → X := fun y => (y i₀).val
  have hf : Continuous f := by
    apply continuous_pi
    intro i
    exact continuous_subtype_val.subtype_mk _
  have hg : Continuous g := continuous_subtype_val.comp (continuous_apply i₀)
  have hfg : IsEmbedding f := by
    apply IsEmbedding.of_comp hf hg
    exact IsEmbedding.subtypeVal
  have hrange : Set.range f = {y : Y | ∀ i, (y i).val = (y i₀).val} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      intro i
      rfl
    · intro hy
      let x : {x : X // ∀ i, x ∈ U i} := ⟨(y i₀).val, by
        intro i
        rw [← hy i]
        exact (y i).property⟩
      refine ⟨x, ?_⟩
      funext i
      apply Subtype.ext
      exact (hy i).symm
  have hclosed : IsClosed (Set.range f) := by
    rw [hrange]
    have heq : {y : Y | ∀ i, (y i).val = (y i₀).val} =
        ⋂ i, {y : Y | (y i).val = (y i₀).val} := by ext y; simp
    rw [heq]
    exact isClosed_iInter (fun i => isClosed_eq
      (continuous_subtype_val.comp (continuous_apply i)) hg)
  exact (show IsClosedEmbedding f from ⟨hfg, hclosed⟩).polishSpace

theorem isOpen_freeShift_condition (d : ℕ) (g : Lattice d) :
    IsOpen {x : ShiftSpace d | shift g x = x → g = 0} := by
  by_cases hg : g = 0
  · simp [hg]
  · have hs : {x : ShiftSpace d | shift g x = x → g = 0} =
        {x : ShiftSpace d | shift g x ≠ x} := by
      ext x
      simp [hg]
    rw [hs]
    exact (isClosed_eq (continuous_shift g) continuous_id).isOpen_compl

/-- The free binary shift with its literal inherited topology is Polish. -/
instance freeShiftPolishSpace (d : ℕ) : PolishSpace (FreeShift d) := by
  exact polishSpace_countable_open_intersection
    (fun g : Lattice d => {x : ShiftSpace d | shift g x = x → g = 0})
    (isOpen_freeShift_condition d)

/-- Universal targets apply in particular to the actual free binary shift. -/
theorem inClass_of_universalTarget {d : ℕ} {V : Type*}
    [TopologicalSpace V] {H : SimpleGraph V}
    (h : UniversalTarget.{0} d H) : InClass d H :=
  h (FreeShift d) (freeShift_zeroDimensional d) (freeShift_isFree d)

end AbelianTargets
