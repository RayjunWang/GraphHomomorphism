import AbelianTargets.Actions
import AbelianTargets.Probability
import Mathlib.Topology.Separation.Basic

/-!
# Continuous finite-range rounding

The final step of Theorem 1.4 and Proposition 7.1 is proved here.
The existence of `ProbabilityField` is a separate, unproved geometric
obligation, never an axiom of this project.
-/

namespace AbelianTargets

/-- Any selection from the finite image of a continuous map into a T1 space
is continuous. This justifies a fixed maximum-mass selection even at ties. -/
theorem continuous_comp_of_finite_range
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y]
    [TopologicalSpace Z] {f : X → Y} (hf : Continuous f)
    (hfinite : (Set.range f).Finite) (g : Y → Z) :
    Continuous (fun x => g (f x)) := by
  letI : Finite (Set.range f) := hfinite.to_subtype
  haveI : DiscreteTopology (Set.range f) := inferInstance
  exact (continuous_of_discreteTopology (f := fun y : Set.range f => g y.val)).comp
    hf.rangeFactorization

/-- A finite-range probability field with the precise support and error
conditions constructed in Section 6 of the paper. Only the first shore
needs to be continuous for the rounding theorem. -/
structure ProbabilityField {d : ℕ} {X V : Type*}
    [AddAction (Lattice d) X] [TopologicalSpace X] [Fintype V]
    (H : SimpleGraph V) where
  p : X → Probability V
  q : X → Probability V
  continuous_p : Continuous p
  finite_range_p : (Set.range p).Finite
  compatible : ∀ x, Compatible H (p x) (q x)
  close : ∀ (x : X) (i : Fin d) (v : V),
    |(p (unitVector i +ᵥ x)).mass v - (q x).mass v| <
      1 / (2 * (Fintype.card V : ℝ))

/-- Complete, unconditional verification of the rounding implication.
This proves existence of the homomorphism from the stated probability field;
it does not prove existence of that field from an odd torsion walk. -/
theorem hasContinuousHom_of_probabilityField
    {d : ℕ} {X V : Type*} [AddAction (Lattice d) X]
    [TopologicalSpace X] [TopologicalSpace V] [Fintype V]
    {H : SimpleGraph V} (field : ProbabilityField (d := d) (X := X) H) :
    HasContinuousHom (d := d) (X := X) H := by
  by_cases hX : Nonempty X
  · letI : Nonempty X := hX
    letI : Nonempty V := (field.p (Classical.choice hX)).nonempty
    let c : X → V := fun x => Probability.chooseMax (field.p x)
    have hc : Continuous c := continuous_comp_of_finite_range
      field.continuous_p field.finite_range_p Probability.chooseMax
    apply hasContinuousHom_of_positive c hc
    intro x i
    exact rounding_edge H (field.p x) (field.q x)
      (field.p (unitVector i +ᵥ x)) (field.compatible x) (field.close x i)
  · letI : IsEmpty X := not_nonempty_iff.mp hX
    refine ⟨isEmptyElim, continuous_iff_continuousAt.mpr (fun x => isEmptyElim x), ?_⟩
    intro x
    exact isEmptyElim x

end AbelianTargets
