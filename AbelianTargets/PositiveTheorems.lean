import AbelianTargets.SmallStepProjectedOrbitMaps
import AbelianTargets.Statements

/-!
# Theorem 1.4 and Proposition 7.1 in every positive dimension

The actual canonical atlas maps on the inverse-sheared action provide
finite-range approximate shore-swap maps. Each original generator becomes
one or two coordinate steps. The constructed torsion support data and the
checked probability rounding then give the requested graph homomorphism.
There is no additional geometric-construction hypothesis.
-/

namespace AbelianTargets

noncomputable section

universe u v

/-- The support-space approximate parity maps for every free continuous
zero-dimensional Polish lattice action, with the original generators. -/
theorem approximateParityMaps_supportPair
    {d : ℕ} {X : Type u} {V : Type v}
    [TopologicalSpace X] [PolishSpace X]
    [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
    [Fintype V] {H : SimpleGraph V} (D : SupportTorsionData H)
    (hd : 1 ≤ d) (zeroDim : ZeroDimensional X)
    (free : IsFree (G := Lattice d) (X := X)) :
    ApproximateParityMaps (d := d) X (SupportPair H) (SupportPair.swap H) := by
  classical
  apply approximateParityMaps_of_latticeOrbitConstruction hd (SupportPair.isometry_swap H)
  intro ε hε
  obtain ⟨F⟩ := exists_smallStepLatticeOrbitMap (X := ParitySheared hd X)
    D (firstAxis hd) (ParitySheared.zeroDimensional hd zeroDim)
      (ParitySheared.isFree hd free) hε
  refine ⟨fun x g => F.orbitMap (ParitySheared.ofOriginal hd x) g,
    F.continuous_origin.comp (ParitySheared.continuous_ofOriginal hd), ?_, ?_, ?_⟩
  · apply F.finite_range_origin.subset
    rintro y ⟨x, rfl⟩
    exact ⟨ParitySheared.ofOriginal hd x, rfl⟩
  · intro x i
    change F.orbitMap (ParitySheared.ofOriginal hd (unitVector i +ᵥ x)) 0 =
      SupportPair.swap H
        (F.orbitMap (ParitySheared.ofOriginal hd x) (shearCoordinates hd (unitVector i)))
    rw [ParitySheared.ofOriginal_vadd]
    have hc := F.covariance (ParitySheared.ofOriginal hd x)
      (shearCoordinates hd (unitVector i))
    rw [shearCoordinates_generator_first] at hc
    simpa [SupportPair.paritySwap] using hc
  · intro x i g
    exact F.unit_step (ParitySheared.ofOriginal hd x) i g

/-- Proposition 7.1: an odd reduced torsion class gives a continuous graph
homomorphism for every positive dimension and every action in the source. -/
theorem proposition7_1 {V : Type v} [TopologicalSpace V] [Fintype V]
    [DiscreteTopology V] (H : SimpleGraph V) :
    Proposition71Statement.{u} H := by
  intro ht d hd X _ _ _ _ zeroDim free
  obtain ⟨D⟩ := supportTorsionData_of_oddTorsion H ht
  letI : Nonempty V := D.base.left.nonempty
  exact SupportPair.hasContinuousHom_of_approximateSwap H
    (approximateParityMaps_supportPair D hd zeroDim free)

/-- Theorem 1.4: the odd square-trivial case of Proposition 7.1. -/
theorem theorem1_4 {V : Type v} [TopologicalSpace V] [Fintype V]
    [DiscreteTopology V] (H : SimpleGraph V) :
    Theorem14Statement.{u} H :=
  theorem1_4_of_proposition7_1 H (proposition7_1 H)

end

end AbelianTargets
