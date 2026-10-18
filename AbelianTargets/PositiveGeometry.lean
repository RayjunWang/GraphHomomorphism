import AbelianTargets.SupportWitness
import AbelianTargets.PresentationImage
import AbelianTargets.ParityFields
import AbelianTargets.Statements

/-!
# An alternative anisotropic closing interface

The support space, swap, generator paths, torsion boundary fillings,
successive scale choice, and final graph rounding are actual constructions.
This module retains the stronger global anisotropic-map premise as an
alternative closing API. The unconditional results in `PositiveTheorems`
use constructed integer-step bounds instead, without that premise.
-/

namespace AbelianTargets

universe u v

noncomputable section

variable {V : Type v} [TopologicalSpace V] [Fintype V]

theorem hasContinuousHom_of_anisotropicSupportConstruction
    {d : ℕ} {X : Type u} [TopologicalSpace X] [AddAction (Lattice d) X]
    [Nonempty V] (H : SimpleGraph V) (hd : 1 ≤ d)
    (construction : AnisotropicParityConstruction X (SupportPair H) (SupportPair.swap H) hd) :
    HasContinuousHom (d := d) (X := X) H :=
  SupportPair.hasContinuousHom_of_approximateSwap H
    (approximateParityMaps_of_anisotropicConstruction (SupportPair.isometry_swap H) construction)

/-- The same analytic closing argument on the actual compact metric image
of the filled parity presentation. -/
theorem hasContinuousHom_of_anisotropicPresentationConstruction
    {d : ℕ} {X : Type u} [TopologicalSpace X] [AddAction (Lattice d) X]
    [Nonempty V] {H : SimpleGraph V} (D : SupportTorsionData H) (hd : 1 ≤ d)
    (construction : AnisotropicParityConstruction X (ParityPresentation.Image D)
      (ParityPresentation.imageSwap D) hd) :
    HasContinuousHom (d := d) (X := X) H :=
  ParityPresentation.hasContinuousHom_of_approximateImage D
    (approximateParityMaps_of_anisotropicConstruction (ParityPresentation.isometry_imageSwap D) construction)

/-- A stronger alternative construction interface after constructing the
support-space torsion data. Continuity, finite image, covariance, and
global coordinate estimates are explicit fields of these orbit maps. -/
def UniversalAnisotropicSupportConstruction (H : SimpleGraph V) : Prop :=
  ∀ (_D : SupportTorsionData H) (d : ℕ) (hd : 1 ≤ d),
    ∀ (X : Type u) [TopologicalSpace X] [PolishSpace X]
      [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X],
      ZeroDimensional X → IsFree (G := Lattice d) (X := X) →
        AnisotropicParityConstruction X (SupportPair H) (SupportPair.swap H) hd

/-- Closing deduction for Proposition 7.1 from the stronger alternative
anisotropic interface. The direct unconditional proof is in `PositiveTheorems`. -/
theorem proposition7_1_of_anisotropicSupportConstruction
    (H : SimpleGraph V) [DiscreteTopology V]
    (geometry : UniversalAnisotropicSupportConstruction.{u} H) :
    Proposition71Statement.{u} H := by
  intro ht d hd X _ _ _ _ hzero hfree
  obtain ⟨D⟩ := supportTorsionData_of_oddTorsion H ht
  letI : Nonempty V := D.base.left.nonempty
  exact hasContinuousHom_of_anisotropicSupportConstruction H hd (geometry D d hd X hzero hfree)

/-- Theorem 1.4 follows from the same geometric construction because
the odd order-two hypothesis is a special case of odd finite torsion. -/
theorem theorem1_4_of_anisotropicSupportConstruction
    (H : SimpleGraph V) [DiscreteTopology V]
    (geometry : UniversalAnisotropicSupportConstruction.{u} H) :
    Theorem14Statement.{u} H :=
  theorem1_4_of_proposition7_1 H (proposition7_1_of_anisotropicSupportConstruction H geometry)

end

end AbelianTargets
