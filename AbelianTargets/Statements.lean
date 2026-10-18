import AbelianTargets.Actions
import AbelianTargets.ReducedWalks
import AbelianTargets.SupportModel
import AbelianTargets.MarkerWindows

/-!
# Exact requested statements and intermediate construction interfaces

`Theorem14Statement` and `Proposition71Statement` give the exact requested
positive propositions. Their unconditional proofs in every positive dimension
are `theorem1_4` and `proposition7_1` in `PositiveTheorems.lean`.
The intermediate construction interface and conditional closing implications
below are retained as reusable APIs.
-/

namespace AbelianTargets

universe u v

variable {V : Type v} [TopologicalSpace V]

/-- Theorem 1.4, with the paper's exact reduced-walk hypothesis. -/
def Theorem14Statement (H : SimpleGraph V) [Fintype V] [DiscreteTopology V] : Prop :=
  HasOddInvolution H → ∀ d : ℕ, 1 ≤ d → UniversalTarget.{u} d H

/-- Proposition 7.1, with the paper's exact positive finite-order hypothesis. -/
def Proposition71Statement (H : SimpleGraph V) [Fintype V] [DiscreteTopology V] : Prop :=
  HasOddTorsion H → ∀ d : ℕ, 1 ≤ d → UniversalTarget.{u} d H

/-- The intermediate probability-field construction interface for Sections
3–6 and Proposition 7.1. It is a proposition, never an axiom. The final
proofs construct approximate support maps and close directly. -/
def TorsionFieldConstruction (H : SimpleGraph V) [Fintype V] [DiscreteTopology V] : Prop :=
  HasOddTorsion H → ∀ d : ℕ, 1 ≤ d →
    ∀ (X : Type u) [TopologicalSpace X] [PolishSpace X]
      [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X],
      ZeroDimensional X → IsFree (G := Lattice d) (X := X) →
        Nonempty (ProbabilityField (d := d) (X := X) H)

/-- Checked closing implication for a supplied probability-field
construction. The unconditional theorem is in `PositiveTheorems.lean`. -/
theorem proposition7_1_of_torsionFieldConstruction (H : SimpleGraph V)
    [Fintype V] [DiscreteTopology V]
    (construction : TorsionFieldConstruction.{u} H) :
    Proposition71Statement.{u} H := by
  intro ht d hd X _ _ _ _ hzero hfree
  obtain ⟨field⟩ := construction ht d hd X hzero hfree
  exact hasContinuousHom_of_probabilityField field

/-- Theorem 1.4 is a special case of Proposition 7.1: order two is finite. -/
theorem theorem1_4_of_proposition7_1 (H : SimpleGraph V)
    [Fintype V] [DiscreteTopology V]
    (h71 : Proposition71Statement.{u} H) : Theorem14Statement.{u} H := by
  intro h14
  exact h71 h14.hasOddTorsion

/-- Conditional proof of Theorem 1.4 from the missing torsion construction. -/
theorem theorem1_4_of_torsionFieldConstruction (H : SimpleGraph V)
    [Fintype V] [DiscreteTopology V]
    (construction : TorsionFieldConstruction.{u} H) :
    Theorem14Statement.{u} H :=
  theorem1_4_of_proposition7_1 H
    (proposition7_1_of_torsionFieldConstruction H construction)

/-- Proposition 7.7 for the literal finite marker-window graph of (9).
The full proof is `proposition7_7` in `Proposition77.lean`. -/
def Proposition77Statement : Prop :=
  ∀ (d L : ℕ), 1 ≤ d → ∀ hL : 4 ≤ L,
    InClass d (MarkerGraph d L hL) ∧ ¬InClass (d + 1) (MarkerGraph d L hL)

end AbelianTargets
