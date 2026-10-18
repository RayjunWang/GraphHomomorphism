import AbelianTargets.Actions
import AbelianTargets.ReducedWalks
import AbelianTargets.DimensionEmbedding

/-!
# Explicit assumptions from the cited literature

The user authorized results of the target paper's references as axioms.
This module contains only specializations of two verified external results.
Neither axiom asserts any of the new higher-dimensional results of
arXiv:2609.39824. See `docs/reference-axioms.md` for their source statements.
-/

namespace AbelianTargets

universe u v

namespace References

/-- Bernshteyn [1], Theorem 1.12, specialized to the finite forbidden
edge patterns of a finite graph and the standard generating set of `ℤᵈ`.
The condition `1 ≤ d` ensures that the group is countably infinite. -/
axiom bernshteyn_theorem_1_12
    {V : Type v} [TopologicalSpace V] [Fintype V] [DiscreteTopology V]
    (H : SimpleGraph V) (d : ℕ) (hd : 1 ≤ d) :
    InClass d H → UniversalTarget.{u} d H

/-- Gao–Jackson–Krohne–Seward [4], Theorem 3.5.1 (author PDF, p. 91):
an odd closed walk of finite order in the reduced homotopy group gives
a continuous homomorphism from the two-dimensional free binary shift.
Their term "cycle" allows repeated vertices, as used in the same section. -/
axiom gjks_theorem_3_5_1
    {V : Type v} [TopologicalSpace V] [Fintype V] [DiscreteTopology V]
    (H : SimpleGraph V) : HasOddTorsion H → InClass 2 H

end References

/-- The two-dimensional case of Proposition 7.1, using exactly the
cited two-dimensional theorem and continuous universality. -/
theorem proposition7_1_dimension_two
    {V : Type v} [TopologicalSpace V] [Fintype V] [DiscreteTopology V]
    (H : SimpleGraph V) (ht : HasOddTorsion H) : UniversalTarget.{u} 2 H :=
  References.bernshteyn_theorem_1_12 H 2 (by decide)
    (References.gjks_theorem_3_5_1 H ht)

/-- Restriction to the sparse coordinate plane proves the one-dimensional
case from the two-dimensional reference result. -/
theorem proposition7_1_dimension_one
    {V : Type v} [TopologicalSpace V] [Fintype V] [DiscreteTopology V]
    (H : SimpleGraph V) (ht : HasOddTorsion H) : UniversalTarget.{u} 1 H :=
  References.bernshteyn_theorem_1_12 H 1 (by decide)
    (inClass_succ_subset (by decide : 1 ≤ 1)
      (References.gjks_theorem_3_5_1 H ht))

/-- Complete proof of Proposition 7.1 for the range `1 ≤ d ≤ 2`, relative
to the two explicit reference axioms above. The general range is separate. -/
theorem proposition7_1_dimensions_at_most_two
    {V : Type v} [TopologicalSpace V] [Fintype V] [DiscreteTopology V]
    (H : SimpleGraph V) (ht : HasOddTorsion H)
    (d : ℕ) (hd : 1 ≤ d) (hd2 : d ≤ 2) : UniversalTarget.{u} d H := by
  have h : d = 1 ∨ d = 2 := by omega
  rcases h with rfl | rfl
  · exact proposition7_1_dimension_one H ht
  · exact proposition7_1_dimension_two H ht

/-- Complete proof of Theorem 1.4 for the range `1 ≤ d ≤ 2`, relative
to the verified reference results. -/
theorem theorem1_4_dimensions_at_most_two
    {V : Type v} [TopologicalSpace V] [Fintype V] [DiscreteTopology V]
    (H : SimpleGraph V) (ht : HasOddInvolution H)
    (d : ℕ) (hd : 1 ≤ d) (hd2 : d ≤ 2) : UniversalTarget.{u} d H :=
  proposition7_1_dimensions_at_most_two H ht.hasOddTorsion d hd hd2

end AbelianTargets
