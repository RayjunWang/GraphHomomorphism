# Permitted reference assumptions

The user explicitly authorized results from papers cited by arXiv:2609.39824
as axioms on 2026-10-09. The target paper's own new statements and lemmas are
not covered by this authorization. The declaration audit admits only the
individual external declarations listed here, in addition to Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`.


## Dependency scope of the requested results

The new general proofs `AbelianTargets.proposition7_1` and
`AbelianTargets.theorem1_4` in
[PositiveTheorems.lean](../AbelianTargets/PositiveTheorems.lean) construct the
maps directly. Their individually checked kernel dependencies are exactly
`propext`, `Classical.choice`, and `Quot.sound`. They do
not invoke any of the five reference axioms below.

`AbelianTargets.proposition7_7` retains its previous dependencies on
`bernshteyn_theorem_1_12`, `gjks_direction_preserving_twelve_tiles`, and
`gjks_eventual_twelve_tile_source`. The audit allowlist also retains the two
other reference specializations used elsewhere in the library.

## Bernshteyn [1], Theorem 1.12

Source: *Probabilistic constructions in continuous combinatorics and a bridge
to distributed algorithms*, Advances in Mathematics 415 (2023), 108895.
[Author's arXiv version 2102.08797v2](https://arxiv.org/html/2102.08797v2#S1.SS3.SSS1).

The theorem equates the existence of a continuous coloring avoiding a finite
set of finite patterns on the free binary shift with its existence on every
free zero-dimensional Polish action of the countably infinite group.

`AbelianTargets.References.bernshteyn_theorem_1_12` specializes this to
`ℤ^d`, `d ≥ 1`, and a finite discrete simple graph target. The forbidden
patterns are the nonadjacent target pairs on `{0,e_i}`. It asserts
`InClass d H → UniversalTarget d H`. It imposes no positive condition on
the target and does not assert existence of a coloring of the free shift.

## Gao–Jackson–Krohne–Seward [4], Theorem 3.5.1

Source: *Continuous Combinatorics of Abelian Group Actions*, Memoirs of the
AMS 311 (2025), no. 1573, 1–120.
[Author-hosted PDF](https://mathweb.ucsd.edu/~bseward/Files/continuousabelian.pdf),
printed page 91 (PDF page 91), Theorem 3.5.1; arXiv:1803.03872.

The theorem gives a continuous graph homomorphism from the free binary
`ℤ²` shift when the target has an odd closed walk whose reduced homotopy
class has finite order. The source's word “cycle” permits repeated vertices;
the discussion immediately preceding the theorem uses alternating walks.

`AbelianTargets.References.gjks_theorem_3_5_1` is the finite target
specialization `HasOddTorsion H → InClass 2 H`. The reduced homotopy
relation, quotient group, and equivalence of the finite-order formulations
are proved in this project. This axiom applies only in dimension two.

## Earlier low-dimensional consequences

`proposition7_1_dimension_one`, `proposition7_1_dimension_two`, and
`proposition7_1_dimensions_at_most_two` combine the two reference assumptions
with the proved embedding of successive free shifts.
`theorem1_4_dimensions_at_most_two` additionally uses the proved fact that
an odd involution has finite order. They prove the requested positive
statements for `1 ≤ d ≤ 2` through a separate reference-based route.
The direct general proofs now cover all `d ≥ 1` without these reference axioms.

## The width-one twelve-tile source assumptions

`AbelianTargets.References.gjks_direction_preserving_twelve_tiles` is the
width-one specialization of GJKS Theorem 2.5.1. Its conclusion uses the
literal positive horizontal and vertical step relations of the concrete
twelve-grid gluing defined in `TwelveTiles.lean`.

`AbelianTargets.References.gjks_eventual_twelve_tile_source` is the
width-one specialization of GJKS Corollary 3.3.1, implication (1) to (4).
It supplies maps from all sufficiently large admissible twelve-tile
graphs to a finite graph already known to belong to `𝓗₂`.

`AbelianTargets.References.bernshteyn_directed_twelve_tiles_universality`
is a second finite-pattern specialization of Bernshteyn Theorem 1.12.
It transfers an existing direction-preserving twelve-tile map from the
free binary `ℤ²` shift to a free zero-dimensional Polish `ℤ²` action.
The source map is an explicit premise of the axiom. This retains the
separate dependency on the GJKS source-map theorem.

The compact factorization, layered compact free model, higher-dimensional
finite-source extraction, direction rigidity, and translation arguments
are proved here. They are not included among the reference assumptions.
