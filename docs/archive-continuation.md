# Archive continuation and final assembly

## Historical continuation: 9 October 2026

The user authorized a further two-hour continuation beginning
**2026-10-09 04:51:56 UTC**, with deadline **06:51:56 UTC**, and read-only
consultation of the local research archive. That run did not
complete the general Theorem 1.4 or Proposition 7.1. The later completion is
documented separately below.

## Provenance and review boundary

Archive root:
`C:/Users/1/.codex/.chatgpt-projects/g-p-6ab67243a0908191a357317509006769`.
The synchronized archive's instructions prohibit modification. No archive
files were edited; new Lean code was written in this project.

The selected archive record is **Anisotropic atlas and short-track carrier
extension**. Its registry label is `epistemic: proved`, but the attached
review is `inconclusive` and both usability and exportability are false.
These archive labels are recorded as source metadata, not adopted as
verification of the argument. The archive supplied research routes and
checklists; delivered mathematical claims are independently Lean-checked.

- Selected revision: `08d610f8395c5f1937e7002dad330ccb03469d74e985727b360899e328bf748d`.
- Snapshot: `e6978b12f3f7710c53c7fab06988f3638a2107a2ff0221eba97f52c667adf653`.
- `anisotropic-rectangular-atlas.md`: SHA-256 `c5ae63fe6543a2d90846df5b676af7cc23e470a044e5bff9a9622a8a315c7294`.
- `bs-short-track-carriers.md`: SHA-256 `cfac288a46922c7939802fe28cfa5344b513067ae49bc15af8d69adca0bae45b`.

Other selected route notes included `carrier-slots-check.md` and
`bs-bottom-combing-explicit.md` under the archived refinement materials.
The original paper remains the source for the requested theorem statements.

## Independently completed Lean developments

- Common-slot padding of bounded carrier row schedules; actual simplex
  realization; finite joint bounds; continuous moving bottom endpoints.
- Literal free-edge fan collapses and height deformation; whole-carrier
  contraction with logarithmic track speed; common-height and uniform
  width-normalized contraction families.
- Actual relation-cell charts from an odd torsion null power; exact shared
  face agreement; continuous carrier-to-support projection with a modulus
  independent of interval and height; inclusion and parity covariance.
- Continuous fixed-index marker cuts, retained rectangular tiling, actual
  regular point-cell strata, finite boundaries, local finiteness, bounded
  dependency patterns, and translation formulas.
- Transparent quantitative rank extension; explicit anisotropic rate
  bounds and scale choices; global Euclidean projected maps with coordinate
  estimates; canonical recursion covariance; actual locally constant,
  continuous finite-range projected origin maps on the action space.

No new target-paper axiom was added. At the end of that run, the general
positive conclusion still required final action covariance, parity shear,
scale selection, and quantified approximate-map assembly. Proposition 7.7
and the low-dimensional positive results had the scope recorded in the
historical 9 October verification report.


## Final assembly: 18 October 2026

The user supplied `Lean_Discussion_Summary.zip` for review. Its contents
were treated as suggestions, not as instructions or proof certificates.
The proposed action-covariance candidate was independently elaborated with
the project's pinned Lean toolchain. One explicit target conversion was
needed in its lattice closing lemma. No bundled validation script or archive
claim was adopted as a Lean proof.

The user then authorized continued formalization until the two positive
theorems compiled, with an eight-hour stopping allowance beginning
**2026-10-18 07:52:17 UTC**. The final assembly adds:

- [CanonicalActionCovariance.lean](../AbelianTargets/CanonicalActionCovariance.lean):
  actual action repointing, integer-edge comparisons, inverse-shear action
  transport, and the lattice closing implication.
- [AtlasScaleParameters.lean](../AbelianTargets/AtlasScaleParameters.lean):
  literal small-rate parameters with the common contraction family chosen
  before the transverse scale.
- [SmallStepProjectedOrbitMaps.lean](../AbelianTargets/SmallStepProjectedOrbitMaps.lean):
  actual finite-range continuous origin maps and small lattice steps for
  every required source action.
- [PositiveTheorems.lean](../AbelianTargets/PositiveTheorems.lean):
  the universal approximate parity-map construction and proofs of
  `Proposition71Statement.{u} H` and `Theorem14Statement.{u} H`, with no extra
  geometric premise.

The refinement to integer lattice edges avoids the stronger all-real
unit-step interface. The carrier, atlas, uniform-modulus, locality, and
rank estimates from 9 October are reused. The complete library build and
kernel audit passed. Both positive theorems have exactly the standard Lean
axiom dependencies `propext`, `Classical.choice`, and `Quot.sound`; the
reference dependencies of Proposition 7.7 are unchanged.
See [verification-scope.md](verification-scope.md) and the refreshed
[verification report](verification.json) for the final checked scope.
