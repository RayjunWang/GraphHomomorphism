# Positive-proof completion

The general Theorem 1.4 and Proposition 7.1 are proved and kernel-checked in
[PositiveTheorems.lean](../AbelianTargets/PositiveTheorems.lean), for every
positive dimension. Their theorem types contain no extra geometric premise.
This page retains its historical filename so earlier links remain valid.

The final assembly discharges the obligations left by the 9 October run:

| Earlier obligation | Implemented proof |
| --- | --- |
| Action-level covariance of the canonical map | [CanonicalActionCovariance.lean](../AbelianTargets/CanonicalActionCovariance.lean) specializes the literal rank covariance to the repointed marker tiling and transfers it through the support projection. |
| Correct original generators after the parity shear | The same module defines `ParitySheared`, pulls the action back along the inverse lattice automorphism, and proves continuity, freeness, and the original-to-sheared displacement identity. |
| Quantitative choices without circular dependence | [AtlasScaleParameters.lean](../AbelianTargets/AtlasScaleParameters.lean) fixes the height and common contraction family as functions of the longitudinal scale before choosing the transverse scale. |
| Actual approximate maps for every source action | [SmallStepProjectedOrbitMaps.lean](../AbelianTargets/SmallStepProjectedOrbitMaps.lean) instantiates the uniform projection modulus, actual marker atlas, quantitative recursion, and integer-edge estimates. |
| Unconditional target statements | [PositiveTheorems.lean](../AbelianTargets/PositiveTheorems.lean) transfers the maps to the original action and invokes checked probability rounding. |

The integer lattice suffices: each sheared original generator is either the
first unit vector or the sum of the first and one transverse unit vector.
Using an error below half the desired tolerance for each edge gives the
required generator error. This avoids the stronger interface asking for
unit-step estimates from arbitrary real starting points.

The older `UniversalAnisotropicSupportConstruction` and
`AnisotropicParityConstruction` interfaces remain useful conditional
statements. The final proof does not use them and does not need to establish
their stronger projected global coordinate bounds. Their presence is no
longer an open premise in either requested theorem.

The [verification report](verification.json) is the machine-readable record
of final build, audit, hashes, and theorem scope. See
[positive-proof-map.md](positive-proof-map.md) for the full construction.
