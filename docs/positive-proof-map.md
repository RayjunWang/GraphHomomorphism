# Theorem 1.4 and Proposition 7.1: proof map

Source: [arXiv:2609.39824v1](https://arxiv.org/html/2609.39824v1),
Sections 2–6 and 7.1. The general proofs are kernel-checked as
`AbelianTargets.theorem1_4` and `AbelianTargets.proposition7_1` in
[PositiveTheorems.lean](../AbelianTargets/PositiveTheorems.lean), with no
additional construction premise. They quantify over every positive dimension
and every free continuous zero-dimensional Polish lattice action.

## Exact hypotheses and low-dimensional results

`ReducedHomotopic H p q` is generated on genuine `SimpleGraph.Walk`s by
spur deletion, closed four-walk deletion, and concatenation.
`ReducedFundamentalGroup H b` is the checked quotient group of based loops.
The odd involution and torsion predicates agree with the corresponding
group assertions, and finite order agrees with mathlib's `IsOfFinOrder`.
Parity is preserved, an odd class is nonidentity, and every positive
trivializing power is even. Graph maps induce parity-preserving group maps.
`Examples.lean` checks the complete reduction of the square of a K₄ triangle.

`proposition7_1_dimensions_at_most_two` and
`theorem1_4_dimensions_at_most_two` quantify over every free continuous
lattice action in dimensions one and two. These earlier, separate proofs use the named reference assumptions in
[reference-axioms.md](reference-axioms.md). The final general proofs instead
construct the required maps directly.

## Checked geometric components

| Paper step | Implemented components | Scope |
| --- | --- | --- |
| Lemma 3.1 | Countable clopen independent covers, relative clopen maximal independent sets, and finite continuous colorings with explicit neighbor lists. | The stated interfaces and actual marker-priority coloring are proved. |
| Lemma 3.2 | Anisotropic markers; packing and overlap bounds; continuous fixed-index cuts; retained rectangles; actual bounded tiling; unique relative-interior cells; finite boundary strata; local finiteness; covariance and finite dependency patterns. | `exists_regularAnisotropicAtlas` constructs the atlas package for sufficiently large scales. No identification with a separately defined CW complex is claimed. |
| Lemma 4.1 | Finite interval carriers and fan triangulations; short digit walks; bounded carry rows; common-slot padding; simplex interpolation; moving bottom endpoints; fan and vertical collapses; whole-carrier contractions. | Actual contractions have logarithmic track speed, a finite joint Lipschitz constant, and a fixed base. |
| Lemma 5.1 | Explicit endpoint-fixed relative path homotopies and quantitative comparison estimates, including varying endpoints. | The analytic lemma is proved for an explicit controlled contraction. |
| Lemma 5.2 | Literal radial and rectangular extensions, boundary agreement, longitudinal/transverse estimates, boundary carrier maps, and transparent quantitative rank recursion. | Actual compatible full-rank carrier maps are constructed from carrier contractions. The action-level assembly is completed by the final four modules below. |
| Lemma 6.2 | Compact metric support space; free isometric shore swap; double-cover and reduced-homotopy lifts; odd torsion paths; null relation boundaries; finite topological presentation quotient. | The presentation image and support model are constructed. No identification with the paper's universal cover is claimed. |
| Carrier-to-support projection | Whole-cell relation charts, outer-edge restrictions, positive-support skeleton charts, finite simplex gluing, uniform three-vertex estimates, and inclusion/translation naturality. | `carrierProjection` is continuous with a modulus uniform in carrier interval and height. |
| Proposition 6.1 | Integer parity shear, anisotropic rank-rate bounds, successive scale selection, global projected Euclidean orbit maps, coordinate-unit estimates, and actual locally constant finite-range projected origin maps. | `SmallStepProjectedOrbitMaps` and `PositiveTheorems` complete the quantified construction on the original action. |
| Closing argument | Uniform probability error, support positivity, finite-image maximum-mass selection, and the resulting graph homomorphism. | The construction is supplied for every source action; `proposition7_1` and `theorem1_4` close without a geometry hypothesis. |

## Literal carrier contraction and projection

`FixedSlotPadding` converts bounded length-changing triangle rows into
equal-length schedules using checked pause slides. `FixedRowRealization`
and `CarrierRowRealization` realize those moves continuously in actual
probability simplex charts. `JointCarrierRows` gives finite joint
Lipschitz estimates. These modules supply the adapter missing initially.

`RealizedBottomCombing` handles continuous endpoints along the entire bottom
interval. Its paths use a common slot budget and have speed at most
`(3*m+8)*(Nat.log m R+1)`. `CarrierHeightDeformation` retracts the whole
triangulated carrier to height zero by literal fan and vertical collapses.
`CarrierControlledContraction` combines both deformations, fixes the base,
and proves the contraction endpoints and estimates.
`UniformCarrierContraction` gives, for common height `K` and bounded widths,
the uniform track bound `2*((3*m+8)*(K+1))` and a finite common joint bound.

`SegmentedOddPath` builds the alternating odd relation path directly from
`SupportTorsionData`, with explicit finitely many dyadic path slots.
`SupportCellCharts` gives one chart per whole polygon, so same-polygon
fan overlaps agree literally. `TriangleChartIntersections` and the exact
outer-edge formulas handle distinct polygon overlaps.
`CarrierSupportProjection` instantiates the actual finite-simplex gluer.
`UniformCarrierSupportProjection` proves a modulus independent of growing
intervals and heights using the uniform three-vertex face bound.
`CarrierProjectionNaturality` checks inclusions, translation parity, and
vertex values; `CarrierProjectionEdges` checks literal skeleton paths.

## Actual atlas and quantitative recursion

`ContinuousMarkerBoxes`, `RetainedMarkerTiles`, and `ActualMarkerAtlas`
construct the retained rectangular tiling. `RectangularBoundaryStrata`
and `RectangularAtlasBoundary` construct its compatible point-cell
stratification and finite boundary covers. `MarkerAtlasLocality`,
`ContinuousAtlasPatterns`, and `FiniteAtlasDependencyPatterns` describe
the bounded finite data determining local cells.

`DeterministicQuantitativeAtlas` constructs the rank recursion with an
explicit extension formula, rather than choosing a fresh extension at
each cell. `ActualMarkerQuantitativeAtlas` applies it to the actual marker
atlas and proves anisotropic coordinate bounds. Normalized contractions
are selected by interval width and transported by checked isometries;
`CanonicalIntervalContractions` proves their translation coherence.
`ControlledAtlasScaleChoice` proves actual logarithmic-speed bounds and
the successive first-scale/other-scale smallness estimates.

`ProjectedAtlasMaps` glues compatible cell projections to a global
continuous map on Euclidean orbit coordinates. `ProjectedAtlasEstimates`
proves coordinate-unit comparisons. `AtlasRankCovariance` and
`DeterministicAtlasCovariance` propagate a covariant local extension
through the actual recursion. `ProjectedAtlasCovariance` and
`ComputedProjectedCovariance` transfer covariance to the support map.
`ActualAtlasExtensionCovariance` checks the literal local extension
identity, and `CanonicalAtlasCovariance` closes the full rank recursion
for a fixed normalized contraction family. `CanonicalActionCovariance`
specializes this to the action-level origin map and proves its repointing
identity in both orientations.
`ActualProjectedOriginLocality` proves that the actual projected value
depends only on its bounded dependency pattern. `CanonicalProjectedOrigin`
proves local constancy, continuity, and finite range on the action space
for each fixed Euclidean point, including the origin.

## Concrete auxiliary space and closing argument

`SupportPair H` consists of compatible finite probability distributions.
The shore swap is a free isometry. Edge paths and square fillings realize
reduced graph homotopies in this space.
`supportTorsionData_of_oddTorsion` gives the path and null power needed by
the carrier charts. `PresentationComplex` and `PresentationImage`
construct a literal compact quotient and its compact metric support image.

The maximum probability coordinate is at least `1/|V|`. An error less than
`1/(2*|V|)` preserves positive mass on the neighboring shore, so compatibility
supplies a graph edge. `continuous_comp_of_finite_range` proves continuity
of a fixed selection on a finite image. `hasContinuousHom_of_supportModel`
and `PositiveGeometry` implement the rounding, including the empty case.
`ParityUnitSteps` closes directly from finite-image continuous origin maps,
parity covariance, and small coordinate unit-step errors. It avoids an
unnecessary global Lipschitz requirement after the support projection.

## Final quantified construction

The last four modules connect the checked geometric pieces:

1. [CanonicalActionCovariance.lean](../AbelianTargets/CanonicalActionCovariance.lean)
   proves the actual marker-map repointing identity and adapts existing
   single-interval comparisons to every integer lattice edge. It also
   defines `ParitySheared hd X`: the same topological space with action
   `h +ᵥ x := originalAction (S⁻¹ h) x`. The transported action is continuous
   and free. An original displacement `g` becomes `S g`.
2. [AtlasScaleParameters.lean](../AbelianTargets/AtlasScaleParameters.lean)
   constructs small-rate parameters for a supplied carrier-space tolerance.
   The height and common normalized contraction family depend only on the
   longitudinal scale `L`. The first-coordinate rank bound is
   `A_d * D(L) / L`, where `D(L)` grows logarithmically. With that family and
   its finite joint constant fixed, the transverse scale `M` controls the
   remaining rate `B_d(L) / M`. The actual marker lower-scale constraints
   are included in the selected parameters.
3. [SmallStepProjectedOrbitMaps.lean](../AbelianTargets/SmallStepProjectedOrbitMaps.lean)
   combines those parameters with the actual marker atlas and common
   projection modulus. `exists_smallStepLatticeOrbitMap` gives continuous
   finite-range origin values, exact parity covariance under every lattice
   displacement, and arbitrarily small integer unit-edge errors.
4. [PositiveTheorems.lean](../AbelianTargets/PositiveTheorems.lean)
   applies this construction to the inverse-sheared action. Every original
   generator has first coordinate one after shearing and is a sum of at
   most two positive lattice unit vectors. Two edge errors below `ε/2`
   therefore give the generator error below `ε`.
   `approximateParityMaps_supportPair` quantifies over all required actions.
   `proposition7_1` constructs `SupportTorsionData` from the exact odd torsion
   hypothesis and applies probability rounding. `theorem1_4` is its odd
   square-trivial special case.

This route uses the uniformly continuous support projection only on integer
unit edges. It does not require a global projected Lipschitz bound or
unit-step estimates from every real starting point.

`TorsionFieldConstruction`, `AnisotropicParityConstruction`, and
`UniversalAnisotropicSupportConstruction` remain explicit propositions and
conditional interfaces. They are not axioms, and the final positive proofs
do not take them as hypotheses. The older stronger anisotropic interface is
not an unfinished obligation of the completed lattice-edge route.
