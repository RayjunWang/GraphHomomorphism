# Library module index

Every library source below is explicitly imported by `AbelianTargets.lean`
and included in the kernel dependency audit. The requested positive proofs
are in [PositiveTheorems.lean](../AbelianTargets/PositiveTheorems.lean), and
Proposition 7.7 is in [Proposition77.lean](../AbelianTargets/Proposition77.lean).
[Statements.lean](../AbelianTargets/Statements.lean) defines their exact types.
The older conditional construction interfaces remain available; neither
final positive theorem takes one as an extra premise.

See [positive-proof-map.md](positive-proof-map.md) for the full construction.

Total library modules: **257**.

| Module | Topic |
| --- | --- |
| [Actions.lean](../AbelianTargets/Actions.lean) | Definitions for arXiv:2609.39824v1, Sections 2.1 and 7.2. The action convention is `(g +ᵥ x)(u) = x(u + g)`. |
| [ActualAtlasExtensionCovariance.lean](../AbelianTargets/ActualAtlasExtensionCovariance.lean) | Actual Atlas Extension Covariance |
| [ActualMarkerAtlas.lean](../AbelianTargets/ActualMarkerAtlas.lean) | The actual bounded rectangular tiling, and its regular point-cell atlas, constructed from continuous covariant marker cuts. |
| [ActualMarkerQuantitativeAtlas.lean](../AbelianTargets/ActualMarkerQuantitativeAtlas.lean) | Actual Marker Quantitative Atlas |
| [ActualProjectedOriginLocality.lean](../AbelianTargets/ActualProjectedOriginLocality.lean) | Actual Projected Origin Locality |
| [ActualQuantitativeAtlasRecursion.lean](../AbelianTargets/ActualQuantitativeAtlasRecursion.lean) | Actual Quantitative Atlas Recursion |
| [AdjacentSliceDirections.lean](../AbelianTargets/AdjacentSliceDirections.lean) | Adjacent Slice Directions |
| [AnisotropicMarkers.lean](../AbelianTargets/AnisotropicMarkers.lean) | Clopen markers at independent coordinate scales |
| [AnisotropicRankRates.lean](../AbelianTargets/AnisotropicRankRates.lean) | Anisotropic Rank Rates |
| [AnisotropicScales.lean](../AbelianTargets/AnisotropicScales.lean) | Successive scale choice in Proposition 6.1 |
| [AppendedEdgeRows.lean](../AbelianTargets/AppendedEdgeRows.lean) | The concrete row data used in the first half of a bottom-edge splice. |
| [AppendedSpliceData.lean](../AbelianTargets/AppendedSpliceData.lean) | Constructing the complete moving-endpoint data from literal appended edge rows. |
| [AtlasBoundaryCarrierMaps.lean](../AbelianTargets/AtlasBoundaryCarrierMaps.lean) | Compatible maps on actual lower-rank strata lift continuously into the literal carrier of a parent cell. The canonical value uses the true point cell, and the… |
| [AtlasBoundaryCoordinateBounds.lean](../AbelianTargets/AtlasBoundaryCoordinateBounds.lean) | Coordinate estimates survive subdivisions of actual cell boundaries. |
| [AtlasBoundaryPathBounds.lean](../AbelianTargets/AtlasBoundaryPathBounds.lean) | The subdivided cell boundary retains its controlled first path variable. |
| [AtlasBoundaryTranslation.lean](../AbelianTargets/AtlasBoundaryTranslation.lean) | Atlas Boundary Translation |
| [AtlasBoundaryTransverseBounds.lean](../AbelianTargets/AtlasBoundaryTransverseBounds.lean) | Atlas Boundary Transverse Bounds |
| [AtlasBoxes.lean](../AbelianTargets/AtlasBoxes.lean) | Covering and overlap bounds for the actual marker boxes |
| [AtlasCanonicalContractions.lean](../AbelianTargets/AtlasCanonicalContractions.lean) | One fixed family of contractions at zero-based interval widths gives a literal contraction provider on all atlas cells, with exact translation covariance. There… |
| [AtlasCarrierEndpoints.lean](../AbelianTargets/AtlasCarrierEndpoints.lean) | Atlas Carrier Endpoints |
| [AtlasCellContractions.lean](../AbelianTargets/AtlasCellContractions.lean) | Atlas Cell Contractions |
| [AtlasCellLocality.lean](../AbelianTargets/AtlasCellLocality.lean) | Atlas Cell Locality |
| [AtlasControlledCellExtension.lean](../AbelianTargets/AtlasControlledCellExtension.lean) | Atlas Controlled Cell Extension |
| [AtlasCuts.lean](../AbelianTargets/AtlasCuts.lean) | The finite cut-selection argument in Lemma 3.2 |
| [AtlasDependencyAgreement.lean](../AbelianTargets/AtlasDependencyAgreement.lean) | Equality of the finite dependency pattern determines the point cell and every cell contained in a parent through the evaluation point. |
| [AtlasEndpointRecursion.lean](../AbelianTargets/AtlasEndpointRecursion.lean) | Atlas Endpoint Recursion |
| [AtlasPacking.lean](../AbelianTargets/AtlasPacking.lean) | Anisotropic marker packing |
| [AtlasQuantitativeRecursion.lean](../AbelianTargets/AtlasQuantitativeRecursion.lean) | Atlas Quantitative Recursion |
| [AtlasRankCovariance.lean](../AbelianTargets/AtlasRankCovariance.lean) | Translation covariance propagates through the literal rank recursion. |
| [AtlasRankRecursion.lean](../AbelianTargets/AtlasRankRecursion.lean) | Rank recursion for actual atlas cells and literal interval carriers. The local extension operator remains an explicit input; this module proves the global… |
| [AtlasRelativeCellExtension.lean](../AbelianTargets/AtlasRelativeCellExtension.lean) | Atlas Relative Cell Extension |
| [AtlasScaleParameters.lean](../AbelianTargets/AtlasScaleParameters.lean) | Small anisotropic rank rates with a common normalized contraction family selected before the transverse scale. |
| [BottomCarrierClassification.lean](../AbelianTargets/BottomCarrierClassification.lean) | Literal height-zero carrier faces are single vertices or adjacent horizontal unit edges. Hence every bottom realization point is exactly recovered from its… |
| [BottomCombingBounds.lean](../AbelianTargets/BottomCombingBounds.lean) | An explicit logarithmic track bound for the actual bottom combing. |
| [BottomCoordinateInverse.lean](../AbelianTargets/BottomCoordinateInverse.lean) | The actual affine bottom interval is inverted by its barycentric horizontal coordinate, on every singleton and unit bottom edge. |
| [BottomEdgeSplice.lean](../AbelianTargets/BottomEdgeSplice.lean) | The complete moving-endpoint family across one bottom edge. |
| [BottomHeightZero.lean](../AbelianTargets/BottomHeightZero.lean) | Bottom Height Zero |
| [BottomIntervalMap.lean](../AbelianTargets/BottomIntervalMap.lean) | The literal affine bottom interval in barycentric carrier coordinates. |
| [BoundedCarries.lean](../AbelianTargets/BoundedCarries.lean) | Bounded cellular moves on compressed words |
| [CanonicalActionCovariance.lean](../AbelianTargets/CanonicalActionCovariance.lean) | Action repointing, actual projected covariance, integer lattice steps, inverse-shear action transport, and lattice parity closing. |
| [CanonicalAtlasCovariance.lean](../AbelianTargets/CanonicalAtlasCovariance.lean) | Translation covariance of the literal rank recursion driven by a single normalized contraction family. |
| [CanonicalIntervalContractions.lean](../AbelianTargets/CanonicalIntervalContractions.lean) | Contractions are selected once at zero-based interval widths and then transported by an explicit isometry. The normalized data are retained as data rather than… |
| [CanonicalMarkerQuantitativeAtlas.lean](../AbelianTargets/CanonicalMarkerQuantitativeAtlas.lean) | Canonical Marker Quantitative Atlas |
| [CanonicalProjectedOrigin.lean](../AbelianTargets/CanonicalProjectedOrigin.lean) | Canonical Projected Origin |
| [CanonicalRows.lean](../AbelianTargets/CanonicalRows.lean) | # Canonical endpoint-padded rows and their exact fixed-slot endpoints |
| [CarrierCellRealization.lean](../AbelianTargets/CarrierCellRealization.lean) | # Every digital relation move uses a cell of the literal finite carrier |
| [CarrierCharts.lean](../AbelianTargets/CarrierCharts.lean) | Convex ambient charts of the actual finite interval carrier. |
| [CarrierCollapseFixed.lean](../AbelianTargets/CarrierCollapseFixed.lean) | Carrier Collapse Fixed |
| [CarrierControlledContraction.lean](../AbelianTargets/CarrierControlledContraction.lean) | An actual controlled contraction of the finite triangulated interval carrier. Every track has logarithmic speed; the joint constant is finite. |
| [CarrierFaceBound.lean](../AbelianTargets/CarrierFaceBound.lean) | Uniform simplex dimension, independent of the size of the carrier. |
| [CarrierFanMoves.lean](../AbelianTargets/CarrierFanMoves.lean) | # Actual presentation polygons collapse by bounded fan row moves |
| [CarrierGeometry.lean](../AbelianTargets/CarrierGeometry.lean) | # The actual finite barycentric interval carrier The carrier is the union of the probability-simplex faces specified by the finite fan triangulation. Its… |
| [CarrierHeightChain.lean](../AbelianTargets/CarrierHeightChain.lean) | Actual height-by-height deformation curves in one fixed carrier. |
| [CarrierHeightCut.lean](../AbelianTargets/CarrierHeightCut.lean) | Carrier Height Cut |
| [CarrierHeightDeformation.lean](../AbelianTargets/CarrierHeightDeformation.lean) | The actual finite strip is deformed to its literal bottom edges in logarithmic-height time, with a speed independent of its horizontal size. |
| [CarrierIntervalInclusion.lean](../AbelianTargets/CarrierIntervalInclusion.lean) | Literal isometric inclusions of nested bounded interval carriers. |
| [CarrierNesting.lean](../AbelianTargets/CarrierNesting.lean) | Carrier Nesting |
| [CarrierProjectionEdges.lean](../AbelianTargets/CarrierProjectionEdges.lean) | Exact images of the literal horizontal and vertical carrier edge paths. |
| [CarrierProjectionFaceCharts.lean](../AbelianTargets/CarrierProjectionFaceCharts.lean) | Carrier Projection Face Charts |
| [CarrierProjectionGluing.lean](../AbelianTargets/CarrierProjectionGluing.lean) | Global carrier projections assembled from polygon and skeleton charts. |
| [CarrierProjectionNaturality.lean](../AbelianTargets/CarrierProjectionNaturality.lean) | Carrier Projection Naturality |
| [CarrierRowRealization.lean](../AbelianTargets/CarrierRowRealization.lean) | Literal interval-carrier row moves, realized in barycentric coordinates. |
| [CarrierSupportProjection.lean](../AbelianTargets/CarrierSupportProjection.lean) | The actual continuous carrier projection supplied by odd torsion. |
| [CarrierTranslationEquiv.lean](../AbelianTargets/CarrierTranslationEquiv.lean) | Carrier Translation Equiv |
| [CarrierTranslationGeometry.lean](../AbelianTargets/CarrierTranslationGeometry.lean) | Literal horizontal translation is an isometry of barycentric carriers. |
| [CarrierTriangulation.lean](../AbelianTargets/CarrierTriangulation.lean) | Finite polygon fans in the actual interval carrier |
| [CartesianConstancy.lean](../AbelianTargets/CartesianConstancy.lean) | Propagation across a finite Cartesian product |
| [ClopenColoring.lean](../AbelianTargets/ClopenColoring.lean) | Continuous finite coloring from a countable clopen independent cover |
| [ClopenMarkers.lean](../AbelianTargets/ClopenMarkers.lean) | A clopen maximal independent set from a countable clopen independent cover |
| [CollapseTransport.lean](../AbelianTargets/CollapseTransport.lean) | Collapse Transport |
| [CommonHeightCarrierContraction.lean](../AbelianTargets/CommonHeightCarrierContraction.lean) | Controlled contractions at a common height, including intervals shorter than the ambient logarithmic scale. |
| [CompactFactorization.lean](../AbelianTargets/CompactFactorization.lean) | Compact finite-product colorings factor through finite coordinate codes |
| [CompactFreeModel.lean](../AbelianTargets/CompactFreeModel.lean) | A compact free lattice action recording displacement three-colorings |
| [CompressedCarrierWalks.lean](../AbelianTargets/CompressedCarrierWalks.lean) | Actual logarithmically short walks in finite interval carriers |
| [CompressedWords.lean](../AbelianTargets/CompressedWords.lean) | Base-m compressed Baumslag--Solitar words |
| [ComputedProjectedCovariance.lean](../AbelianTargets/ComputedProjectedCovariance.lean) | Covariance of a checked full-rank atlas gives covariance of its actual support projection. |
| [ConeDomainNaturality.lean](../AbelianTargets/ConeDomainNaturality.lean) | The relative cone formula respects linear isometries of the transverse coordinate space. In particular, a relabeling of active rectangular axes does not change… |
| [ContextualCarrierRows.lean](../AbelianTargets/ContextualCarrierRows.lean) | # Literal path contexts preserve the bounded fan row homotopies |
| [ContinuousAtlasPatterns.lean](../AbelianTargets/ContinuousAtlasPatterns.lean) | Actual finite atlas patterns on a fixed spatial neighborhood. |
| [ContinuousAtlasStrata.lean](../AbelianTargets/ContinuousAtlasStrata.lean) | The actual incident tile lists and point cells are locally constant in the action point. The proof uses the finite universe of bounded integer rectangles near… |
| [ContinuousMarkerBoxes.lean](../AbelianTargets/ContinuousMarkerBoxes.lean) | # Actual continuous covariant marker boxes This record contains cut data, rather than a tiling or an assumed atlas. Its existence follows from the checked… |
| [ContinuousOrbitCuts.lean](../AbelianTargets/ContinuousOrbitCuts.lean) | Continuous local marker inputs on a fixed lattice index |
| [ContinuousPriorityCuts.lean](../AbelianTargets/ContinuousPriorityCuts.lean) | Continuity of finite priority-cut processing |
| [ControlledAtlasScaleChoice.lean](../AbelianTargets/ControlledAtlasScaleChoice.lean) | Controlled Atlas Scale Choice |
| [ControlledCone.lean](../AbelianTargets/ControlledCone.lean) | Controlled radial extension of a boundary path family |
| [ControlledRowRealization.lean](../AbelianTargets/ControlledRowRealization.lean) | The padded-row realization is jointly Lipschitz as well as uniformly Lipschitz in path time. Its finite joint constant may depend on the row count. |
| [ControlledStages.lean](../AbelianTargets/ControlledStages.lean) | # Equal-slot concatenation of controlled deformation stages The stages act on one ambient metric space. Their actual inputs are the endpoints of the preceding… |
| [CoordinateBoxBounds.lean](../AbelianTargets/CoordinateBoxBounds.lean) | # Coordinate bounds on a rectangular cell imply a full metric bound |
| [CovariantCuts.lean](../AbelianTargets/CovariantCuts.lean) | Translation-covariant local cut selection |
| [CovariantOrbitCuts.lean](../AbelianTargets/CovariantOrbitCuts.lean) | # Repointing covariance of actual orbit cuts Changing the orbit origin by `t` changes every lattice coordinate by `-t`. The neighborhood, priorities, and actual… |
| [CubeBoundaryGluing.lean](../AbelianTargets/CubeBoundaryGluing.lean) | # Quantitative gluing on the boundary of a maximum-norm cube Facewise ambient estimates imply a global boundary estimate. Points on different nonopposite faces… |
| [CubeFaceCoordinateBounds.lean](../AbelianTargets/CubeFaceCoordinateBounds.lean) | Coordinate telescoping on a fixed face of a finite maximum-norm cube. |
| [CurveFamilyStages.lean](../AbelianTargets/CurveFamilyStages.lean) | Equal-slot concatenation of a family of curves with literal seams. |
| [CyclicTransfers.lean](../AbelianTargets/CyclicTransfers.lean) | Straight-middle transfers around an odd cycle |
| [DeterministicAtlasCovariance.lean](../AbelianTargets/DeterministicAtlasCovariance.lean) | The computed quantitative atlas builder preserves a covariant local extension rule. |
| [DeterministicAtlasLocality.lean](../AbelianTargets/DeterministicAtlasLocality.lean) | Deterministic Atlas Locality |
| [DeterministicQuantitativeAtlas.lean](../AbelianTargets/DeterministicQuantitativeAtlas.lean) | Deterministic Quantitative Atlas |
| [DigitBottomCombing.lean](../AbelianTargets/DigitBottomCombing.lean) | The actual digit combing of the entire finite bottom interval, with common slots. |
| [DigitBottomData.lean](../AbelianTargets/DigitBottomData.lean) | Actual compressed digit paths supply every moving-endpoint splice datum. |
| [DigitPathRealization.lean](../AbelianTargets/DigitPathRealization.lean) | # Literal directed realization of every bounded digital carry row |
| [Dimension.lean](../AbelianTargets/Dimension.lean) | Checked parts of the dimension argument |
| [DimensionEmbedding.lean](../AbelianTargets/DimensionEmbedding.lean) | Actual inclusion of successive target classes |
| [DirectedSourcePullback.lean](../AbelianTargets/DirectedSourcePullback.lean) | Directed twelve-tile sources on coordinate subgroup actions |
| [DirectionSaturation.lean](../AbelianTargets/DirectionSaturation.lean) | Equality in the signed-unit-vector bound |
| [DoubleCoverLifts.lean](../AbelianTargets/DoubleCoverLifts.lean) | Binary lifts of graph walks |
| [DoubleCoverSupport.lean](../AbelianTargets/DoubleCoverSupport.lean) | Realization of the graph double cover in the support complex |
| [EndpointCorrection.lean](../AbelianTargets/EndpointCorrection.lean) | Reserving the final path slot for a continuously moving endpoint. |
| [EquivariantCellCharts.lean](../AbelianTargets/EquivariantCellCharts.lean) | Actual relation-polygon charts with the literal horizontal parity action. |
| [EvenFiniteSources.lean](../AbelianTargets/EvenFiniteSources.lean) | Finite twelve-tile sources in even dimension |
| [Examples.lean](../AbelianTargets/Examples.lean) | A concrete odd involution in the complete graph on four vertices |
| [FacewiseConeExtension.lean](../AbelianTargets/FacewiseConeExtension.lean) | # Controlled cone filling from facewise boundary estimates This supplies the ambient boundary estimate needed by the existing cone formula from estimates on… |
| [FanStageTransitions.lean](../AbelianTargets/FanStageTransitions.lean) | Fan Stage Transitions |
| [FiniteAtlasDependencyPatterns.lean](../AbelianTargets/FiniteAtlasDependencyPatterns.lean) | A finite atlas pattern containing every boundary dependency of every cell through a fixed spatial point. The universe includes all subcells, even when their… |
| [FiniteCodes.lean](../AbelianTargets/FiniteCodes.lean) | Finite carrier reindexing and the strict-decrease consequence of the exact Proposition 7.7 statement. `Proposition77.lean` supplies the proved input. |
| [FiniteIntervalGluing.lean](../AbelianTargets/FiniteIntervalGluing.lean) | Finite families on neighboring unit intervals glue literally. Their path-time Lipschitz constant is independent of the number of intervals. |
| [FinitePatternFunctions.lean](../AbelianTargets/FinitePatternFunctions.lean) | A function determined by a locally constant finite pattern is itself locally constant and has finite range. This is the action-parameter step used after proving… |
| [FiniteRectangleIntersections.lean](../AbelianTargets/FiniteRectangleIntersections.lean) | Finite Rectangle Intersections |
| [FiniteSourceReferences.lean](../AbelianTargets/FiniteSourceReferences.lean) | Exact reference assumptions about the literal twelve-tile graphs |
| [FixedOrbitPriorityCuts.lean](../AbelianTargets/FixedOrbitPriorityCuts.lean) | # Actual fixed-index continuous priority cuts Inactive lattice indices are isolated; active indices use the literal finite marker-proximity neighborhood. This… |
| [FixedRowCharts.lean](../AbelianTargets/FixedRowCharts.lean) | Four-corner simplex certificates for contextual equal-slot replacements. |
| [FixedRowRealization.lean](../AbelianTargets/FixedRowRealization.lean) | A complete realization of padded combinatorial row moves by endpoint-fixed homotopies. The path-time constant depends only on the common slot budget. |
| [FixedSlotInterpolation.lean](../AbelianTargets/FixedSlotInterpolation.lean) | Fixed slots and the path-time estimate in Section 4 |
| [FixedSlotPadding.lean](../AbelianTargets/FixedSlotPadding.lean) | # Canonical common-slot padding of every bounded cellular row chain Each row is padded only at its endpoint. A triangle collapse becomes one equal-slot local… |
| [FreeShiftDensity.lean](../AbelianTargets/FreeShiftDensity.lean) | Finite patterns extend to free binary configurations |
| [FreeShiftTopology.lean](../AbelianTargets/FreeShiftTopology.lean) | The free shift is a zero-dimensional Polish action |
| [GeneralCarrierHeightRestriction.lean](../AbelianTargets/GeneralCarrierHeightRestriction.lean) | General Carrier Height Restriction |
| [IntegerCellGluing.lean](../AbelianTargets/IntegerCellGluing.lean) | # Global coordinate estimates from literal integer cells On a coordinate line, any integer rectangle containing the midpoint of a unit interval contains the… |
| [IntegerGridIntervals.lean](../AbelianTargets/IntegerGridIntervals.lean) | Finite consecutive integer cut levels and their closed-interval cover. |
| [IntegerIntervalGluing.lean](../AbelianTargets/IntegerIntervalGluing.lean) | Unit-interval gluing on an integer bounded coordinate interval. |
| [IntegerPrismChart.lean](../AbelianTargets/IntegerPrismChart.lean) | Literal active-coordinate prism charts for possibly degenerate atlas cells. The first coordinate retains its own interval parameter. |
| [IntegerPrismEstimates.lean](../AbelianTargets/IntegerPrismEstimates.lean) | Integer Prism Estimates |
| [IntegerPrismFillTranslation.lean](../AbelianTargets/IntegerPrismFillTranslation.lean) | Integer Prism Fill Translation |
| [IntegerPrismFilling.lean](../AbelianTargets/IntegerPrismFilling.lean) | The actual relative cone filling on arbitrary integer rectangular strata, including degenerate transverse coordinates. |
| [IntegerPrismTranslation.lean](../AbelianTargets/IntegerPrismTranslation.lean) | Integer Prism Translation |
| [IntegerRectangleProbes.lean](../AbelianTargets/IntegerRectangleProbes.lean) | # Integer probes for rectangular incidence germs The probes lie strictly between consecutive integer levels. A rectangle containing a probe contains its base… |
| [IntervalCarriers.lean](../AbelianTargets/IntervalCarriers.lean) | The literal finite interval-carrier skeleton |
| [JointCarrierRows.lean](../AbelianTargets/JointCarrierRows.lean) | Bounded carrier row certificates have actual jointly Lipschitz realizations. |
| [JointEndpointCorrection.lean](../AbelianTargets/JointEndpointCorrection.lean) | Finite joint Lipschitz constants for the reserved endpoint slot. |
| [JointHomotopyGluing.lean](../AbelianTargets/JointHomotopyGluing.lean) | # Joint Lipschitz bounds for concatenated homotopies |
| [LowerCarrierCollapse.lean](../AbelianTargets/LowerCarrierCollapse.lean) | Actual successive, simultaneous collapses of the lower polygon fans. |
| [LowerCarrierFaces.lean](../AbelianTargets/LowerCarrierFaces.lean) | The successive free diagonals of a presentation-polygon fan. |
| [MarkerAtlasCovariance.lean](../AbelianTargets/MarkerAtlasCovariance.lean) | Marker Atlas Covariance |
| [MarkerAtlasLocality.lean](../AbelianTargets/MarkerAtlasLocality.lean) | Finite local cut inputs determine actual retained tiles. In particular the retained status of every fixed parent/cell is locally constant. |
| [MarkerAtlasQuantitativeWidths.lean](../AbelianTargets/MarkerAtlasQuantitativeWidths.lean) | Marker Atlas Quantitative Widths |
| [MarkerAtlasSideBounds.lean](../AbelianTargets/MarkerAtlasSideBounds.lean) | Every nondegenerate side of an actual atlas cell is uniformly long. Endpoint owners lie within twelve scales of one incident parent, so the checked priority-cut… |
| [MarkerCutNeighborhoods.lean](../AbelianTargets/MarkerCutNeighborhoods.lean) | The actual marker neighborhood used by the priority-cut algorithm |
| [MarkerExistence.lean](../AbelianTargets/MarkerExistence.lean) | Existence of clopen separated covering orbit markers |
| [MarkerMap.lean](../AbelianTargets/MarkerMap.lean) | The continuous map into a finite marker graph |
| [MarkerPriorities.lean](../AbelianTargets/MarkerPriorities.lean) | Continuous marker priorities with a scale-independent color bound |
| [MarkerWindows.lean](../AbelianTargets/MarkerWindows.lean) | Finite separated marker windows |
| [MixedCompactSources.lean](../AbelianTargets/MixedCompactSources.lean) | Compact factor graphs for odd-dimensional actions |
| [MovingPause.lean](../AbelianTargets/MovingPause.lean) | Moving a spare constant slot through a path |
| [NaturalLogScaleBounds.lean](../AbelianTargets/NaturalLogScaleBounds.lean) | Converting the literal base-`m` carrier height into the analytic scale bound. |
| [Nonisolated.lean](../AbelianTargets/Nonisolated.lean) | Removing isolated target vertices |
| [OddCycleSources.lean](../AbelianTargets/OddCycleSources.lean) | Odd cycle sources |
| [OddFiniteSources.lean](../AbelianTargets/OddFiniteSources.lean) | Odd-dimensional finite source extraction |
| [OddProductObstruction.lean](../AbelianTargets/OddProductObstruction.lean) | The actual odd-cycle product obstruction (Lemma 7.6) |
| [OneHeightDeformation.lean](../AbelianTargets/OneHeightDeformation.lean) | Equal-slot assembly of the actual `m+2` collapses in one height layer. |
| [OneHeightRetraction.lean](../AbelianTargets/OneHeightRetraction.lean) | One Height Retraction |
| [OrbitMarkerCuts.lean](../AbelianTargets/OrbitMarkerCuts.lean) | Priority cuts in actual orbit coordinates |
| [PaddedRowCoordinates.lean](../AbelianTargets/PaddedRowCoordinates.lean) | Coordinate identities for canonical endpoint padding and one appended edge. |
| [ParallelCollapse.lean](../AbelianTargets/ParallelCollapse.lean) | Simultaneous free-edge collapses, with track speed independent of the number of triangles. These are actual finite compositions of PL maps. |
| [ParameterFaceBounds.lean](../AbelianTargets/ParameterFaceBounds.lean) | Affine chart coordinates have a bound depending only on face dimension. |
| [ParityCoordinates.lean](../AbelianTargets/ParityCoordinates.lean) | The unimodular parity coordinate change in Proposition 6.1 |
| [ParityFields.lean](../AbelianTargets/ParityFields.lean) | From controlled orbit maps to approximate parity fields |
| [ParitySwapGeometry.lean](../AbelianTargets/ParitySwapGeometry.lean) | Literal parity covariance of the support-space shore swap. |
| [ParityUnitSteps.lean](../AbelianTargets/ParityUnitSteps.lean) | Closing via unit steps after a uniformly continuous projection. A global Lipschitz estimate on the projected support map is unnecessary: the shear generator is a… |
| [PauseSliding.lean](../AbelianTargets/PauseSliding.lean) | # Equal-slot pause transport through an entire edge row |
| [PositiveGeometry.lean](../AbelianTargets/PositiveGeometry.lean) | Retained conditional geometric closing interfaces; the final unconditional proofs use the integer-lattice route. |
| [PositiveTheorems.lean](../AbelianTargets/PositiveTheorems.lean) | Unconditional Theorem 1.4 and Proposition 7.1 in every positive dimension, via approximate parity maps and probability rounding. |
| [PresentationComplex.lean](../AbelianTargets/PresentationComplex.lean) | The compact parity presentation quotient and its support map |
| [PresentationImage.lean](../AbelianTargets/PresentationImage.lean) | A compact metric parity model obtained from the actual presentation map |
| [PresentationPathRows.lean](../AbelianTargets/PresentationPathRows.lean) | # Edge-labelled sides of the actual presentation polygon |
| [PresentationSkeleton.lean](../AbelianTargets/PresentationSkeleton.lean) | The literal parity presentation one-skeleton |
| [PrimeParameters.lean](../AbelianTargets/PrimeParameters.lean) | Distinct odd prime parameters above any finite-source threshold |
| [PrimitiveDirections.lean](../AbelianTargets/PrimitiveDirections.lean) | Coprime odd cycle totals determine one signed direction |
| [PriorityCuts.lean](../AbelianTargets/PriorityCuts.lean) | The finite-priority parallel-cut algorithm |
| [PrismFillNaturality.lean](../AbelianTargets/PrismFillNaturality.lean) | Prism Fill Naturality |
| [Probability.lean](../AbelianTargets/Probability.lean) | Probability coordinates and exact graph rounding |
| [ProbabilityMap.lean](../AbelianTargets/ProbabilityMap.lean) | Pushforward of probability support pairs |
| [ProbabilityParameters.lean](../AbelianTargets/ProbabilityParameters.lean) | Affine unit-interval coordinates on literal probability faces. |
| [ProbabilityPushDirac.lean](../AbelianTargets/ProbabilityPushDirac.lean) | Probability Push Dirac |
| [ProbabilityPushGeometry.lean](../AbelianTargets/ProbabilityPushGeometry.lean) | Probability Push Geometry |
| [ProbabilityTwoVertices.lean](../AbelianTargets/ProbabilityTwoVertices.lean) | Exact barycentric coordinates on an edge, used to invert the literal height-zero carrier parametrization. |
| [ProductAxisRigidity.lean](../AbelianTargets/ProductAxisRigidity.lean) | Product Axis Rigidity |
| [ProductShift.lean](../AbelianTargets/ProductShift.lean) | The actual product of two-dimensional free shifts |
| [ProductSliceRigidity.lean](../AbelianTargets/ProductSliceRigidity.lean) | Direction independence across Cartesian factor slices |
| [ProjectedAtlasCovariance.lean](../AbelianTargets/ProjectedAtlasCovariance.lean) | Literal covariance of the global projected map follows from cell-map covariance. |
| [ProjectedAtlasEstimates.lean](../AbelianTargets/ProjectedAtlasEstimates.lean) | Coordinate estimates survive the actual carrier projection with its common modulus. |
| [ProjectedAtlasMaps.lean](../AbelianTargets/ProjectedAtlasMaps.lean) | Actual global support maps from compatible carrier maps on a rectangular atlas. |
| [Proposition77.lean](../AbelianTargets/Proposition77.lean) | Proposition 7.7 and strict decrease of the finite target classes |
| [QuantitativeProjectedUnits.lean](../AbelianTargets/QuantitativeProjectedUnits.lean) | Quantitative Projected Units |
| [RealizedBottomCombing.lean](../AbelianTargets/RealizedBottomCombing.lean) | The logarithmic-speed bottom combing takes values in the actual carrier. |
| [RectangleHalfGluing.lean](../AbelianTargets/RectangleHalfGluing.lean) | Literal seam gluing of two square families, including moving endpoints. |
| [RectangularAtlasBoundary.lean](../AbelianTargets/RectangularAtlasBoundary.lean) | Finite, strictly lower-rank boundary refinements of the actual point cells. |
| [RectangularBoundaryStrata.lean](../AbelianTargets/RectangularBoundaryStrata.lean) | # Actual boundary strata of a bounded integer rectangular tiling The cell at a point is the finite intersection of the minimal faces of all incident full tiles.… |
| [RectangularCells.lean](../AbelianTargets/RectangularCells.lean) | # Integer rectangular cells and their point faces These are literal closed rectangles, including degenerate coordinates. The relative interior keeps a degenerate… |
| [RectangularCone.lean](../AbelianTargets/RectangularCone.lean) | Physical coordinate estimates for the rectangular cone |
| [RectangularFaceRefinement.lean](../AbelianTargets/RectangularFaceRefinement.lean) | Rectangular Face Refinement |
| [RectangularLocalFiniteness.lean](../AbelianTargets/RectangularLocalFiniteness.lean) | # Local finiteness of bounded integer rectangles Integer endpoints and a uniform coordinate diameter bound alone give a locally finite family of distinct… |
| [RectangularTranslation.lean](../AbelianTargets/RectangularTranslation.lean) | # Literal translation covariance of integer boundary strata |
| [ReducedWalks.lean](../AbelianTargets/ReducedWalks.lean) | Reduced graph-walk homotopy and parity |
| [References.lean](../AbelianTargets/References.lean) | Explicit assumptions from the cited literature |
| [RegularAnisotropicAtlas.lean](../AbelianTargets/RegularAnisotropicAtlas.lean) | An actual regular anisotropic atlas package. Its fields are marker and cut data; all tiling, stratum, boundary, covariance and locality properties are theorems… |
| [RelativeContractionNaturality.lean](../AbelianTargets/RelativeContractionNaturality.lean) | The literal relative homotopy and cone filling commute with isometric transport. These equalities concern the actual formulas, including all four path… |
| [RelativePathBounds.lean](../AbelianTargets/RelativePathBounds.lean) | Relative Path Bounds |
| [RelativePathComparison.lean](../AbelianTargets/RelativePathComparison.lean) | Relative Path Comparison |
| [RelativePathContraction.lean](../AbelianTargets/RelativePathContraction.lean) | Relative path contraction |
| [RetainedMarkerTiles.lean](../AbelianTargets/RetainedMarkerTiles.lean) | # Actual retained marker-box subdivisions Each marker box is subdivided at the finite cut levels of all markers within six scales. Only the elementary boxes… |
| [RetainedTilesCovariance.lean](../AbelianTargets/RetainedTilesCovariance.lean) | Retained Tiles Covariance |
| [Rounding.lean](../AbelianTargets/Rounding.lean) | Continuous finite-range rounding |
| [RowSlotScaling.lean](../AbelianTargets/RowSlotScaling.lean) | Literal equality of normalized row paths after reserving a final slot. |
| [RowValidity.lean](../AbelianTargets/RowValidity.lean) | # Valid edge rows and preservation under the actual cellular moves |
| [SafeDigitalCarries.lean](../AbelianTargets/SafeDigitalCarries.lean) | Carry certificates retaining every vertex of the literal carrier |
| [SegmentedOddPath.lean](../AbelianTargets/SegmentedOddPath.lean) | A literal alternating odd path and its finite dyadic edge subdivision. |
| [ShiftTransitivity.lean](../AbelianTargets/ShiftTransitivity.lean) | Transitivity of a common nonzero translation on active free-shift factors |
| [SimplexDimensionBounds.lean](../AbelianTargets/SimplexDimensionBounds.lean) | # Common-face bounds depending on simplex dimension The estimates depend on the number of vertices in a supporting simplex, rather than on the total number of… |
| [SimplexMetricGluing.lean](../AbelianTargets/SimplexMetricGluing.lean) | # A common-face estimate for finite probability simplices Two nearby probability points have a normalized coordinatewise minimum supported in both of their… |
| [SimplicialChartGluing.lean](../AbelianTargets/SimplicialChartGluing.lean) | # Concrete continuous maps from finite probability-simplex carriers Continuous face charts agreeing on their literal intersections produce an actual global… |
| [SimplicialSupport.lean](../AbelianTargets/SimplicialSupport.lean) | Simplicial Support |
| [SmallStepProjectedOrbitMaps.lean](../AbelianTargets/SmallStepProjectedOrbitMaps.lean) | Continuous finite-range origin maps, parity covariance, and small integer unit edges for every required source action. |
| [Statements.lean](../AbelianTargets/Statements.lean) | Exact theorem types and retained construction interfaces; the positive proof terms are in PositiveTheorems.lean. |
| [SupportCellCharts.lean](../AbelianTargets/SupportCellCharts.lean) | A single continuous chart on each complete literal relation polygon. |
| [SupportCellRestrictions.lean](../AbelianTargets/SupportCellRestrictions.lean) | Support Cell Restrictions |
| [SupportChartNaturality.lean](../AbelianTargets/SupportChartNaturality.lean) | Support Chart Naturality |
| [SupportGeometry.lean](../AbelianTargets/SupportGeometry.lean) | Concrete probability support geometry |
| [SupportLipschitz.lean](../AbelianTargets/SupportLipschitz.lean) | Quantitative affine homotopies in support carriers |
| [SupportModel.lean](../AbelianTargets/SupportModel.lean) | The analytic implication in Section 6 |
| [SupportPathClasses.lean](../AbelianTargets/SupportPathClasses.lean) | Path-class algebra of the support complex |
| [SupportRelationCharts.lean](../AbelianTargets/SupportRelationCharts.lean) | Explicit barycentric charts filling the odd Baumslag--Solitar relation. |
| [SupportSkeletonMap.lean](../AbelianTargets/SupportSkeletonMap.lean) | A total support-space map whose restrictions to skeleton edges are literal paths. |
| [SupportTorsion.lean](../AbelianTargets/SupportTorsion.lean) | Odd torsion walks and support-space paths |
| [SupportWitness.lean](../AbelianTargets/SupportWitness.lean) | Support-space data from an arbitrary odd torsion target |
| [ThreeColoring.lean](../AbelianTargets/ThreeColoring.lean) | Three colors for a nonzero displacement |
| [TopologicalWalks.lean](../AbelianTargets/TopologicalWalks.lean) | Passing the reduced walk presentation to topological path classes |
| [Torus.lean](../AbelianTargets/Torus.lean) | Coprime torus collapse |
| [TorusRigidity.lean](../AbelianTargets/TorusRigidity.lean) | Torus Rigidity |
| [TriangleChartIntersections.lean](../AbelianTargets/TriangleChartIntersections.lean) | Non-skeleton diagonals belong to one literal relation polygon. |
| [TriangleCollapse.lean](../AbelianTargets/TriangleCollapse.lean) | # An explicit simplicial free-edge collapse The two coordinates on a free edge lose their common minimum, and the opposite vertex receives twice that amount.… |
| [TriangleRowMoves.lean](../AbelianTargets/TriangleRowMoves.lean) | # Bounded elementary row moves and polygon fan contraction |
| [TwelveTileAxisCycles.lean](../AbelianTargets/TwelveTileAxisCycles.lean) | Twelve Tile Axis Cycles |
| [TwelveTileDirections.lean](../AbelianTargets/TwelveTileDirections.lean) | Twelve Tile Directions |
| [TwelveTileFields.lean](../AbelianTargets/TwelveTileFields.lean) | Twelve Tile Fields |
| [TwelveTileTorus.lean](../AbelianTargets/TwelveTileTorus.lean) | Twelve Tile Torus |
| [TwelveTileUniform.lean](../AbelianTargets/TwelveTileUniform.lean) | Twelve Tile Uniform |
| [TwelveTiles.lean](../AbelianTargets/TwelveTiles.lean) | The width-one twelve-tile graph |
| [UniformAffineSupportCharts.lean](../AbelianTargets/UniformAffineSupportCharts.lean) | A common modulus for all torsion charts, independent of the vertex set. |
| [UniformCarrierContraction.lean](../AbelianTargets/UniformCarrierContraction.lean) | Uniform Carrier Contraction |
| [UniformCarrierSupportProjection.lean](../AbelianTargets/UniformCarrierSupportProjection.lean) | One modulus for every finite interval-carrier projection. |
| [UniformParityProjection.lean](../AbelianTargets/UniformParityProjection.lean) | # Uniform-continuity closing for parity projections Approximate equivariance is preserved by a uniformly continuous equivariant projection. The family version… |
| [UniformSimplexGluing.lean](../AbelianTargets/UniformSimplexGluing.lean) | # A uniform modulus on families of bounded-dimensional simplex unions The vertex sets and number of simplices may grow. A common simplex size bound and a common… |
| [UpperCarrierCollapse.lean](../AbelianTargets/UpperCarrierCollapse.lean) | A simultaneous, continuous, speed-one collapse of all top horizontal edges in the literal finite interval carrier. |
| [UpperCarrierFaces.lean](../AbelianTargets/UpperCarrierFaces.lean) | The actual top edges of the finite carrier are free faces of their presentation-polygon fans. This is a combinatorial statement about the literal integer-height… |
| [VariableRowFamilies.lean](../AbelianTargets/VariableRowFamilies.lean) | Fixed-slot row interpolation with a moving terminal vertex. |
| [VerticalCarrierCollapse.lean](../AbelianTargets/VerticalCarrierCollapse.lean) | The final speed-one vertical collapse of a literal carrier height layer. |
| [VerticalCarrierFaces.lean](../AbelianTargets/VerticalCarrierFaces.lean) | Terminal polygon fans consist of lower faces and vertical edges. |
| [WordPathHelpers.lean](../AbelianTargets/WordPathHelpers.lean) | Determinism and exact vertex rows of directed carrier word paths |
