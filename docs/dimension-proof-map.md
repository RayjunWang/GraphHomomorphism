# Proposition 7.7: completed proof

`AbelianTargets.proposition7_7` proves the exact `Proposition77Statement`
for the literal marker-window graph in every positive dimension and at
every scale at least four. The strict-decrease corollary is also proved.
Source: [arXiv:2609.39824v1](https://arxiv.org/html/2609.39824v1), Section 7.2.

The proof is complete relative to three named reference axioms.
None of the target paper's lemmas is assumed.

| Dependency | Checked implementation |
| --- | --- |
| Lemma 7.3 | `MarkerWindows`, `MarkerMap`, `ClopenMarkers`, `MarkerExistence`: actual finite patterns and overlap graph, clopen covering markers, continuous window map, and all direction laws. |
| Literal sources | `TwelveTiles`: four based boundary cycles, twelve grids with exact boundary words, private interiors, and positive horizontal/vertical steps. |
| Direction rigidity | `TwelveTileFields`, `PrimitiveDirections`, `TwelveTileUniform`, `TwelveTileDirections`: square-field sums, long-tile relations, coprime arithmetic, and saturation. |
| Distinct axes | `Torus`, `TorusRigidity`, `TwelveTileTorus`, `TwelveTileAxisCycles`, `ProductAxisRigidity`: actual coprime tori and straight-middle uniqueness, within and between factors. |
| Context independence | `CartesianConstancy`, `ProductSliceRigidity`, `AdjacentSliceDirections`: invariance under other-factor updates and agreement between adjacent slices. |
| Lemma 7.4 | `TwelveTiles.lemma7_4` and `lemma7_4_dimension_bound`: globally uniform directions, injective axes, and the actual dimension bound. |
| Compact models | `ThreeColoring`, `CompactFreeModel`, `CompactFactorization`: compact free displacement-coloring models, equivariant maps, finite clopen factor partitions, and atom graphs. |
| Lemma 7.5 | `EvenFiniteSources`, `MixedCompactSources`, `OddCycleSources`, `OddFiniteSources`: actual Cartesian sources, including a literal odd cycle for odd dimension. |
| Parameters | `PrimeParameters`: arbitrarily large distinct odd primes with all coprimality conditions. |
| Transitivity | `FreeShiftDensity`, `ShiftTransitivity`, `ProductShift`: finite-pattern realization by free shifts, common orbit bridges, and transitivity on active product factors. |
| Lemma 7.6 | `CyclicTransfers`, `OddProductObstruction`: uniform cycle-layer matrices, constant crossing directions, signed transfers, odd nonzero translation, and the proper-coloring contradiction. |
| Final proof | `Proposition77`: parity split and parameter choice above the finite-source thresholds. |
| Strict decrease | `DimensionEmbedding`, `FiniteCodes`, `Proposition77`: actual class inclusion, finite-carrier reindexing, and separating marker witnesses. |

The odd-product proof uses independent two-dimensional free-shift factors.
Separate subgroup maps on a single larger shift need not stay invariant
under the other coordinates, so their product is not used.

The extracted odd-cycle length is odd and at least three, and is not
required to be prime. This is the source implication needed for Proposition
7.7; it is weaker than the paper's prime-length formulation of Lemma 7.5.

The completed proposition depends on:

- `References.bernshteyn_theorem_1_12`;
- `References.gjks_direction_preserving_twelve_tiles`;
- `References.gjks_eventual_twelve_tile_source`.

See [reference-axioms.md](reference-axioms.md) for their exact attribution.
The kernel audit prints the dependency list of the final theorem.
