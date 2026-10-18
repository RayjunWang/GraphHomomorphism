# Final positive-theorem source review

Date: 2026-10-18.

Reviewer: a Codex sub-agent that began with fresh context and subsequently performed this read-only source audit. The reviewer received coordination updates and inspected the actual Lean sources and source paper. This is a substantive source review, not a blind read-back. No different-model independence is claimed; the exact model deployment identifier was not exposed to the reviewer. Saving this report is the reviewer's only project edit in this audit.

## Scope and verification boundary

The four new modules reviewed were `AtlasScaleParameters.lean`, `CanonicalActionCovariance.lean`, `SmallStepProjectedOrbitMaps.lean`, and `PositiveTheorems.lean`. The reviewer also inspected the existing statement, action, reduced-walk, projection-modulus, contraction-family, and origin-regularity interfaces used by their closing chain.

The reviewer independently executed one read-only Lean inspection importing `AbelianTargets.Statements`, with `pp.universes` and `pp.explicit` enabled, and printed `UniversalTarget`, `Proposition71Statement`, and `Theorem14Statement`. The command exited successfully. The printed definitions assign the source space to `Type u` and target vertices to the independent universe `Type v`; both statement definitions expand to `UniversalTarget.{u, v}`.

The root agent reports that the full project build passed with 3,255 jobs, the final kernel audit passed over 5,601 declarations, and both final positive theorems have exactly the axiom dependencies `propext`, `Classical.choice`, and `Quot.sound`. These full-build, kernel-audit, and final-theorem axiom results were reported by the root agent and were not independently rerun by this reviewer.

## Exact target comparison

The reviewer directly consulted [arXiv:2609.39824v1](https://arxiv.org/html/2609.39824v1), Theorem 1.4, Proposition 7.1, and Sections 2.1–2.2. The final theorem types use the existing `Theorem14Statement` and `Proposition71Statement` definitions without strengthening their hypotheses or weakening their conclusions. They quantify over every natural dimension $d\ge1$ and every free continuous $\mathbb Z^d$-action on a zero-dimensional Polish space, and conclude a continuous homomorphism to the finite discrete simple graph $H$.

The order-two hypothesis is an odd closed graph walk whose square is reduced-homotopic to the empty walk. The torsion hypothesis is an odd closed walk with a positive trivializing exponent. The existing reduced-walk relation permits spur cancellation, all closed four-walk relations, equivalence closure, and concatenation. The checked `hasOddInvolution_iff` and `hasOddTorsion_iff_isOfFinOrder` identify these hypotheses with the corresponding assertions in the reduced fundamental group.

Neither final theorem in `PositiveTheorems.lean` has a geometric-construction parameter. Proposition 7.1 obtains its support torsion data internally from its stated hypothesis. Theorem 1.4 uses the checked implication from odd square-triviality to odd torsion.

## Substantive findings

- **Scale order and normalized contractions.** In `AtlasScaleParameters.lean`, `exists_smallAtlasParameters` chooses $K(a)=\log_m(6(a+2))$ and a joint bound $J(a)$ with one normalized contraction family $H(a)$ for all positive widths at most $6a$, before choosing the transverse scale $b$. Its transverse rate bound depends on $a$, $K(a)$, and $J(a)$, with no dependence on $b$. The logarithmic height dominates the required height for widths at most $6a$. Successive scale choice makes the sum of longitudinal and transverse bounds small; nonnegativity then gives each required coordinate bound. The resulting scales are positive and at least $32\cdot61^d$.

- **Covariance and the inverse shear.** In `CanonicalActionCovariance.lean`, the same normalized family is used on translated cells and pointed atlases. The forward repointing identity has the orientation required by closing. The `ParitySheared` action sends a new displacement $g$ to the original displacement $S^{-1}g$, while `ofOriginal_vadd` sends an original displacement to $Sg$. Its topology is inherited, the continuous action instance uses the discrete lattice, and freeness follows from the injectivity of $S^{-1}$. Every original positive generator has distinguished shear coordinate $1$ and becomes either one coordinate unit vector or the sum of two such vectors.

- **Regularity and small steps.** In `SmallStepProjectedOrbitMaps.lean`, the projection modulus is obtained before scale selection and is uniform in carrier height and interval endpoints. The atlas and normalized contraction family are fixed before evaluation at a point of the action space. Origin continuity and finite range therefore use the same data as covariance and coordinate estimates. The factor $(2\cdot30+1)^d$ matches $61^d$ in the scale package. The integer-step projection estimate is reversed by symmetry of distance to match the unit-step field.

- **Unconditional closing.** In `PositiveTheorems.lean`, the original-action map is the small-step map on `ParitySheared` composed with `ofOriginal`. Its origin remains continuous with finite range. Covariance becomes the required shore swap because the distinguished coordinate of $S(e_i)$ is $1$. The lattice closing argument compares through at most two positive coordinate steps with half the requested error. `SupportPair.hasContinuousHom_of_approximateSwap` then applies the existing probability rounding directly. The inspected closing route introduces no reference-result axiom or additional construction premise.

## Edge cases and assessment

Dimension one is included; dimension zero is excluded by the target hypotheses. Empty action spaces are permitted. Empty target vertex types cannot satisfy the odd-walk hypothesis, and the support torsion data supply target nonemptiness internally. Disconnected targets and repeated walk vertices or edges are permitted. Width-zero carrier cells do not require a normalized contraction: the provider is requested only under a strictly positive distinguished width. Preliminary families at first scale zero may be vacuous, while the finally selected scales are strictly positive. No connectedness, compactness, nonemptiness of the action space, injectivity, or surjectivity is added to the final target statements.

No source-level statement, quantifier-order, covariance-orientation, or unit-step-orientation issue was found in the reviewed modules. This assessment covers the inspected assembly and interfaces; the reported complete compilation and transitive axiom checks belong to the root agent's verification run.
