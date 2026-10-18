# Lean formalization of arXiv:2609.39824

The requested statements are proved and kernel-checked in every positive dimension:
**Theorem 1.4**, **Proposition 7.1**, and **Proposition 7.7**.
The positive proofs have no additional geometric-construction hypothesis.

Source: Ruijun Wang, [*Continuous graph homomorphisms of higher dimensional
abelian group actions*, arXiv:2609.39824v1](https://arxiv.org/abs/2609.39824v1),
30 September 2026. Lean **4.30.0**; mathlib revision
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

## Requested results

| Result | Entry point and scope |
| --- | --- |
| Theorem 1.4 | `AbelianTargets.theorem1_4` in [PositiveTheorems.lean](AbelianTargets/PositiveTheorems.lean): every `d ≥ 1`, with the exact odd square-trivial reduced-walk hypothesis. |
| Proposition 7.1 | `AbelianTargets.proposition7_1` in [PositiveTheorems.lean](AbelianTargets/PositiveTheorems.lean): every `d ≥ 1`, with the exact odd finite-torsion reduced-walk hypothesis. |
| Proposition 7.7 | `AbelianTargets.proposition7_7` in [Proposition77.lean](AbelianTargets/Proposition77.lean): the literal marker graph, every `d ≥ 1` and `L ≥ 4`, relative to the permitted reference results. |
| Strict decrease of the finite target classes | `finiteGraphClasses_strictDecrease`, using actual finite graph codes. |

The positive statements quantify over every free continuous lattice action
on a zero-dimensional Polish space and every finite discrete target satisfying
the corresponding graph hypothesis. They construct the continuous graph
homomorphism directly. The earlier proofs for dimensions one and two remain
available as separate reference-based deductions.

The final construction uses four modules:

- [CanonicalActionCovariance.lean](AbelianTargets/CanonicalActionCovariance.lean): actual marker-atlas repointing, projected covariance, integer lattice edges, and the inverse-sheared action.
- [AtlasScaleParameters.lean](AbelianTargets/AtlasScaleParameters.lean): actual small-rate scale parameters and one common normalized contraction family.
- [SmallStepProjectedOrbitMaps.lean](AbelianTargets/SmallStepProjectedOrbitMaps.lean): continuous finite-range origin maps, exact parity covariance, and small integer unit steps for every source action.
- [PositiveTheorems.lean](AbelianTargets/PositiveTheorems.lean): approximate parity maps on the original action, probability rounding, and both unconditional positive theorems.

The carrier, support projection, rectangular marker atlas, and quantitative
rank recursion are actual Lean constructions. The closing argument needs
only integer lattice edges: after the parity shear, each original generator
uses one or two such edges. It does not require a global Lipschitz bound for
the support projection.

See the [positive proof map](docs/positive-proof-map.md),
[dimension proof map](docs/dimension-proof-map.md),
[verification scope](docs/verification-scope.md), and
[module index](docs/module-index.md). The former
[remaining-work page](docs/remaining-positive-work.md) records how the final
obligations were discharged. [Archive continuation](docs/archive-continuation.md)
separates the historical partial results from the completed final assembly.

## Reference assumptions and trust

The user authorized results from reference papers as axioms. Five specific
specializations remain in `References.lean` and `FiniteSourceReferences.lean`;
see [reference-axioms.md](docs/reference-axioms.md). Proposition 7.7 uses
Bernshteyn Theorem 1.12, GJKS Theorem 2.5.1, and GJKS Corollary 3.3.1.
The kernel dependencies of both general positive proofs are exactly
`propext`, `Classical.choice`, and `Quot.sound`. They use no named reference axiom.

No result from the target paper or the archived research notes is an axiom.
The audit checks every project declaration against an exact allowlist, and
the source scan rejects `sorry`, `admit`, `unsafe`, and `native_decide`.
The [saved verification report](docs/verification.json) records the checked
source hashes and the exact theorem scope.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build
python3 scripts/verify.py --skip-build
```

Use `python` instead of `python3` on Windows. Running
`python3 scripts/verify.py` also builds the library. The initial dependency
fetch and cache download need internet access.

The [GitHub Actions workflow](.github/workflows/lean.yml) builds and audits
the project after upload. No GitHub-hosted run is asserted.

## Upload to GitHub

Extract the archive and upload this directory's contents, including
`.github`, to an empty repository. Alternatively:

```sh
git init
git add .
git commit -m "Formalize Theorem 1.4 and Propositions 7.1 and 7.7"
git branch -M main
git remote add origin YOUR_REPOSITORY_URL
git push -u origin main
```

The source archive excludes build caches and machine-specific directory links.
