# Verification scope

The three requested theorem types are proved and kernel-checked without additional
construction hypotheses:

| Statement | Proof |
| --- | --- |
| `Theorem14Statement.{u} H` | `AbelianTargets.theorem1_4 H` |
| `Proposition71Statement.{u} H` | `AbelianTargets.proposition7_1 H` |
| `Proposition77Statement` | `AbelianTargets.proposition7_7` |

The two positive statements retain their exact graph hypotheses and quantify
over every `d ≥ 1`, every free continuous `ℤ^d` action on a zero-dimensional
Polish space, and source and target universes independently. Proposition 7.7
uses the literal finite marker-window graph for every `d ≥ 1` and `L ≥ 4`.
The strict-decrease corollary uses actual finite graph codes.

## Kernel dependencies

`AxiomAudit.lean` inspects every declaration in the `AbelianTargets`
namespace, including intermediate and private declarations. It permits
`propext`, `Classical.choice`, `Quot.sound`, and the five individually named
reference axioms in [reference-axioms.md](reference-axioms.md).
The final positive proofs depend only on the three standard Lean axioms.
The full library build and kernel audit passed; both theorem dependencies
were also checked individually. Proposition 7.7 retains
its three previously permitted reference dependencies. No target-paper
result or archive claim is an axiom.

The source scan rejects `sorry`, `admit`, `unsafe`, and `native_decide`,
rejects axiom declarations outside the exact allowlist, and requires every
library module to appear in the umbrella import. A clean audit alone would
not discharge an unproved construction hypothesis: the final theorem types
and direct construction in `PositiveTheorems.lean` supply that distinction.

## Construction and retained interfaces

The proof constructs the actual marker atlas, controlled finite-carrier
contractions, uniform support projection, compatible quantitative rank
extension, and finite continuous origin maps. The final four modules add
action covariance, inverse-shear transport, successive scale choices, and
the quantified small-step maps needed by probability rounding.

The older conditional interfaces in `PositiveGeometry.lean` and
`ParityFields.lean` remain in the library. The unconditional positive proofs
use the integer-lattice route and do not assume those interfaces.
The general result supersedes the earlier dimension-at-most-two proof
scope without removing those separate reference-based proofs.

## Reproducibility

Lean and mathlib are pinned by `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`. The source archive excludes dependency caches and
machine-specific directory links. The
[saved verification report](verification.json) contains the exact checked
source/configuration hashes, build and audit status, and completion scope.

The GitHub workflow builds and audits after upload. No repository publication
or remote CI success is asserted by the local verification.
