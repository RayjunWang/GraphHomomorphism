import AbelianTargets.TwelveTiles
import AbelianTargets.Actions

/-!
# Exact reference assumptions about the literal twelve-tile graphs

Both assumptions are specializations of the cited GJKS monograph,
arXiv:1803.03872 (author version, 126 pages). They are not assumptions
of any higher-dimensional result of arXiv:2609.39824.

* Theorem 2.5.1, printed p. 54, gives a continuous direction-preserving
  `ℤ²`-homomorphism from the free shift to `Γ₁,p,q` for `1<p,q` coprime.
* Corollary 3.3.1, printed pp. 81–82, equivalence (1)→(4), gives graph
  homomorphisms `Γ₁,p,q→J` for every sufficiently large pair `p,q`.

We restrict to `p,q≥5`, matching the concrete graph representation.
Primary source: https://arxiv.org/pdf/1803.03872

The last axiom is the finite-pattern specialization of Bernshteyn,
Theorem 1.12, arXiv:2102.08797v2. The two forbidden-pattern constraints
require respectively a positive horizontal and vertical tile step on
each positive standard generator edge. The hypothesis explicitly supplies
the free-shift solution, so the GJKS dependence remains separate.
Primary source: https://arxiv.org/html/2102.08797v2#S1.Thmtheorem1.12
-/

namespace AbelianTargets.References

open TwelveTiles

/-- GJKS [4], Theorem 2.5.1, width one, with the two coordinate directions
specified by the actual positive tile-step relations. -/
axiom gjks_direction_preserving_twelve_tiles
    (p q : ℕ) (hp : 5 ≤ p) (hq : 5 ≤ q) (hcop : p.Coprime q) :
    ∃ θ : FreeShift 2 → Vertex p q, Continuous θ ∧
      (∀ x, HorizontalStep hp hq (θ x) (θ (unitVector (0 : Fin 2) +ᵥ x))) ∧
      (∀ x, VerticalStep hp hq (θ x) (θ (unitVector (1 : Fin 2) +ᵥ x)))

/-- GJKS [4], Corollary 3.3.1, (1)→(4), specialized to width one and
finite discrete targets. Coprimality only weakens its conclusion. -/
axiom gjks_eventual_twelve_tile_source
    {V : Type*} [TopologicalSpace V] [Fintype V] [DiscreteTopology V]
    (J : SimpleGraph V) (hJ : InClass 2 J) :
    ∃ N : ℕ, ∀ (p q : ℕ) (hp : 5 ≤ p) (hq : 5 ≤ q),
      N ≤ p → N ≤ q → p.Coprime q → Nonempty (graph p q hp hq →g J)

/-- Bernshteyn [2], Theorem 1.12, specialized to the finite forbidden
patterns expressing the two positive directed twelve-tile constraints. -/
axiom bernshteyn_directed_twelve_tiles_universality
    (p q : ℕ) (hp : 5 ≤ p) (hq : 5 ≤ q)
    (hsource : ∃ θ : FreeShift 2 → Vertex p q, Continuous θ ∧
      (∀ x, HorizontalStep hp hq (θ x) (θ (unitVector (0 : Fin 2) +ᵥ x))) ∧
      (∀ x, VerticalStep hp hq (θ x) (θ (unitVector (1 : Fin 2) +ᵥ x))))
    (X : Type*) [TopologicalSpace X] [PolishSpace X]
    [AddAction (Lattice 2) X] [ContinuousVAdd (Lattice 2) X]
    (zeroDim : ZeroDimensional X) (free : IsFree (G := Lattice 2) (X := X)) :
    ∃ θ : X → Vertex p q, Continuous θ ∧
      (∀ x, HorizontalStep hp hq (θ x) (θ (unitVector (0 : Fin 2) +ᵥ x))) ∧
      (∀ x, VerticalStep hp hq (θ x) (θ (unitVector (1 : Fin 2) +ᵥ x)))

end AbelianTargets.References
