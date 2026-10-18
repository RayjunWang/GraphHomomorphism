import AbelianTargets.Rounding
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# The analytic implication in Section 6

This file checks composition with an equivariant support model, choice of
a uniform error on a compact source, and exact graph rounding.
The actual presentation complex is constructed in separate modules;
existence of its approximate parity maps remains an explicit geometric input.
-/

namespace AbelianTargets

/-- The assertion of Proposition 6.1, expressed without committing to a
particular auxiliary compact metric complex. -/
def ApproximateParityMaps {d : ℕ} (X Y : Type*)
    [TopologicalSpace X] [AddAction (Lattice d) X] [MetricSpace Y]
    (τ : Y → Y) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ f : X → Y,
    Continuous f ∧ (Set.range f).Finite ∧
      ∀ (x : X) (i : Fin d), dist (f (unitVector i +ᵥ x)) (τ (f x)) < ε

/-- Coordinates of the map into `𝒟(H)` used in Lemma 6.2. The first-shore
swap identity is the part of equivariance needed in the rounding argument. -/
structure SupportModel {Y V : Type*} [TopologicalSpace Y] [Fintype V]
    (H : SimpleGraph V) (τ : Y → Y) where
  p : Y → Probability V
  q : Y → Probability V
  continuous_p : Continuous p
  compatible : ∀ y, Compatible H (p y) (q y)
  first_swap : ∀ y, p (τ y) = q y

/-- The uniform-continuity step followed by probability-field construction.
Existence of both inputs is an explicit hypothesis, not a proved claim about
the presentation complex in the paper. -/
theorem probabilityField_of_approximateParityMaps
    {d : ℕ} {X Y V : Type*} [TopologicalSpace X]
    [AddAction (Lattice d) X] [MetricSpace Y] [CompactSpace Y]
    [Fintype V] [Nonempty V] {H : SimpleGraph V} {τ : Y → Y}
    (model : SupportModel H τ)
    (approx : ApproximateParityMaps (d := d) X Y τ) :
    Nonempty (ProbabilityField (d := d) (X := X) H) := by
  have hcard : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty V)
  have hε : 0 < 1 / (2 * (Fintype.card V : ℝ)) := by positivity
  have huc : UniformContinuous (fun y => (model.p y).mass) :=
    CompactSpace.uniformContinuous_of_continuous
      (Probability.continuous_mass.comp model.continuous_p)
  obtain ⟨δ, hδ, hbound⟩ :=
    Metric.uniformContinuous_iff.mp huc (1 / (2 * (Fintype.card V : ℝ))) hε
  obtain ⟨f, hf, hfinite, he⟩ := approx δ hδ
  refine ⟨{
    p := fun x => model.p (f x)
    q := fun x => model.q (f x)
    continuous_p := model.continuous_p.comp hf
    finite_range_p := ?_
    compatible := fun x => model.compatible (f x)
    close := ?_ }⟩
  · apply (hfinite.image model.p).subset
    rintro z ⟨x, rfl⟩
    exact ⟨f x, ⟨x, rfl⟩, rfl⟩
  · intro x i v
    have hclose := (dist_pi_lt_iff hε).mp (hbound (he x i)) v
    simpa only [Real.dist_eq, model.first_swap] using hclose

/-- Complete formalization of the closing argument in Section 6, conditional
on the two independent geometric inputs. -/
theorem hasContinuousHom_of_supportModel
    {d : ℕ} {X Y V : Type*} [TopologicalSpace X]
    [AddAction (Lattice d) X] [MetricSpace Y] [CompactSpace Y]
    [Fintype V] [Nonempty V] [TopologicalSpace V]
    {H : SimpleGraph V} {τ : Y → Y}
    (model : SupportModel H τ)
    (approx : ApproximateParityMaps (d := d) X Y τ) :
    HasContinuousHom (d := d) (X := X) H := by
  obtain ⟨field⟩ := probabilityField_of_approximateParityMaps model approx
  exact hasContinuousHom_of_probabilityField field

end AbelianTargets
