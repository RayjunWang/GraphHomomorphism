import AbelianTargets.SupportModel

/-!
# Uniform-continuity closing for parity projections

Approximate equivariance is preserved by a uniformly continuous equivariant
projection. The family version permits a different finite carrier at each
scale, provided their projections share a uniform modulus.
-/

namespace AbelianTargets

noncomputable section

theorem approximateParityMaps_postcompose {d : ℕ} {X Y Z : Type*}
    [TopologicalSpace X] [AddAction (Lattice d) X] [MetricSpace Y] [MetricSpace Z]
    {τ : Y → Y} {σ : Z → Z} (η : Y → Z) (hη : UniformContinuous η)
    (hequiv : ∀ y, η (τ y)=σ (η y)) (approx : ApproximateParityMaps (d := d) X Y τ) :
    ApproximateParityMaps (d := d) X Z σ := by
  intro ε hε
  obtain ⟨δ,hδ,hbound⟩ := Metric.uniformContinuous_iff.mp hη ε hε
  obtain ⟨f,hf,hfin,hclose⟩ := approx δ hδ
  refine ⟨η ∘ f,hη.continuous.comp hf,?_,?_⟩
  · apply (hfin.image η).subset
    rintro z ⟨x,rfl⟩
    exact ⟨f x,⟨x,rfl⟩,rfl⟩
  · intro x i
    simpa only [Function.comp_def,hequiv] using hbound (hclose x i)

theorem approximateParityMaps_of_uniform_carrier_family {d : ℕ} {X I Z : Type*}
    [TopologicalSpace X] [AddAction (Lattice d) X] [MetricSpace Z]
    (Y : I → Type*) [∀ i, MetricSpace (Y i)] (τ : ∀ i, Y i → Y i)
    (σ : Z → Z) (η : ∀ i, Y i → Z)
    (hmodulus : ∀ ε : ℝ, 0<ε → ∃ δ : ℝ, 0<δ ∧
      ∀ i (p q : Y i), dist p q < δ → dist (η i p) (η i q) < ε)
    (hequiv : ∀ i y, η i (τ i y)=σ (η i y))
    (source : ∀ δ : ℝ, 0<δ → ∃ i : I, ∃ f : X → Y i,
      Continuous f ∧ (Set.range f).Finite ∧
      ∀ (x : X) (j : Fin d), dist (f (unitVector j +ᵥ x)) (τ i (f x)) < δ) :
    ApproximateParityMaps (d := d) X Z σ := by
  have hη : ∀ i, UniformContinuous (η i) := by
    intro i
    apply Metric.uniformContinuous_iff.mpr
    intro ε hε
    obtain ⟨δ,hδ,hbound⟩ := hmodulus ε hε
    refine ⟨δ,hδ,?_⟩
    intro p q hpq
    exact hbound i p q hpq
  intro ε hε
  obtain ⟨δ,hδ,hbound⟩ := hmodulus ε hε
  obtain ⟨i,f,hf,hfin,hclose⟩ := source δ hδ
  refine ⟨η i ∘ f,(hη i).continuous.comp hf,?_,?_⟩
  · apply (hfin.image (η i)).subset
    rintro z ⟨x,rfl⟩
    exact ⟨f x,⟨x,rfl⟩,rfl⟩
  · intro x j
    simpa only [Function.comp_def,hequiv] using hbound i _ _ (hclose x j)

end

end AbelianTargets
