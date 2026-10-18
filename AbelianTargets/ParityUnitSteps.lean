import AbelianTargets.ParityFields

/-! Closing via unit steps after a uniformly continuous projection.
A global Lipschitz estimate on the projected support map is unnecessary:
the shear generator is a sum of at most two coordinate unit steps. -/

namespace AbelianTargets
noncomputable section
variable {d : ℕ} {X Y : Type*} [TopologicalSpace X] [AddAction (Lattice d) X]
  [MetricSpace Y] {τ : Y→Y} {hd : 1≤d} {ε : ℝ}

structure ProjectedParityStepMap (τ : Y→Y) (hd : 1≤d) (ε : ℝ) where
  orbitMap : X→RealCoordinates d→Y
  continuous_origin : Continuous (fun x=>orbitMap x 0)
  finite_range_origin : (Set.range (fun x=>orbitMap x 0)).Finite
  covariance : ∀x i,orbitMap (unitVector i +ᵥ x) 0=τ (orbitMap x (parityStep hd i))
  unit_step : ∀x i u,dist (orbitMap x (u+realUnitVector i)) (orbitMap x u)<ε

theorem ProjectedParityStepMap.generator_error_lt (F : ProjectedParityStepMap (X := X) τ hd ε)
    (hτ : Isometry τ) (hε : 0<ε) (x : X) (i : Fin d) :
    dist (F.orbitMap (unitVector i +ᵥ x) 0) (τ (F.orbitMap x 0))<2*ε := by
  rw [F.covariance,hτ.dist_eq]
  have hf : dist (F.orbitMap x (realUnitVector (firstAxis hd))) (F.orbitMap x 0)<ε := by
    simpa using F.unit_step x (firstAxis hd) 0
  by_cases hi : i=firstAxis hd
  · rw [parityStep,if_pos hi]
    exact hf.trans (by linarith)
  · rw [parityStep,if_neg hi]
    calc
      _ ≤ dist (F.orbitMap x (realUnitVector (firstAxis hd)+realUnitVector i))
          (F.orbitMap x (realUnitVector (firstAxis hd)))+
          dist (F.orbitMap x (realUnitVector (firstAxis hd))) (F.orbitMap x 0) := dist_triangle _ _ _
      _ < ε+ε := add_lt_add (F.unit_step x i (realUnitVector (firstAxis hd))) hf
      _ = 2*ε := by ring

theorem approximateParityMaps_of_unitStepConstruction (hτ : Isometry τ)
    (construction : ∀ε : ℝ,0<ε→Nonempty (ProjectedParityStepMap (X := X) τ hd ε)) :
    ApproximateParityMaps (d := d) X Y τ := by
  intro ε hε
  obtain ⟨F⟩ := construction (ε/2) (by positivity)
  refine ⟨fun x=>F.orbitMap x 0,F.continuous_origin,F.finite_range_origin,?_⟩
  intro x i
  have hh := F.generator_error_lt hτ (by positivity) x i
  linarith

end
end AbelianTargets
