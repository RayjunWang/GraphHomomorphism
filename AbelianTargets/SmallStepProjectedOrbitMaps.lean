import AbelianTargets.AtlasScaleParameters
import AbelianTargets.CanonicalActionCovariance
import AbelianTargets.RegularAnisotropicAtlas
import AbelianTargets.UniformCarrierSupportProjection

/-!
Actual small-step orbit maps for arbitrary free zero-dimensional Polish
lattice actions. All geometric and quantitative parameters are constructed
before the canonical projected map is evaluated on the action space.
-/

namespace AbelianTargets
noncomputable section
open scoped NNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Integer-coordinate orbit data with finite continuous origin values.
Repointing acts on the support shores by the chosen coordinate parity. -/
structure SmallStepLatticeOrbitMap {d : ℕ} {X V : Type*}
    [TopologicalSpace X] [AddAction (Lattice d) X] [Fintype V]
    (H : SimpleGraph V) (i : Fin d) (ε : ℝ) where
  orbitMap : X → Lattice d → SupportPair H
  continuous_origin : Continuous (fun x => orbitMap x 0)
  finite_range_origin : (Set.range (fun x => orbitMap x 0)).Finite
  covariance : ∀ x g, orbitMap (g +ᵥ x) 0 =
    SupportPair.paritySwap H (g i) (orbitMap x g)
  unit_step : ∀ x j g, dist (orbitMap x (g + unitVector j)) (orbitMap x g) < ε

/-- The required origin values, exact repointing identity, and small integer
unit steps are supplied by the actual canonical atlas construction.
The projection modulus is uniform in every carrier height and interval. -/
theorem exists_smallStepLatticeOrbitMap
    {d : ℕ} {X V : Type*} [TopologicalSpace X] [PolishSpace X]
    [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
    [Fintype V] {H : SimpleGraph V} (D : SupportTorsionData H) (i : Fin d)
    (zeroDim : ZeroDimensional X) (free : IsFree (G := Lattice d) (X := X))
    {ε : ℝ} (hε : 0 < ε) :
    Nonempty (SmallStepLatticeOrbitMap (X := X) H i ε) := by
  classical
  obtain ⟨δ, hδ, hmod⟩ := D.carrierProjection_uniform_modulus ε hε
  have hm : 2 ≤ 2 * D.power + 1 := by have := D.power_pos; omega
  obtain ⟨P⟩ := exists_smallAtlasParameters (2 * D.power + 1) hm d i hδ
  obtain ⟨A⟩ := exists_regularAnisotropicAtlas P.scales zeroDim free P.scales_large
  let B := A.boxes
  have h30 : (24 : ℕ) ≤ 30 := by norm_num
  have hsmall (j : Fin d) :
      (atlasRankRates
        (fun k => (P.scales k : ℝ≥0) / (32 * ((2 * 30 + 1) ^ d : ℕ)))
        (fun k => 6 * (P.scales k : ℝ≥0))
        (IntervalCarriers.uniformCarrierSpeed (2 * D.power + 1) P.height)
        P.joint i (d + 1) j : ℝ) < δ := by
    simpa only [show 2 * 30 + 1 = (61 : ℕ) by norm_num] using P.rate_lt j
  refine ⟨{
    orbitMap := fun x g => B.canonicalProjectedMap D P.scales_pos h30
      P.height i P.joint P.contractions x (fun k => (g k : ℝ))
    continuous_origin := ?_
    finite_range_origin := ?_
    covariance := ?_
    unit_step := ?_
  }⟩
  · simpa only [Pi.zero_apply, Int.cast_zero] using
      B.continuous_canonicalProjectedMap D P.scales_pos h30
        P.height i P.joint P.contractions (0 : RealCoordinates d)
  · simpa only [Pi.zero_apply, Int.cast_zero] using
      B.canonicalProjectedMap_finite_range D P.scales_pos h30
        P.height i P.joint P.contractions (0 : RealCoordinates d)
  · intro x g
    have hz : translateCoordinates g (0 : RealCoordinates d) =
        (fun k => (g k : ℝ)) := by
      funext k
      simp [translateCoordinates]
    have hh := B.canonicalProjectedMap_repoint_forward D P.scales_pos h30
      P.height i P.joint P.contractions x g (0 : RealCoordinates d)
    rw [hz] at hh
    simpa only [Pi.zero_apply, Int.cast_zero] using hh
  · intro x j g
    have hh :=
      (B.canonicalQuantitativeSkeleton P.scales_pos h30 x
        (2 * D.power + 1) P.height i P.joint P.contractions (d + 1)).projected_lattice_step_close
          D ε δ (fun a b p q hpq => hmod P.height a b p q hpq) j g (hsmall j)
    simpa only [ContinuousMarkerBoxes.canonicalProjectedMap, dist_comm] using hh

end
end AbelianTargets
