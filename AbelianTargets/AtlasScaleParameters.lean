import AbelianTargets.ControlledAtlasScaleChoice
import AbelianTargets.CanonicalIntervalContractions
import AbelianTargets.AnisotropicRankRates

/-!
Choose the longitudinal scale before the transverse scale. The common
contraction family and its joint constant depend only on the former.
This produces the literal rank rates needed by the canonical marker atlas.
-/

namespace AbelianTargets
noncomputable section
open scoped NNReal

/-- Actual small-rate parameters, including a single normalized contraction
family shared by every cell of every pointed marker atlas at these scales. -/
structure SmallAtlasParameters (m d : ℕ) (i : Fin d) (η : ℝ) where
  scales : Fin d → ℕ
  scales_pos : ∀ j, 1 ≤ scales j
  scales_large : ∀ j, 32 * 61 ^ d ≤ scales j
  height : ℕ
  joint : ℝ≥0
  contractions : IntervalCarriers.NormalizedContractionFamily
    m height (6 * scales i) joint
  rate_lt : ∀ j,
    (atlasRankRates
      (fun k => (scales k : ℝ≥0) / (32 * (61 ^ d : ℕ)))
      (fun k => 6 * (scales k : ℝ≥0))
      (IntervalCarriers.uniformCarrierSpeed m height) joint i (d + 1) j : ℝ) < η

/-- The joint contraction constant is selected as a function of the first
scale before the two-scale existence theorem is used. In particular, the
transverse scale cannot feed back into that constant. -/
theorem exists_smallAtlasParameters (m : ℕ) (hm : 2 ≤ m) (d : ℕ)
    (i : Fin d) {η : ℝ} (hη : 0 < η) :
    Nonempty (SmallAtlasParameters m d i η) := by
  classical
  let K : ℕ → ℕ := fun a => Nat.log m (6 * (a + 2))
  let D : ℕ → ℝ≥0 := fun a => IntervalCarriers.uniformCarrierSpeed m (K a)
  have hfamily (a : ℕ) : ∃ J : ℝ≥0,
      Nonempty (IntervalCarriers.NormalizedContractionFamily m (K a) (6 * a) J) := by
    apply IntervalCarriers.exists_normalizedContractionFamily m hm (K a) (6 * a)
    exact Nat.log_mono_right (by omega)
  choose J hJ using hfamily
  let H (a : ℕ) := Classical.choice (hJ a)
  let P : ℝ≥0 := (61 ^ d : ℕ)
  let A : ℝ≥0 := firstRankFactor P (d + 1)
  let B : ℕ → ℝ := fun a => (transverseRankFactor P d (D a) (J a) (d + 1) : ℝ)
  obtain ⟨a, b, ha, ha₀, hb, hb₀, hsmall⟩ :=
    exists_controlled_atlas_scales m hm A B (32 * 61 ^ d) (32 * 61 ^ d) hη
  let L : Fin d → ℕ := fun j => if j = i then a else b
  have hLi : L i = a := by simp [L]
  have hpos : ∀ j, 1 ≤ L j := by
    intro j
    dsimp [L]
    split_ifs <;> assumption
  have hlarge : ∀ j, 32 * 61 ^ d ≤ L j := by
    intro j
    dsimp [L]
    split_ifs <;> assumption
  have hP : 0 < P := by dsimp [P]; positivity
  have hfirst : (A : ℝ) * (D a : ℝ) / (a : ℝ) < η := by
    have hnonneg : 0 ≤ B a / (b : ℝ) := by dsimp [B]; positivity
    change (A : ℝ) * (D a : ℝ) / (a : ℝ) + B a / (b : ℝ) < η at hsmall
    linarith
  have hother : B a / (b : ℝ) < η := by
    have hnonneg : 0 ≤ (A : ℝ) * (D a : ℝ) / (a : ℝ) := by positivity
    change (A : ℝ) * (D a : ℝ) / (a : ℝ) + B a / (b : ℝ) < η at hsmall
    linarith
  refine ⟨{
    scales := L
    scales_pos := hpos
    scales_large := hlarge
    height := K a
    joint := J a
    contractions := by simpa only [hLi] using H a
    rate_lt := ?_
  }⟩
  intro j
  have hlower : (fun k => (L k : ℝ≥0) / (32 * (61 ^ d : ℕ))) =
      anisotropicLowerRates i P (a : ℝ≥0) (b : ℝ≥0) := by
    funext k
    dsimp [L, anisotropicLowerRates, P]
    split_ifs <;> rfl
  have hupper : (fun k => 6 * (L k : ℝ≥0)) =
      anisotropicUpperRates i (a : ℝ≥0) (b : ℝ≥0) := by
    funext k
    dsimp [L, anisotropicUpperRates]
    split_ifs <;> rfl
  rw [hlower, hupper]
  have hrates := anisotropic_rank_rates_bound i P (a : ℝ≥0) (b : ℝ≥0)
    (D a) (J a) hP (by exact_mod_cast ha) (by exact_mod_cast hb) (d + 1) j
  have hrates' :
      (atlasRankRates (anisotropicLowerRates i P (a : ℝ≥0) (b : ℝ≥0))
        (anisotropicUpperRates i (a : ℝ≥0) (b : ℝ≥0))
        (D a) (J a) i (d + 1) j : ℝ) ≤
      (if j = i then A * D a / (a : ℝ≥0)
        else transverseRankFactor P d (D a) (J a) (d + 1) / (b : ℝ≥0) : ℝ≥0) := by
    exact_mod_cast hrates
  apply lt_of_le_of_lt hrates'
  by_cases hj : j = i
  · simpa only [if_pos hj, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast] using hfirst
  · simpa only [if_neg hj, NNReal.coe_div, NNReal.coe_natCast, B] using hother

end
end AbelianTargets
