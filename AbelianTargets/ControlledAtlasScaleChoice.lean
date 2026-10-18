import AbelianTargets.NaturalLogScaleBounds
import AbelianTargets.UniformCarrierContraction

namespace AbelianTargets
noncomputable section
open scoped NNReal

theorem uniformCarrierSpeed_log_bound (m : ℕ) (hm : 2≤m) (L : ℕ) :
    (IntervalCarriers.uniformCarrierSpeed m (Nat.log m (6*(L+2))) : ℝ)≤
      (2*(3*m+8 : ℕ) : ℝ)*carrierHeightLogCoefficient m 6*Real.log ((L : ℝ)+2) := by
  have hh := nat_log_scaled_bound m hm 6 (by norm_num) L
  have he : (IntervalCarriers.uniformCarrierSpeed m (Nat.log m (6*(L+2))) : ℝ)=
      (2*(3*m+8 : ℕ) : ℝ)*(Nat.log m (6*(L+2))+1 : ℝ) := by
    unfold IntervalCarriers.uniformCarrierSpeed
    push_cast
    ring
  rw [he]
  calc
    _ ≤ (2*(3*m+8 : ℕ) : ℝ)*(carrierHeightLogCoefficient m 6*Real.log ((L : ℝ)+2)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

theorem exists_controlled_atlas_scales (m : ℕ) (hm : 2≤m)
    (A : ℝ≥0) (B : ℕ→ℝ) (L₀ M₀ : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃L M : ℕ,1≤L ∧ L₀≤L ∧ 1≤M ∧ M₀≤M ∧
      (A : ℝ)*(IntervalCarriers.uniformCarrierSpeed m (Nat.log m (6*(L+2))) : ℝ)/(L : ℝ)+B L/(M : ℝ)<ε := by
  obtain ⟨L,M,hL,hL₀,hM,hM₀,hh⟩ := exists_anisotropic_scales
    ((A : ℝ)*(2*(3*m+8 : ℕ) : ℝ)*carrierHeightLogCoefficient m 6) B L₀ M₀ hε
  refine ⟨L,M,hL,hL₀,hM,hM₀,lt_of_le_of_lt ?_ hh⟩
  have hs := uniformCarrierSpeed_log_bound m hm L
  have ha : (A : ℝ)* (IntervalCarriers.uniformCarrierSpeed m (Nat.log m (6*(L+2))) : ℝ)≤
      ((A : ℝ)*(2*(3*m+8 : ℕ) : ℝ)*carrierHeightLogCoefficient m 6)*Real.log ((L : ℝ)+2) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs A.coe_nonneg
  exact add_le_add (div_le_div_of_nonneg_right ha (by positivity : 0≤(L : ℝ))) le_rfl

end
end AbelianTargets
