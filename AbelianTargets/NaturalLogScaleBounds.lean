import AbelianTargets.AnisotropicScales
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Converting the literal base-`m` carrier height into the analytic scale bound. -/
namespace AbelianTargets
open Filter Topology
noncomputable section

theorem nat_log_le_real_log (m : ℕ) (hm : 2≤m) (R : ℕ) (hR : 0<R) :
    (Nat.log m R : ℝ)≤Real.log (R : ℝ)/Real.log (m : ℝ) := by
  have hm' : (1 : ℝ)<m := by exact_mod_cast (show 1<m by omega)
  have hp : 0<(m : ℝ)^Nat.log m R := pow_pos (by linarith) _
  have hpow : (m : ℝ)^Nat.log m R≤(R : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self m (Nat.ne_of_gt hR)
  have hh := Real.log_le_log hp hpow
  rw [Real.log_pow] at hh
  exact (le_div_iff₀ (Real.log_pos hm')).mpr hh

def carrierHeightLogCoefficient (m C : ℕ) : ℝ :=
  (1+Real.log (C : ℝ)/Real.log 2)/Real.log (m : ℝ)+1/Real.log 2

theorem nat_log_scaled_bound (m : ℕ) (hm : 2≤m) (C : ℕ) (hC : 1≤C) (L : ℕ) :
    (Nat.log m (C*(L+2))+1 : ℝ)≤carrierHeightLogCoefficient m C*Real.log ((L : ℝ)+2) := by
  have hCpos : 0<(C : ℝ) := by exact_mod_cast (show 0<C by omega)
  have hCm : 1≤(C : ℝ) := by exact_mod_cast hC
  have hmlog : 0<Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (show 1<m by omega))
  have htwo : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hx : 0<(L : ℝ)+2 := by positivity
  have hlogx : Real.log 2≤Real.log ((L : ℝ)+2) := Real.log_le_log (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) L; linarith)
  have hlogC : 0≤Real.log (C : ℝ) := Real.log_nonneg hCm
  have hratio : 1≤Real.log ((L : ℝ)+2)/Real.log 2 := (one_le_div htwo).mpr hlogx
  have hCscale : Real.log (C : ℝ)≤(Real.log (C : ℝ)/Real.log 2)*Real.log ((L : ℝ)+2) := by
    have hh := mul_le_mul_of_nonneg_left hratio hlogC
    calc
      Real.log (C : ℝ)≤Real.log (C : ℝ)*(Real.log ((L : ℝ)+2)/Real.log 2) := by simpa using hh
      _ = _ := by ring
  have hn := nat_log_le_real_log m hm (C*(L+2)) (by positivity)
  have he : ((C*(L+2) : ℕ) : ℝ)=(C : ℝ)*((L : ℝ)+2) := by push_cast; rfl
  rw [he,Real.log_mul hCpos.ne' hx.ne'] at hn
  have hlogbound : (Real.log (C : ℝ)+Real.log ((L : ℝ)+2))/Real.log (m : ℝ)≤
      ((1+Real.log (C : ℝ)/Real.log 2)/Real.log (m : ℝ))*Real.log ((L : ℝ)+2) := by
    apply (div_le_iff₀ hmlog).mpr
    have he' : (((1+Real.log (C : ℝ)/Real.log 2)/Real.log (m : ℝ))*Real.log ((L : ℝ)+2))*Real.log (m : ℝ)=
        (1+Real.log (C : ℝ)/Real.log 2)*Real.log ((L : ℝ)+2) := by field_simp
    rw [he']; nlinarith
  have hone : (1 : ℝ)≤(1/Real.log 2)*Real.log ((L : ℝ)+2) := by
    convert hratio using 1 <;> ring
  dsimp [carrierHeightLogCoefficient]
  calc
    _ ≤ ((1+Real.log (C : ℝ)/Real.log 2)/Real.log (m : ℝ))*Real.log ((L : ℝ)+2)+
        (1/Real.log 2)*Real.log ((L : ℝ)+2) := add_le_add (hn.trans hlogbound) hone
    _ = _ := by ring

theorem nat_log_scaled_error_tendsto (m : ℕ) (hm : 2≤m) (C : ℕ) (hC : 1≤C) :
    Tendsto (fun L : ℕ => (Nat.log m (C*(L+2))+1 : ℝ)/(L : ℝ)) atTop (𝓝 0) := by
  have hup : Tendsto (fun L : ℕ => carrierHeightLogCoefficient m C*Real.log ((L : ℝ)+2)/(L : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero,mul_div_assoc] using logarithmic_scale_error_tendsto.const_mul (carrierHeightLogCoefficient m C)
  apply squeeze_zero (fun L => div_nonneg (by positivity) (by positivity)) (fun L => ?_) hup
  exact div_le_div_of_nonneg_right (nat_log_scaled_bound m hm C hC L) (by positivity)

end
end AbelianTargets
