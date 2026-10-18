import AbelianTargets.RealizedBottomCombing

/-! An explicit logarithmic track bound for the actual bottom combing. -/

namespace AbelianTargets.IntervalCarriers
open scoped NNReal

theorem carryRowBudget_log_bound (m R : ℕ) :
    carryRowBudget m R+2 ≤ (3*m+8)*(Nat.log m R+1) := by
  have h₁ : 2*m+7 ≤ (2*m+7)*(Nat.log m R+1) := by
    simpa only [mul_one] using Nat.mul_le_mul_left (2*m+7)
      (show 1 ≤ Nat.log m R+1 by omega)
  calc
    carryRowBudget m R+2 = (m+1)*(Nat.log m R+1)+(2*m+7) := by
      unfold carryRowBudget
      omega
    _ ≤ (m+1)*(Nat.log m R+1)+(2*m+7)*(Nat.log m R+1) := Nat.add_le_add_left h₁ _
    _ = (3*m+8)*(Nat.log m R+1) := by ring

theorem realizedBottomCombing_log_speed (m : ℕ) (hm : 2 ≤ m) (R : ℕ)
    (hR : 0 < R) (x : ℝ) :
    LipschitzWith (((3*m+8)*(Nat.log m R+1) : ℕ) : ℝ≥0)
      (fun u => realizedBottomCombing m hm R hR (x,u)) := by
  exact (realizedBottomCombing_path_time_lipschitz m hm R hR x).weaken (by
    exact_mod_cast carryRowBudget_log_bound m R)

end AbelianTargets.IntervalCarriers
