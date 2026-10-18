import AbelianTargets.JointEndpointCorrection

/-! Literal seam gluing of two square families, including moving endpoints. -/

namespace AbelianTargets.FixedSlots
open scoped NNReal
noncomputable section

variable {Z : Type*} [MetricSpace Z]

def halfGlueRaw (F G : unitInterval × unitInterval → Z) (z : ℝ × unitInterval) : Z :=
  if z.1 ≤ 1/2 then F (clampInterval (2*z.1),z.2)
  else G (clampInterval (2*z.1-1),z.2)

def halfGlue (F G : unitInterval × unitInterval → Z) (z : unitInterval × unitInterval) : Z :=
  halfGlueRaw F G (z.1,z.2)

theorem halfGlue_continuous (F G : unitInterval × unitInterval → Z)
    (hF : Continuous F) (hG : Continuous G) (hmatch : ∀ u, F (1,u) = G (0,u)) :
    Continuous (halfGlue F G) := by
  have h₀ : Continuous (fun z : ℝ × unitInterval => F (clampInterval (2*z.1),z.2)) :=
    hF.comp ((lipschitz_clampInterval.continuous.comp (continuous_const.mul continuous_fst)).prodMk
      continuous_snd)
  have h₁ : Continuous (fun z : ℝ × unitInterval => G (clampInterval (2*z.1-1),z.2)) :=
    hG.comp ((lipschitz_clampInterval.continuous.comp
      ((continuous_const.mul continuous_fst).sub continuous_const)).prodMk continuous_snd)
  have hh : Continuous (halfGlueRaw F G) := by
    apply h₀.if_le h₁ continuous_fst continuous_const
    intro z hz
    change z.1 = 1/2 at hz
    simp only [hz]
    norm_num [clampInterval]
    exact hmatch z.2
  exact hh.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

theorem halfGlue_path_time_lipschitz (F G : unitInterval × unitInterval → Z) {K : ℝ≥0}
    (hF : ∀ r, LipschitzWith K (fun u => F (r,u)))
    (hG : ∀ r, LipschitzWith K (fun u => G (r,u))) (r : unitInterval) :
    LipschitzWith K (fun u => halfGlue F G (r,u)) := by
  by_cases hr : (r : ℝ) ≤ 1/2
  · simpa only [halfGlue,halfGlueRaw,if_pos hr] using hF (clampInterval (2*(r : ℝ)))
  · simpa only [halfGlue,halfGlueRaw,if_neg hr] using hG (clampInterval (2*(r : ℝ)-1))

theorem halfGlue_joint_lipschitz (F G : unitInterval × unitInterval → Z) {K L : ℝ≥0}
    (hF : LipschitzWith K F) (hG : LipschitzWith L G)
    (hmatch : ∀ u, F (1,u) = G (0,u)) : LipschitzWith (4*max K L) (halfGlue F G) := by
  have ha : LipschitzWith 2 (fun z : ℝ × unitInterval => (clampInterval (2*z.1),z.2)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hc := (lipschitz_clamp_affine 2 0).dist_le_mul x.1 y.1
    simp only [add_zero] at hc
    change max (dist (clampInterval (2*x.1)) (clampInterval (2*y.1))) (dist x.2 y.2) ≤ _
    apply max_le
    · exact hc.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num))
    · have hh : dist x.2 y.2 ≤ dist x y := le_max_right _ _
      simp only [NNReal.coe_ofNat]; nlinarith [dist_nonneg (x := x) (y := y)]
  have hb : LipschitzWith 2 (fun z : ℝ × unitInterval => (clampInterval (2*z.1-1),z.2)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hc := (lipschitz_clamp_affine 2 (-1)).dist_le_mul x.1 y.1
    simp only [show ∀ u : ℝ, 2*u+(-1) = 2*u-1 by intro u; ring] at hc
    change max (dist (clampInterval (2*x.1-1)) (clampInterval (2*y.1-1))) (dist x.2 y.2) ≤ _
    apply max_le
    · exact hc.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num))
    · have hh : dist x.2 y.2 ≤ dist x y := le_max_right _ _
      simp only [NNReal.coe_ofNat]; nlinarith [dist_nonneg (x := x) (y := y)]
  have hf : LipschitzWith (2*max K L) (fun z : ℝ × unitInterval => F (clampInterval (2*z.1),z.2)) :=
    by simpa only [Function.comp_def,mul_comm] using (hF.weaken (le_max_left K L)).comp ha
  have hg : LipschitzWith (2*max K L) (fun z : ℝ × unitInterval => G (clampInterval (2*z.1-1),z.2)) :=
    by simpa only [Function.comp_def,mul_comm] using (hG.weaken (le_max_right K L)).comp hb
  have hh := lipschitz_glue_product_at _ _ hf hg (1/2) (by
    intro u
    norm_num [clampInterval]
    exact hmatch u)
  have he : LipschitzWith 1 (fun z : unitInterval × unitInterval => ((z.1 : ℝ),z.2)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist x y ≤ (1 : ℝ)*dist x y
    simp
  simpa only [Function.comp_def,halfGlue,halfGlueRaw,mul_one,
    show 2*(2*max K L)=4*max K L by ring] using hh.comp he

theorem halfGlue_mem {S : Set Z} (F G : unitInterval × unitInterval → Z)
    (hF : ∀ z, F z ∈ S) (hG : ∀ z, G z ∈ S) (z : unitInterval × unitInterval) :
    halfGlue F G z ∈ S := by
  unfold halfGlue halfGlueRaw
  split
  · exact hF _
  · exact hG _

@[simp] theorem halfGlue_zero (F G : unitInterval × unitInterval → Z) (u : unitInterval) :
    halfGlue F G (0,u) = F (0,u) := by simp [halfGlue,halfGlueRaw,clampInterval]

@[simp] theorem halfGlue_one (F G : unitInterval × unitInterval → Z) (u : unitInterval) :
    halfGlue F G (1,u) = G (1,u) := by norm_num [halfGlue,halfGlueRaw,clampInterval]

end
end AbelianTargets.FixedSlots
