import AbelianTargets.VariableRowFamilies
import AbelianTargets.JointHomotopyGluing

/-! Reserving the final path slot for a continuously moving endpoint. -/

namespace AbelianTargets.FixedSlots
open scoped NNReal
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def correctionCut (n : ℕ) : ℝ := ((n : ℝ)+1)/((n : ℝ)+2)
def correctionScale (n : ℕ) : ℝ≥0 := ⟨((n : ℝ)+2)/((n : ℝ)+1),by positivity⟩

theorem correctionCut_pos (n : ℕ) : 0 < correctionCut n := by unfold correctionCut; positivity
theorem correctionCut_lt_one (n : ℕ) : correctionCut n < 1 := by
  unfold correctionCut
  apply (div_lt_one (by positivity)).mpr
  linarith

theorem correctionScale_cut (n : ℕ) : (correctionScale n : ℝ)*correctionCut n = 1 := by
  change (((n : ℝ)+2)/((n : ℝ)+1))*(((n : ℝ)+1)/((n : ℝ)+2)) = 1
  have h₁ : (n : ℝ)+1 ≠ 0 := by positivity
  have h₂ : (n : ℝ)+2 ≠ 0 := by positivity
  field_simp

theorem correction_final_zero (n : ℕ) : ((n : ℝ)+2)*correctionCut n-((n : ℝ)+1) = 0 := by
  unfold correctionCut
  have h₂ : (n : ℝ)+2 ≠ 0 := by positivity
  field_simp
  ring

theorem lipschitz_clamp_affine (c : ℝ≥0) (b : ℝ) :
    LipschitzWith c (fun u : ℝ => clampInterval ((c : ℝ)*u+b)) := by
  simpa only [one_mul,Function.comp_def] using
    lipschitz_clampInterval.comp (lipschitz_affine_le c c b (by simp))

def correctedCarryRaw (n : ℕ) (F : unitInterval × unitInterval → E) (q : E)
    (e : unitInterval → E) (z : unitInterval × ℝ) : E :=
  if z.2 ≤ correctionCut n then F (z.1,clampInterval ((correctionScale n : ℝ)*z.2))
  else mix q (e z.1) (clampInterval (((n : ℝ)+2)*z.2-((n : ℝ)+1)))

def correctedCarry (n : ℕ) (F : unitInterval × unitInterval → E) (q : E)
    (e : unitInterval → E) (z : unitInterval × unitInterval) : E :=
  correctedCarryRaw n F q e (z.1,z.2)

theorem correctedCarry_continuous (n : ℕ) (F : unitInterval × unitInterval → E)
    (hF : Continuous F) (q : E) (e : unitInterval → E) (he : Continuous e)
    (htarget : ∀ r, F (r,1) = q) : Continuous (correctedCarry n F q e) := by
  have h₀ : Continuous (fun z : unitInterval × ℝ =>
      F (z.1,clampInterval ((correctionScale n : ℝ)*z.2))) :=
    hF.comp (continuous_fst.prodMk
      (lipschitz_clampInterval.continuous.comp (continuous_const.mul continuous_snd)))
  have h₁ : Continuous (fun z : unitInterval × ℝ =>
      mix q (e z.1) (clampInterval (((n : ℝ)+2)*z.2-((n : ℝ)+1)))) := by
    unfold mix
    exact (continuous_const.sub
      (continuous_subtype_val.comp (lipschitz_clampInterval.continuous.comp
        ((continuous_const.mul continuous_snd).sub continuous_const)))).smul continuous_const |>.add
      ((continuous_subtype_val.comp (lipschitz_clampInterval.continuous.comp
        ((continuous_const.mul continuous_snd).sub continuous_const))).smul (he.comp continuous_fst))
  have hh : Continuous (correctedCarryRaw n F q e) := by
    apply h₀.if_le h₁ continuous_snd continuous_const
    intro z hz
    change z.2 = correctionCut n at hz
    rw [hz,correctionScale_cut,correction_final_zero]
    simp [clampInterval,htarget]
  exact hh.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

theorem correctedCarry_path_time_lipschitz (n : ℕ) (F : unitInterval × unitInterval → E)
    (q : E) (e : unitInterval → E) (Δ : ℝ≥0)
    (hF : ∀ r, LipschitzWith (Δ*(n+1)) (fun u : unitInterval => F (r,u)))
    (htarget : ∀ r, F (r,1) = q) (he : ∀ r, dist q (e r) ≤ Δ) (r : unitInterval) :
    LipschitzWith (Δ*(n+2)) (fun u : unitInterval => correctedCarry n F q e (r,u)) := by
  have hfactor : (Δ*(n+1))*correctionScale n = Δ*(n+2) := by
    apply Subtype.ext
    change (Δ : ℝ)*((n : ℝ)+1)*(((n : ℝ)+2)/((n : ℝ)+1)) = (Δ : ℝ)*((n : ℝ)+2)
    have hne : (n : ℝ)+1 ≠ 0 := by positivity
    field_simp
  have h₀ : LipschitzWith (Δ*(n+2)) (fun u : ℝ =>
      F (r,clampInterval ((correctionScale n : ℝ)*u))) := by
    simpa only [Function.comp_def,add_zero,hfactor] using
      (hF r).comp (lipschitz_clamp_affine (correctionScale n) 0)
  have h₁ : LipschitzWith (Δ*(n+2)) (fun u : ℝ =>
      mix q (e r) (clampInterval (((n : ℝ)+2)*u-((n : ℝ)+1)))) := by
    simpa only [Function.comp_def,sub_eq_add_neg] using
      (mix_lipschitz q (e r) Δ (he r)).comp
        (lipschitz_clamp_affine (n+2) (-((n : ℝ)+1)))
  have hh := lipschitz_glue_at _ _ h₀ h₁ (correctionCut n) (by
    rw [correctionScale_cut,correction_final_zero]
    simp [clampInterval,htarget])
  simpa only [Function.comp_def,mul_one,correctedCarry,correctedCarryRaw] using
    hh.comp (LipschitzWith.subtype_val (Set.Icc (0 : ℝ) 1))

@[simp] theorem correctedCarry_source (n : ℕ) (F : unitInterval × unitInterval → E)
    (q : E) (e : unitInterval → E) (r : unitInterval) :
    correctedCarry n F q e (r,0) = F (r,0) := by
  simp [correctedCarry,correctedCarryRaw,(correctionCut_pos n).le,clampInterval]

@[simp] theorem correctedCarry_target (n : ℕ) (F : unitInterval × unitInterval → E)
    (q : E) (e : unitInterval → E) (r : unitInterval) :
    correctedCarry n F q e (r,1) = e r := by
  change (if (1 : ℝ) ≤ correctionCut n then _ else _) = _
  rw [if_neg (not_le.mpr (correctionCut_lt_one n))]
  change mix q (e r) (clampInterval (((n : ℝ)+2)*1-((n : ℝ)+1))) = e r
  have he : ((n : ℝ)+2)*1-((n : ℝ)+1) = 1 := by ring
  rw [he]
  simp [clampInterval]

theorem correctedCarry_mem {S : Set E} (n : ℕ) (F : unitInterval × unitInterval → E)
    (q : E) (e : unitInterval → E) (hF : ∀ z, F z ∈ S)
    (hseg : ∀ r t, mix q (e r) t ∈ S) (z : unitInterval × unitInterval) :
    correctedCarry n F q e z ∈ S := by
  unfold correctedCarry correctedCarryRaw
  split
  · exact hF _
  · exact hseg _ _

end
end AbelianTargets.FixedSlots
