import AbelianTargets.RectangleHalfGluing

/-! Finite families on neighboring unit intervals glue literally.
Their path-time Lipschitz constant is independent of the number of intervals. -/

namespace AbelianTargets.FixedSlots
open scoped NNReal
noncomputable section
variable {Z : Type*} [MetricSpace Z]

def intervalGlue (F : ℕ → unitInterval × unitInterval → Z) : ℕ → ℝ × unitInterval → Z
  | 0 => fun z => F 0 (clampInterval z.1,z.2)
  | n+1 => fun z => if z.1 ≤ (n : ℝ)+1 then intervalGlue F n z
      else F (n+1) (clampInterval (z.1-((n : ℝ)+1)),z.2)

theorem intervalGlue_right (F : ℕ → unitInterval × unitInterval → Z) (n : ℕ)
    (u : unitInterval) : intervalGlue F n ((n : ℝ)+1,u) = F n (1,u) := by
  cases n with
  | zero => simp [intervalGlue,clampInterval]
  | succ n =>
    simp only [intervalGlue]
    rw [if_neg (by push_cast; linarith)]
    have he : ((n+1 : ℕ) : ℝ)+1-((n : ℝ)+1) = 1 := by push_cast; ring
    rw [he]
    simp [clampInterval]

theorem intervalGlue_zero (F : ℕ → unitInterval × unitInterval → Z) (n : ℕ)
    (u : unitInterval) : intervalGlue F n (0,u) = F 0 (0,u) := by
  induction n with
  | zero => simp [intervalGlue,clampInterval]
  | succ n ih =>
    simp only [intervalGlue]
    rw [if_pos (by positivity),ih]

theorem intervalGlue_on_unit (F : ℕ → unitInterval × unitInterval → Z) (N i : ℕ)
    (hi : i ≤ N) (hmatch : ∀ j < N, ∀ u, F j (1,u) = F (j+1) (0,u))
    (s u : unitInterval) : intervalGlue F N ((i : ℝ)+s,u) = F i (s,u) := by
  induction N with
  | zero =>
    have he : i = 0 := by omega
    subst i
    simp only [intervalGlue,Nat.cast_zero,zero_add,clampInterval_coe]
  | succ N ih =>
    by_cases hi' : i ≤ N
    · simp only [intervalGlue]
      rw [if_pos (by
        have hiR : (i : ℝ) ≤ N := by exact_mod_cast hi'
        linarith [s.property.2])]
      exact ih hi' (fun j hj => hmatch j (by omega))
    · have he : i = N+1 := by omega
      subst i
      by_cases hs : (s : ℝ) = 0
      · have hs' : s = 0 := Subtype.ext hs
        subst s
        simp only [intervalGlue]
        rw [if_pos (by simp),show ((N+1 : ℕ) : ℝ)+(0 : unitInterval) =
          (N : ℝ)+1 by simp,intervalGlue_right,hmatch N (by omega)]
      · simp only [intervalGlue]
        rw [if_neg (by push_cast; intro h; apply hs; linarith [s.property.1])]
        have hc : ((N+1 : ℕ) : ℝ)+(s : ℝ)-((N : ℝ)+1) = (s : ℝ) := by push_cast; ring
        rw [hc,clampInterval_coe]

theorem intervalGlue_continuous (F : ℕ → unitInterval × unitInterval → Z) (n : ℕ)
    (hF : ∀ i ≤ n, Continuous (F i))
    (hmatch : ∀ i < n, ∀ u, F i (1,u) = F (i+1) (0,u)) :
    Continuous (intervalGlue F n) := by
  induction n with
  | zero => exact (hF 0 le_rfl).comp (lipschitz_clampInterval.continuous.prodMap continuous_id)
  | succ n ih =>
    have h₀ := ih (fun i hi => hF i (by omega)) (fun i hi => hmatch i (by omega))
    have h₁ : Continuous (fun z : ℝ × unitInterval =>
        F (n+1) (clampInterval (z.1-((n : ℝ)+1)),z.2)) :=
      (hF (n+1) le_rfl).comp ((lipschitz_clampInterval.continuous.comp
        (continuous_fst.sub continuous_const)).prodMk continuous_snd)
    apply h₀.if_le h₁ continuous_fst continuous_const
    intro z hz
    change z.1 = (n : ℝ)+1 at hz
    have he : z = ((n : ℝ)+1,z.2) := by apply Prod.ext; exact hz; rfl
    rw [he,intervalGlue_right,hmatch n (by omega)]
    simp [clampInterval]

theorem intervalGlue_path_time_lipschitz (F : ℕ → unitInterval × unitInterval → Z)
    (n : ℕ) {K : ℝ≥0} (hF : ∀ i ≤ n, ∀ r, LipschitzWith K (fun u => F i (r,u)))
    (x : ℝ) : LipschitzWith K (fun u => intervalGlue F n (x,u)) := by
  induction n with
  | zero =>
    change LipschitzWith K (fun u => F 0 (clampInterval x,u))
    exact hF 0 le_rfl _
  | succ n ih =>
    by_cases hx : x ≤ (n : ℝ)+1
    · simpa only [intervalGlue,if_pos hx] using ih (fun i hi => hF i (by omega))
    · simpa only [intervalGlue,if_neg hx] using hF (n+1) le_rfl (clampInterval (x-((n : ℝ)+1)))

theorem intervalGlue_joint_lipschitz (F : ℕ → unitInterval × unitInterval → Z) (n : ℕ)
    (hF : ∀ i ≤ n, ∃ J : ℝ≥0, LipschitzWith J (F i))
    (hmatch : ∀ i < n, ∀ u, F i (1,u) = F (i+1) (0,u)) :
    ∃ J : ℝ≥0, LipschitzWith J (intervalGlue F n) := by
  have he : ∀ b : ℝ, LipschitzWith 1 (fun z : ℝ × unitInterval =>
      (clampInterval (z.1+b),z.2)) := by
    intro b
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change max (dist (clampInterval (x.1+b)) (clampInterval (y.1+b))) (dist x.2 y.2) ≤ _
    simp only [NNReal.coe_one,one_mul]
    apply max_le
    · have hh := (lipschitz_clamp_affine 1 b).dist_le_mul x.1 y.1
      simpa only [NNReal.coe_one,one_mul] using hh.trans (le_max_left _ _)
    · exact le_max_right _ _
  induction n with
  | zero =>
    obtain ⟨J,hJ⟩ := hF 0 le_rfl
    exact ⟨J,by simpa only [Function.comp_def,add_zero,mul_one,intervalGlue]
      using hJ.comp (he 0)⟩
  | succ n ih =>
    obtain ⟨J,hJ⟩ := ih (fun i hi => hF i (by omega)) (fun i hi => hmatch i (by omega))
    obtain ⟨L,hL⟩ := hF (n+1) le_rfl
    have hg : LipschitzWith L (fun z : ℝ × unitInterval =>
        F (n+1) (clampInterval (z.1-((n : ℝ)+1)),z.2)) := by
      simpa only [Function.comp_def,mul_one,sub_eq_add_neg] using hL.comp (he (-((n : ℝ)+1)))
    refine ⟨2*max J L,lipschitz_glue_product_at _ _
      (hJ.weaken (le_max_left J L)) (hg.weaken (le_max_right J L)) ((n : ℝ)+1) ?_⟩
    intro u
    rw [intervalGlue_right,hmatch n (by omega)]
    simp [clampInterval]

theorem intervalGlue_mem {S : Set Z} (F : ℕ → unitInterval × unitInterval → Z) (n : ℕ)
    (hF : ∀ i ≤ n, ∀ z, F i z ∈ S) (z : ℝ × unitInterval) :
    intervalGlue F n z ∈ S := by
  induction n with
  | zero => exact hF 0 le_rfl _
  | succ n ih =>
    unfold intervalGlue
    split
    · exact ih (fun i hi => hF i (by omega))
    · exact hF (n+1) le_rfl _

theorem intervalGlue_congr (F G : ℕ → unitInterval × unitInterval → Z) (n : ℕ)
    (h : ∀ i ≤ n, F i = G i) : intervalGlue F n = intervalGlue G n := by
  induction n with
  | zero => simp only [intervalGlue,h 0 le_rfl]
  | succ n ih =>
    simp only [intervalGlue,ih (fun i hi => h i (by omega)),h (n+1) le_rfl]

theorem intervalGlue_eval_eq (F G : ℕ → unitInterval × unitInterval → Z) (n : ℕ)
    (u : unitInterval) (h : ∀ i ≤ n, ∀ r, F i (r,u) = G i (r,u)) (x : ℝ) :
    intervalGlue F n (x,u) = intervalGlue G n (x,u) := by
  induction n with
  | zero => exact h 0 le_rfl _
  | succ n ih =>
    simp only [intervalGlue]
    split
    · exact ih (fun i hi => h i (by omega))
    · exact h (n+1) le_rfl _

end
end AbelianTargets.FixedSlots
