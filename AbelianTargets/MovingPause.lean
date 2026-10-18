import AbelianTargets.RelativePathBounds

/-!
# Moving a spare constant slot through a path

A pause of fixed width can move through an arbitrary continuous path.
Its movement leaves the path-time Lipschitz constant unchanged. This is
an analytic pause-transport primitive for Section 4; it does not claim
the complete bounded-list padding adapter or a whole-carrier contraction.
-/

namespace AbelianTargets.FixedSlots

set_option backward.isDefEq.respectTransparency false

open scoped NNReal

noncomputable section

variable {Z : Type*} [PseudoMetricSpace Z]

def movingPause (F : ℝ → Z) (w : ℝ) (v u : ℝ) : Z :=
  if u ≤ v then F u else if u ≤ v+w then F v else F (u-w)

theorem movingPause_continuous (F : ℝ → Z) (hF : Continuous F) (w : ℝ) (hw : 0 ≤ w) :
    Continuous (fun z : ℝ × ℝ => movingPause F w z.1 z.2) := by
  have hinner : Continuous (fun z : ℝ × ℝ => if z.2 ≤ z.1+w then F z.1 else F (z.2-w)) := by
    apply (hF.comp continuous_fst).if_le (hF.comp (continuous_snd.sub continuous_const))
      continuous_snd (continuous_fst.add continuous_const)
    intro z hz
    change z.2 = z.1+w at hz
    change F z.1 = F (z.2-w)
    rw [hz]
    simp
  apply (hF.comp continuous_snd).if_le hinner continuous_snd continuous_fst
  intro z hz
  change F z.2 = if z.2 ≤ z.1+w then F z.1 else F (z.2-w)
  rw [hz, if_pos (by linarith)]

theorem movingPause_path_time_lipschitz (F : ℝ → Z) {K : ℝ≥0}
    (hF : LipschitzWith K F) (w : ℝ) (hw : 0 ≤ w) (v : ℝ) :
    LipschitzWith K (movingPause F w v) := by
  have hconst : LipschitzWith K (fun _ : ℝ => F v) := LipschitzWith.const' _
  have hshift : LipschitzWith K (fun u : ℝ => F (u-w)) := by
    have ht : LipschitzWith 1 (fun u : ℝ => u-w) := by
      apply LipschitzWith.of_dist_le_mul
      intro u t
      simp only [NNReal.coe_one, one_mul]
      apply le_of_eq
      rw [Real.dist_eq, Real.dist_eq]
      congr 1
      ring
    simpa using hF.comp ht
  have hinner := lipschitz_glue_at (fun _ : ℝ => F v) (fun u : ℝ => F (u-w)) hconst hshift
    (v+w) (by simp)
  apply lipschitz_glue_at F (fun u : ℝ => if u ≤ v+w then F v else F (u-w)) hF hinner v
  rw [if_pos (by linarith)]

omit [PseudoMetricSpace Z] in
theorem movingPause_mem {S : Set Z} (F : ℝ → Z) (hF : ∀ u, F u ∈ S)
    (w v u : ℝ) : movingPause F w v u ∈ S := by
  unfold movingPause
  split_ifs <;> exact hF _

/-- Move the pause continuously between any two prescribed positions. -/
def pauseTransport (F : ℝ → Z) (w v₀ v₁ : ℝ)
    (z : unitInterval × ℝ) : Z :=
  movingPause F w ((1-(z.1 : ℝ))*v₀+(z.1 : ℝ)*v₁) z.2

theorem pauseTransport_continuous (F : ℝ → Z) (hF : Continuous F) (w : ℝ) (hw : 0 ≤ w)
    (v₀ v₁ : ℝ) : Continuous (pauseTransport F w v₀ v₁) := by
  have hc : Continuous (fun z : unitInterval × ℝ =>
      (((1-(z.1 : ℝ))*v₀+(z.1 : ℝ)*v₁),z.2)) := by fun_prop
  exact (movingPause_continuous F hF w hw).comp hc

omit [PseudoMetricSpace Z] in
@[simp] theorem pauseTransport_zero (F : ℝ → Z) (w v₀ v₁ u : ℝ) :
    pauseTransport F w v₀ v₁ (0,u) = movingPause F w v₀ u := by simp [pauseTransport]

omit [PseudoMetricSpace Z] in
@[simp] theorem pauseTransport_one (F : ℝ → Z) (w v₀ v₁ u : ℝ) :
    pauseTransport F w v₀ v₁ (1,u) = movingPause F w v₁ u := by simp [pauseTransport]

theorem pauseTransport_path_time_lipschitz (F : ℝ → Z) {K : ℝ≥0}
    (hF : LipschitzWith K F) (w : ℝ) (hw : 0 ≤ w) (v₀ v₁ : ℝ) (r : unitInterval) :
    LipschitzWith K (fun u => pauseTransport F w v₀ v₁ (r,u)) :=
  movingPause_path_time_lipschitz F hF w hw ((1-(r : ℝ))*v₀+(r : ℝ)*v₁)

theorem movingPause_zero (F : ℝ → Z) (w v : ℝ) (hv : 0 ≤ v) :
    movingPause F w v 0 = F 0 := by simp only [movingPause, if_pos hv]

theorem movingPause_one (F : ℝ → Z) (w v : ℝ) (hw : 0 < w) (hv : v ≤ 1-w) :
    movingPause F w v 1 = F (1-w) := by
  unfold movingPause
  rw [if_neg (by linarith)]
  by_cases h : 1 ≤ v+w
  · rw [if_pos h, show v = 1-w by linarith]
  · rw [if_neg h]

def pausedPath (F : ℝ → Z) (hF : Continuous F) (w v : ℝ)
    (hw : 0 < w) (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1-w) : Path (F 0) (F (1-w)) where
  toFun u := movingPause F w v (u : ℝ)
  continuous_toFun := (movingPause_continuous F hF w hw.le).comp
    ((continuous_const (y := v)).prodMk continuous_subtype_val)
  source' := movingPause_zero F w v hv₀
  target' := movingPause_one F w v hw hv₁

/-- An actual endpoint-fixed homotopy moving the spare slot through the
path; its initial and final pause positions agree literally. -/
def pauseTransportHomotopy (F : ℝ → Z) (hF : Continuous F) (w v₀ v₁ : ℝ)
    (hw : 0 < w) (hv₀₀ : 0 ≤ v₀) (hv₀₁ : v₀ ≤ 1-w)
    (hv₁₀ : 0 ≤ v₁) (hv₁₁ : v₁ ≤ 1-w) :
    (pausedPath F hF w v₀ hw hv₀₀ hv₀₁).Homotopy (pausedPath F hF w v₁ hw hv₁₀ hv₁₁) where
  toFun z := pauseTransport F w v₀ v₁ (z.1,(z.2 : ℝ))
  continuous_toFun := (pauseTransport_continuous F hF w hw.le v₀ v₁).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  map_zero_left u := pauseTransport_zero F w v₀ v₁ (u : ℝ)
  map_one_left u := pauseTransport_one F w v₀ v₁ (u : ℝ)
  prop' r u hu := by
    have hr₀ := r.property.1
    have hr₁ := r.property.2
    have hvlow : 0 ≤ (1-(r : ℝ))*v₀+(r : ℝ)*v₁ := by nlinarith
    have hvhigh : (1-(r : ℝ))*v₀+(r : ℝ)*v₁ ≤ 1-w := by nlinarith
    rcases hu with hu | hu
    · subst u
      change movingPause F w _ 0 = (pausedPath F hF w v₀ hw hv₀₀ hv₀₁) 0
      rw [movingPause_zero F w _ hvlow]
      exact (pausedPath F hF w v₀ hw hv₀₀ hv₀₁).source.symm
    · have hu' : u = 1 := Set.mem_singleton_iff.mp hu
      subst u
      change movingPause F w _ 1 = (pausedPath F hF w v₀ hw hv₀₀ hv₀₁) 1
      rw [movingPause_one F w _ hw hvhigh]
      exact (pausedPath F hF w v₀ hw hv₀₀ hv₀₁).target.symm

theorem pauseTransportHomotopy_path_time_lipschitz (F : ℝ → Z) (hF : Continuous F)
    {K : ℝ≥0} (hFL : LipschitzWith K F) (w v₀ v₁ : ℝ)
    (hw : 0 < w) (hv₀₀ : 0 ≤ v₀) (hv₀₁ : v₀ ≤ 1-w)
    (hv₁₀ : 0 ≤ v₁) (hv₁₁ : v₁ ≤ 1-w) (r : unitInterval) :
    LipschitzWith K ((pauseTransportHomotopy F hF w v₀ v₁ hw hv₀₀ hv₀₁ hv₁₀ hv₁₁).eval r) := by
  have hc : LipschitzWith 1 (fun u : unitInterval => (u : ℝ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simp only [NNReal.coe_one, one_mul]
    rfl
  simpa using (pauseTransport_path_time_lipschitz F hFL w hw.le v₀ v₁ r).comp hc

end

end AbelianTargets.FixedSlots
