import AbelianTargets.ControlledCone
import Mathlib.Analysis.Normed.Group.Constructions

/-!
# Physical coordinate estimates for the rectangular cone

This transports the checked radial extension to a literal rectangle.
The first physical coordinate is normalized independently of the
transverse coordinates. The resulting bounds are divided by the
corresponding side lengths, as in Lemma 5.2.
-/

namespace AbelianTargets

open scoped unitInterval NNReal

noncomputable section

variable {d : ℕ}

abbrev RectanglePoint (o ℓ : Fin d → ℝ) :=
  {z : Fin d → ℝ // ∀ i, |z i-o i| ≤ ℓ i/2}

def normalizeRectangle (o ℓ : Fin d → ℝ) (hℓ : ∀ i,0 < ℓ i)
    (z : RectanglePoint o ℓ) : ConeBall (Fin d → ℝ) :=
  ⟨fun i => 2*(z.val i-o i)/ℓ i, by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    rw [Real.norm_eq_abs,abs_div,abs_mul,abs_of_pos (hℓ i)]
    norm_num
    apply (div_le_iff₀ (hℓ i)).mpr
    have := z.property i
    linarith⟩

theorem continuous_normalizeRectangle (o ℓ : Fin d → ℝ) (hℓ : ∀ i,0 < ℓ i) :
    Continuous (normalizeRectangle o ℓ hℓ) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact (continuous_const.mul ((continuous_apply i).comp continuous_subtype_val |>.sub continuous_const)).div_const _

theorem normalizeRectangle_coordinate_dist_le (o ℓ : Fin d → ℝ) (hℓ : ∀ i,0 < ℓ i)
    (z z' : RectanglePoint o ℓ) (i : Fin d) (heq : ∀ j,j ≠ i → z.val j=z'.val j) :
    dist (normalizeRectangle o ℓ hℓ z) (normalizeRectangle o ℓ hℓ z') ≤
      (2/ℓ i)*|z.val i-z'.val i| := by
  have hi := hℓ i
  rw [Subtype.dist_eq]
  apply (dist_pi_le_iff (by positivity)).mpr
  intro j
  by_cases hji : j=i
  · subst j
    change |2*(z.val i-o i)/ℓ i-2*(z'.val i-o i)/ℓ i| ≤ _
    have hsub : 2*(z.val i-o i)/ℓ i-2*(z'.val i-o i)/ℓ i =
        (2/ℓ i)*(z.val i-z'.val i) := by ring
    rw [hsub,abs_mul,abs_of_pos (by positivity : 0 < 2/ℓ i)]
  · change dist (2*(z.val j-o j)/ℓ j) (2*(z'.val j-o j)/ℓ j) ≤ _
    rw [heq j hji,dist_self]
    positivity

def physicalFirstParameter (A δ : ℝ) (r : ℝ) : I := clampInterval ((r-A)/δ)

theorem physicalFirstParameter_lipschitz (A δ : ℝ) (hδ : 0 < δ) :
    LipschitzWith ⟨δ⁻¹,le_of_lt (inv_pos.mpr hδ)⟩ (physicalFirstParameter A δ) := by
  have hh := lipschitz_affine_le ⟨δ⁻¹,le_of_lt (inv_pos.mpr hδ)⟩ δ⁻¹ (-A/δ)
    (by change |δ⁻¹| ≤ δ⁻¹; rw [abs_of_pos (inv_pos.mpr hδ)])
  have hc := lipschitz_clampInterval.comp hh
  have heq : (fun r : ℝ => clampInterval (δ⁻¹*r+(-A/δ))) = physicalFirstParameter A δ := by
    funext r
    unfold physicalFirstParameter
    congr 1
    ring
  simpa only [Function.comp_def,mul_one,one_mul,heq] using hc

@[simp] theorem physicalFirstParameter_left (A δ : ℝ) : physicalFirstParameter A δ A = 0 := by
  simp [physicalFirstParameter]

theorem physicalFirstParameter_right (A δ : ℝ) (hδ : 0 < δ) :
    physicalFirstParameter A δ (A+δ) = 1 := by
  simp [physicalFirstParameter,ne_of_gt hδ]

namespace ControlledContraction

variable {Z : Type*} [MetricSpace Z] {p q : Z} {D J S B : ℝ≥0}
variable (H : ControlledContraction p D J)

def rectangularValue (F : BoundaryPathFamily (E := Fin d → ℝ) p q S B)
    (o ℓ : Fin d → ℝ) (hℓ : ∀ i,0 < ℓ i) (A δ : ℝ)
    (r : ℝ) (z : RectanglePoint o ℓ) : Z :=
  H.coneValue F (normalizeRectangle o ℓ hℓ z) (physicalFirstParameter A δ r)

/-- The first-coordinate estimate has no joint-contraction factor. -/
theorem rectangularValue_first_dist_le (F : BoundaryPathFamily (E := Fin d → ℝ) p q S B)
    (o ℓ : Fin d → ℝ) (hℓ : ∀ i,0 < ℓ i) (A δ : ℝ) (hδ : 0 < δ)
    (r r' : ℝ) (z : RectanglePoint o ℓ) :
    dist (H.rectangularValue F o ℓ hℓ A δ r z) (H.rectangularValue F o ℓ hℓ A δ r' z) ≤
      (3*(max S D : ℝ≥0) : ℝ)/δ*|r-r'| := by
  have hp := (H.coneValue_path_lipschitz F (normalizeRectangle o ℓ hℓ z)).dist_le_mul
    (physicalFirstParameter A δ r) (physicalFirstParameter A δ r')
  have ht := (physicalFirstParameter_lipschitz A δ hδ).dist_le_mul r r'
  calc
    _ ≤ (3*max S D : ℝ≥0)*dist (physicalFirstParameter A δ r) (physicalFirstParameter A δ r') := hp
    _ ≤ (3*max S D : ℝ≥0)*(δ⁻¹*dist r r') :=
      mul_le_mul_of_nonneg_left ht (3*max S D).property
    _ = _ := by rw [Real.dist_eq]; simp only [NNReal.coe_mul,NNReal.coe_ofNat]; ring

theorem rectangularValue_transverse_dist_le (F : BoundaryPathFamily (E := Fin d → ℝ) p q S B)
    (o ℓ : Fin d → ℝ) (hℓ : ∀ i,0 < ℓ i) (A δ r : ℝ)
    (z z' : RectanglePoint o ℓ) (i : Fin d) (heq : ∀ j,j ≠ i → z.val j=z'.val j) :
    dist (H.rectangularValue F o ℓ hℓ A δ r z) (H.rectangularValue F o ℓ hℓ A δ r z') ≤
      2*(coneTransverseConstant S D J B : ℝ)/ℓ i*|z.val i-z'.val i| := by
  have hR := (H.coneValue_transverse_lipschitz F (physicalFirstParameter A δ r)).dist_le_mul
    (normalizeRectangle o ℓ hℓ z) (normalizeRectangle o ℓ hℓ z')
  have hπ := normalizeRectangle_coordinate_dist_le o ℓ hℓ z z' i heq
  calc
    _ ≤ (coneTransverseConstant S D J B : ℝ)*dist
      (normalizeRectangle o ℓ hℓ z) (normalizeRectangle o ℓ hℓ z') := hR
    _ ≤ (coneTransverseConstant S D J B : ℝ)*((2/ℓ i)*|z.val i-z'.val i|) :=
      mul_le_mul_of_nonneg_left hπ (coneTransverseConstant S D J B).property
    _ = _ := by ring

theorem continuous_rectangularValue (F : BoundaryPathFamily (E := Fin d → ℝ) p q S B)
    (o ℓ : Fin d → ℝ) (hℓ : ∀ i,0 < ℓ i) (A δ : ℝ) (hδ : 0 < δ) :
    Continuous (fun z : ℝ × RectanglePoint o ℓ => H.rectangularValue F o ℓ hℓ A δ z.1 z.2) := by
  exact (H.continuous_coneValue F).comp
    (((continuous_normalizeRectangle o ℓ hℓ).comp continuous_snd).prodMk
      ((physicalFirstParameter_lipschitz A δ hδ).continuous.comp continuous_fst))

@[simp] theorem rectangularValue_left (F : BoundaryPathFamily (E := Fin d → ℝ) p q S B)
    (o ℓ : Fin d → ℝ) (hℓ : ∀ i,0 < ℓ i) (A δ : ℝ) (z : RectanglePoint o ℓ) :
    H.rectangularValue F o ℓ hℓ A δ A z = p := by
  simp [rectangularValue]

theorem rectangularValue_right (F : BoundaryPathFamily (E := Fin d → ℝ) p q S B)
    (o ℓ : Fin d → ℝ) (hℓ : ∀ i,0 < ℓ i) (A δ : ℝ) (hδ : 0 < δ) (z : RectanglePoint o ℓ) :
    H.rectangularValue F o ℓ hℓ A δ (A+δ) z = q := by
  simp [rectangularValue,physicalFirstParameter_right A δ hδ]

end ControlledContraction
end
end AbelianTargets
