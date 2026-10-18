import AbelianTargets.CarrierTranslationGeometry
import AbelianTargets.RelativePathContraction

set_option backward.isDefEq.respectTransparency false

namespace AbelianTargets.IntervalCarriers
noncomputable section
attribute [local instance] Classical.propDecidable

def inverseVertexTranslation {K : ℕ} {A B : ℤ} (a : ℤ)
    (v : CarrierVertex K (A+a) (B+a)) : CarrierVertex K A B :=
  ⟨translate (-a) v.1,by
    have h := (translate_mem_carrierVertices (-a) v.1).mpr v.2
    simpa using h⟩

def inverseRealizationTranslation {m K : ℕ} {A B : ℤ} (a : ℤ)
    (p : Realization m K (A+a) (B+a)) : Realization m K A B := by
  refine ⟨Probability.push (inverseVertexTranslation a) p.1,?_⟩
  obtain ⟨s,hs,hp⟩ := p.2
  refine ⟨s.image (inverseVertexTranslation a),?_,?_⟩
  · apply (mem_simplexFaces _).mpr
    rw [Finset.image_image]
    have h := ((mem_simplexFaces s).mp hs).translated (-a)
    simpa only [add_neg_cancel_right,Finset.image_image,Function.comp_def] using h
  · intro w hw
    obtain ⟨v,hv,hvp⟩ := (Probability.push_pos_iff (inverseVertexTranslation a) p.1 w).mp hw
    exact Finset.mem_image.mpr ⟨v,hp v hvp,hv⟩

def realizationTranslationEquiv {m K : ℕ} {A B : ℤ} (a : ℤ) :
    Realization m K A B ≃ᵢ Realization m K (A+a) (B+a) where
  toFun := realizationTranslation a
  invFun := inverseRealizationTranslation a
  left_inv p := by
    apply Subtype.ext
    change Probability.push (inverseVertexTranslation a) (Probability.push (vertexTranslation a) p.1)=p.1
    rw [Probability.push_comp]
    apply Probability.push_eq_self
    intro v hv
    apply Subtype.ext
    simp [vertexTranslation,inverseVertexTranslation,translate]
  right_inv p := by
    apply Subtype.ext
    change Probability.push (vertexTranslation a) (Probability.push (inverseVertexTranslation a) p.1)=p.1
    rw [Probability.push_comp]
    apply Probability.push_eq_self
    intro v hv
    apply Subtype.ext
    simp [vertexTranslation,inverseVertexTranslation,translate]
  isometry_toFun := realizationTranslation_isometry a

end
end AbelianTargets.IntervalCarriers

namespace AbelianTargets.ControlledContraction
open scoped NNReal unitInterval
noncomputable section

def transport {Z W : Type*} [MetricSpace Z] [MetricSpace W] {p : Z} {D J : ℝ≥0}
    (H : ControlledContraction p D J) (e : Z ≃ᵢ W) : ControlledContraction (e p) D J where
  map z := e (H.map (e.symm z.1,z.2))
  continuous := e.continuous.comp (H.continuous.comp ((e.symm.continuous.comp continuous_fst).prodMk continuous_snd))
  at_zero z := by rw [H.at_zero,e.apply_symm_apply]
  at_one z := by rw [H.at_one]
  fixes t := by rw [e.symm_apply_apply,H.fixes]
  track z := by simpa only [Function.comp_def,one_mul] using e.isometry.lipschitz.comp (H.track (e.symm z))
  joint := by
    have hp : LipschitzWith 1 (fun z : W × I => (e.symm z.1,z.2)) := by
      simpa only [Function.comp_def,one_mul,max_self] using
        (e.symm.isometry.lipschitz.comp LipschitzWith.prod_fst).prodMk
          (LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : W × I → I))
    simpa only [Function.comp_def,mul_one,one_mul] using e.isometry.lipschitz.comp (H.joint.comp hp)

end
end AbelianTargets.ControlledContraction
