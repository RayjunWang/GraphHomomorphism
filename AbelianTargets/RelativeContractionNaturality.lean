import AbelianTargets.CarrierTranslationEquiv
import AbelianTargets.ControlledCone

/-! The literal relative homotopy and cone filling commute with isometric
transport. These equalities concern the actual formulas, including all
four path deformation stages and the radial extension. -/

namespace AbelianTargets.ControlledContraction
open scoped unitInterval NNReal
noncomputable section
variable {Z W : Type*} [MetricSpace Z] [MetricSpace W]
variable {p q : Z} {D J S B : ℝ≥0}
variable (H : ControlledContraction p D J) (e : Z ≃ᵢ W)

@[simp] theorem transport_map (z : Z) (t : I) :
    (H.transport e).map (e z,t)=e (H.map (z,t)) := by
  simp [transport]

@[simp] theorem transport_shortPath (u : I) :
    (H.transport e).shortPath (e q) u=e (H.shortPath q u) := by
  simp [shortPath,transport]

theorem transport_compressRaw (P : Path p q) (z : I × ℝ) :
    compressRaw (P.map e.continuous) z=e (compressRaw P z) := rfl

theorem transport_spurRaw (P : Path p q) (z : I × ℝ) :
    (H.transport e).spurRaw (P.map e.continuous) z=e (H.spurRaw P z) := by
  unfold spurRaw slot3
  split_ifs <;> simp [transport]

theorem transport_thirdRaw (P : Path p q) (z : I × ℝ) :
    (H.transport e).thirdRaw (P.map e.continuous) z=e (H.thirdRaw P z) := by
  unfold thirdRaw slot3
  split_ifs <;> simp [transport]

theorem transport_expandRaw (z : I × ℝ) :
    (H.transport e).expandRaw (e q) z=e (H.expandRaw q z) := by
  simp [expandRaw]

theorem transport_relativeHomotopy (P : Path p q) (z : I × I) :
    (H.transport e).relativeHomotopy (P.map e.continuous) z=
      e (H.relativeHomotopy P z) := by
  simp only [relativeHomotopy,Path.Homotopy.trans_apply]
  split_ifs <;>
    simp only [compressionHomotopy,spurHomotopy,thirdHomotopy,expansionHomotopy,
      transport_compressRaw,transport_spurRaw,transport_thirdRaw,transport_expandRaw] <;> rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def BoundaryPathFamily.transport (F : BoundaryPathFamily (E := E) p q S B)
    (e : Z ≃ᵢ W) : BoundaryPathFamily (E := E) (e p) (e q) S B where
  path v := (F.path v).map e.continuous
  path_lipschitz v := by
    simpa only [Path.map_coe,Function.comp_def,one_mul] using
      e.isometry.lipschitz.comp (F.path_lipschitz v)
  transverse := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    apply (ContinuousMap.dist_le (mul_nonneg B.property dist_nonneg)).mpr
    intro r
    change dist (e (F.path v r)) (e (F.path w r)) ≤ _
    rw [e.isometry.dist_eq]
    exact (ContinuousMap.dist_apply_le_dist r).trans (F.transverse.dist_le_mul v w)

theorem transport_coneValue (F : BoundaryPathFamily (E := E) p q S B)
    (x : ConeBall E) (u : I) :
    (H.transport e).coneValue (F.transport e) x u=e (H.coneValue F x u) := by
  unfold coneValue
  split_ifs
  · exact H.transport_relativeHomotopy e _ _
  · exact H.transport_shortPath e u

end
end AbelianTargets.ControlledContraction
