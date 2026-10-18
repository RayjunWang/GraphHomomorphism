import AbelianTargets.RelativeContractionNaturality
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-! The relative cone formula respects linear isometries of the transverse
coordinate space. In particular, a relabeling of active rectangular axes
does not change the filling. -/

namespace AbelianTargets
open scoped unitInterval NNReal
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def coneBallMap (k : E ≃ₗᵢ[ℝ] F) (x : ConeBall E) : ConeBall F :=
  ⟨k x.val,by simpa using x.property⟩

def coneSphereMap (k : E ≃ₗᵢ[ℝ] F) (x : ConeSphere E) : ConeSphere F :=
  ⟨k x.val,by simpa using x.property⟩

theorem radialDirection_linearIsometry (k : E ≃ₗᵢ[ℝ] F) (x : E) (hx : 0<‖x‖) :
    radialDirection (k x) (by simpa using hx)=coneSphereMap k (radialDirection x hx) := by
  apply Subtype.ext
  simp [radialDirection,coneSphereMap]

@[simp] theorem coneParameter_linearIsometry (k : E ≃ₗᵢ[ℝ] F) (x : ConeBall E) :
    coneParameter (coneBallMap k x)=coneParameter x := by
  simp [coneParameter,coneBallMap]

namespace ControlledContraction
variable {Z : Type*} [MetricSpace Z] {p q : Z} {D J S B : ℝ≥0}
variable (H : ControlledContraction p D J)

theorem coneValue_domain_natural (k : E ≃ₗᵢ[ℝ] F)
    (P : BoundaryPathFamily (E := E) p q S B)
    (Q : BoundaryPathFamily (E := F) p q S B)
    (hpaths : ∀ v,Q.path (coneSphereMap k v)=P.path v)
    (x : ConeBall E) (u : I) :
    H.coneValue Q (coneBallMap k x) u=H.coneValue P x u := by
  unfold coneValue
  simp only [coneBallMap,LinearIsometryEquiv.norm_map]
  split_ifs with hx
  · have hv := radialDirection_linearIsometry k x.val (by linarith : 0<‖x.val‖)
    have hp : Q.path (radialDirection (k x.val) (by simpa using
        (show 0<‖x.val‖ by linarith)))=P.path (radialDirection x.val (by linarith)) :=
      (congrArg Q.path hv).trans (hpaths _)
    simpa only [coneParameter,LinearIsometryEquiv.norm_map] using
      congrArg (fun R : Path p q => H.relativeHomotopy R (coneParameter x,u)) hp
  · rfl

theorem coneValue_transport_domain_natural
    {W : Type*} [MetricSpace W] (e : Z ≃ᵢ W) (k : E ≃ₗᵢ[ℝ] F)
    (P : BoundaryPathFamily (E := E) p q S B)
    (Q : BoundaryPathFamily (E := F) (e p) (e q) S B)
    (hpaths : ∀ v,Q.path (coneSphereMap k v)=(P.path v).map e.continuous)
    (x : ConeBall E) (u : I) :
    (H.transport e).coneValue Q (coneBallMap k x) u=e (H.coneValue P x u) := by
  have hh := (H.transport e).coneValue_domain_natural k (P.transport e) Q hpaths x u
  exact hh.trans (H.transport_coneValue e P x u)

end ControlledContraction
end
end AbelianTargets
