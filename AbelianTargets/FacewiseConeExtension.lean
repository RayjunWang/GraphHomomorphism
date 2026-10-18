import AbelianTargets.CubeBoundaryGluing
import AbelianTargets.RectangularCone

/-!
# Controlled cone filling from facewise boundary estimates

This supplies the ambient boundary estimate needed by the existing cone
formula from estimates on individual cube faces. A bounded image also
handles the two components of a one-dimensional cube boundary.
-/

namespace AbelianTargets.ControlledContraction

open scoped NNReal unitInterval

noncomputable section

variable {d : ℕ} {Z : Type*} [MetricSpace Z] {p q : Z} {S B C D J : ℝ≥0}

def BoundaryPathFamily.ofFacewise (path : ConeSphere (Fin d → ℝ) → Path p q)
    (hpath : ∀ x, LipschitzWith S (path x))
    (hdiam : ∀ x y u, dist (path x u) (path y u) ≤ C)
    (hface : ∀ i x y, |x.1 i|=1 → x.1 i=y.1 i → ∀ u,
      dist (path x u) (path y u) ≤ B*dist x y) :
    BoundaryPathFamily (E := Fin d → ℝ) p q S (2*B+C) where
  path := path
  path_lipschitz := hpath
  transverse := lipschitz_cubeBoundary_of_faces (fun x => (path x).toContinuousMap) B C
    (fun x y => (ContinuousMap.dist_le C.2).mpr (fun u => hdiam x y u))
    (fun i x y hi he => (ContinuousMap.dist_le (mul_nonneg B.2 dist_nonneg)).mpr
      (fun u => hface i x y hi he u))

/-- The local filling preserves the supplied literal parametrization and the
common path-time estimate; the face-to-boundary gluing affects only the
transverse constant. -/
theorem exists_facewise_cone_filling (H : ControlledContraction p D J)
    (path : ConeSphere (Fin d → ℝ) → Path p q)
    (hpath : ∀ x, LipschitzWith S (path x))
    (hdiam : ∀ x y u, dist (path x u) (path y u) ≤ C)
    (hface : ∀ i x y, |x.1 i|=1 → x.1 i=y.1 i → ∀ u,
      dist (path x u) (path y u) ≤ B*dist x y) :
    ∃ fill : ConeBall (Fin d → ℝ) × I → Z,
      Continuous fill ∧
      (∀ x : ConeSphere (Fin d → ℝ), ∀ u,
        fill (⟨x.1,by rw [x.2]⟩,u)=path x u) ∧
      (∀ x, LipschitzWith (3*max S D) (fun u => fill (x,u))) ∧
      (∀ u, LipschitzWith (coneTransverseConstant S D J (2*B+C))
        (fun x => fill (x,u))) := by
  let F := BoundaryPathFamily.ofFacewise path hpath hdiam hface
  refine ⟨fun z => H.coneValue F z.1 z.2,H.continuous_coneValue F,?_,?_,?_⟩
  · intro x u
    exact H.coneValue_boundary F x u
  · intro x
    exact H.coneValue_path_lipschitz F x
  · intro u
    exact H.coneValue_transverse_lipschitz F u

end

end AbelianTargets.ControlledContraction
