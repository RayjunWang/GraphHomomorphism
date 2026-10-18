import AbelianTargets.IntegerPrismTranslation
import AbelianTargets.IntegerPrismFilling
import AbelianTargets.ConeDomainNaturality

namespace AbelianTargets
noncomputable section
open scoped NNReal unitInterval
variable {d : ℕ}

theorem prismBoundaryPoint_translate (R : RectangularCell d) (a : Fin d→ℤ) (i : Fin d)
    (v : ConeSphere (R.ActiveTransverse i→ℝ)) (r : I) :
    prismBoundaryPoint (R.translate a) i (R.translateConeSphere a i v) r=
      R.translateBoundaryPoint a (prismBoundaryPoint R i v r) := by
  apply Subtype.ext
  exact R.prismCoordinates_translate a i r ⟨v.val,v.property.le⟩

namespace PrismBoundaryData
variable {Z W : Type*} [MetricSpace Z] [MetricSpace W]
variable {R : RectangularCell d} {i : Fin d} {p q : Z} {D J S B : ℝ≥0}

theorem fill_translate (F : PrismBoundaryData R i p q S B)
    (H : ControlledContraction p D J) (a : Fin d→ℤ) (e : Z ≃ᵢ W)
    (G : PrismBoundaryData (R.translate a) i (e p) (e q) S B)
    (hmap : ∀ z : CellBoundaryDomain R,G.map (R.translateBoundaryPoint a z)=e (F.map z))
    (hi : R.lower i<R.upper i) (z : CellClosedDomain R) :
    G.fill (H.transport e) (by simpa [RectangularCell.translate] using hi) (R.translateClosedPoint a z)=
      e (F.fill H hi z) := by
  let k := R.activeLinearTranslation a i
  have hsphere : ∀ v : ConeSphere (R.ActiveTransverse i→ℝ),
      coneSphereMap k v=R.translateConeSphere a i v := fun v=>rfl
  have hball : ∀ v : ConeBall (R.ActiveTransverse i→ℝ),
      coneBallMap k v=R.translateConeBall a i v := fun v=>rfl
  have hpaths : ∀ v,G.pathFamily.path (coneSphereMap k v)=
      (F.pathFamily.path v).map e.continuous := by
    intro v
    apply Path.ext
    funext r
    change G.map (prismBoundaryPoint (R.translate a) i (coneSphereMap k v) r)=
      e (F.map (prismBoundaryPoint R i v r))
    rw [hsphere,prismBoundaryPoint_translate]
    exact hmap _
  unfold fill
  rw [R.normalizeTransverse_translate,R.firstIntervalParameter_translate]
  rw [←hball]
  exact H.coneValue_transport_domain_natural e k F.pathFamily G.pathFamily hpaths _ _

/-- The computed filling depends on the literal boundary values only.
Different certificates or numerical upper bounds do not affect the map. -/
theorem fill_ext {S' B' : ℝ≥0} (F : PrismBoundaryData R i p q S B)
    (G : PrismBoundaryData R i p q S' B') (H : ControlledContraction p D J)
    (hmap : ∀ z,F.map z=G.map z) (hi : R.lower i<R.upper i) (z : CellClosedDomain R) :
    F.fill H hi z=G.fill H hi z := by
  unfold fill ControlledContraction.coneValue
  split_ifs with hx
  · have hpath : F.pathFamily.path (radialDirection (R.normalizeTransverse i z).val (by linarith))=
        G.pathFamily.path (radialDirection (R.normalizeTransverse i z).val (by linarith)) := by
      apply Path.ext
      funext r
      exact hmap _
    rw [hpath]
  · rfl

end PrismBoundaryData
end
end AbelianTargets
