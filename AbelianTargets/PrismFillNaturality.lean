import AbelianTargets.IntegerPrismFillTranslation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace AbelianTargets
noncomputable section
open scoped NNReal unitInterval

namespace ControlledContraction
variable {E F Z W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MetricSpace Z] [MetricSpace W]
variable {p q : Z} {D J S B S' B' : ℝ≥0}

theorem coneValue_transport_domain_natural_any_bounds (H : ControlledContraction p D J)
    (e : Z≃ᵢW) (k : E≃ₗᵢ[ℝ]F)
    (P : BoundaryPathFamily (E := E) p q S B)
    (Q : BoundaryPathFamily (E := F) (e p) (e q) S' B')
    (hpaths : ∀v,Q.path (coneSphereMap k v)=(P.path v).map e.continuous)
    (x : ConeBall E) (u : I) :
    (H.transport e).coneValue Q (coneBallMap k x) u=e (H.coneValue P x u) := by
  have hh : (H.transport e).coneValue Q (coneBallMap k x) u=
      (H.transport e).coneValue (P.transport e) x u := by
    have hnorm : ‖(coneBallMap k x).val‖=‖x.val‖ := k.norm_map x.val
    by_cases hx : (1/2 : ℝ)≤‖x.val‖
    · have hx' : (1/2 : ℝ)≤‖(coneBallMap k x).val‖ := by rw [hnorm];exact hx
      rw [coneValue,dif_pos hx',coneValue,dif_pos hx]
      have hdir : radialDirection (coneBallMap k x).val (by linarith)=
          coneSphereMap k (radialDirection x.val (by linarith)) := by
        change radialDirection (k x.val) _=coneSphereMap k (radialDirection x.val _)
        exact radialDirection_linearIsometry k x.val (by linarith)
      rw [hdir,hpaths,coneParameter_linearIsometry]
      rfl
    · have hx' : ¬(1/2 : ℝ)≤‖(coneBallMap k x).val‖ := by rw [hnorm];exact hx
      rw [coneValue,dif_neg hx',coneValue,dif_neg hx]
  exact hh.trans (H.transport_coneValue e P x u)

theorem ext_map {p : Z} (H G : ControlledContraction p D J) (h : H.map=G.map) : H=G := by
  cases H
  cases G
  cases h
  rfl

end ControlledContraction

namespace PrismBoundaryData
variable {d : ℕ} {Z W : Type*} [MetricSpace Z] [MetricSpace W]
variable {R : RectangularCell d} {i : Fin d} {p q : Z} {p' q' : W}
variable {D J S B S' B' : ℝ≥0}

theorem fill_translate_of_maps (F : PrismBoundaryData R i p q S B)
    (H : ControlledContraction p D J) (a : Fin d→ℤ) (e : Z≃ᵢW)
    (G : PrismBoundaryData (R.translate a) i p' q' S' B')
    (H' : ControlledContraction p' D J) (hp : e p=p') (hq : e q=q')
    (hH : ∀v t,H'.map (e v,t)=e (H.map (v,t)))
    (hmap : ∀z : CellBoundaryDomain R,G.map (R.translateBoundaryPoint a z)=e (F.map z))
    (hi : R.lower i<R.upper i) (z : CellClosedDomain R) :
    G.fill H' (by simpa [RectangularCell.translate] using hi) (R.translateClosedPoint a z)=
      e (F.fill H hi z) := by
  subst p'
  subst q'
  have hHeq : H'=H.transport e := by
    apply ControlledContraction.ext_map
    funext v
    have hh := hH (e.symm v.1) v.2
    simpa only [e.apply_symm_apply,ControlledContraction.transport] using hh
  rw [hHeq]
  let k := R.activeLinearTranslation a i
  have hsphere : ∀v : ConeSphere (R.ActiveTransverse i→ℝ),
      coneSphereMap k v=R.translateConeSphere a i v := fun _=>rfl
  have hball : ∀v : ConeBall (R.ActiveTransverse i→ℝ),
      coneBallMap k v=R.translateConeBall a i v := fun _=>rfl
  have hpaths : ∀v,G.pathFamily.path (coneSphereMap k v)=(F.pathFamily.path v).map e.continuous := by
    intro v
    apply Path.ext
    funext r
    change G.map (prismBoundaryPoint (R.translate a) i (coneSphereMap k v) r)=
      e (F.map (prismBoundaryPoint R i v r))
    rw [hsphere,prismBoundaryPoint_translate]
    exact hmap _
  unfold fill
  rw [R.normalizeTransverse_translate,R.firstIntervalParameter_translate,←hball]
  exact H.coneValue_transport_domain_natural_any_bounds e k F.pathFamily G.pathFamily hpaths _ _

end PrismBoundaryData
end
end AbelianTargets
